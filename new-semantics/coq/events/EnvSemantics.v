From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.

Variant read_env_res {var loc lang} :=
  | Env_err
  | Env_loc (ℓ : loc)
  | Env_wvl (w : wvl var loc lang)
.

Fixpoint read_env {var loc lang} `{Eq var} (σ : nv var loc lang) (x : var) :=
  match σ with
  | nv_mt | nv_bloc _ _ _ => Env_err
  | nv_ev E => Env_wvl (wvl_v (vl_ev (Read E x)))
  | nv_floc x' ℓ σ' =>
    if eqb x x' then Env_loc ℓ else read_env σ' x
  | nv_bval x' w σ' =>
    if eqb x x' then Env_wvl w else read_env σ' x
  end.

Inductive eval {var loc} `{Eq var} `{Eq loc} (σ : nv var loc (@val var)): tm -> (vl var loc val) -> Prop :=
| ev_id x v (READ : read_env σ x = Env_wvl (wvl_v v))
: eval σ (tm_var x) v
| ev_rec x v (READ : read_env σ x = Env_wvl (wvl_recv v))
: eval σ (tm_var x) (open_wvl_vl 0 (wvl_recv v) v)
| ev_fn x t
: eval σ (tm_lam x t) (vl_clos (v_fn x t) σ)
| ev_app t1 t2 x e σ1 v2 v
  (FN : eval σ t1 (vl_clos (v_fn x e) σ1))
  (ARG : eval σ t2 v2)
  (BODY : eval (nv_bval x (wvl_v v2) σ1) e v)
: eval σ (tm_app t1 t2) v
| ev_appevent t1 t2 E1 v2
  (FN : eval σ t1 (vl_ev E1))
  (ARG : eval σ t2 v2)
: eval σ (tm_app t1 t2) (vl_ev (Call E1 v2))
| ev_link t1 t2 σ1 v
  (MOD : eval σ t1 (vl_exp σ1))
  (IMP : eval σ1 t2 v)
: eval σ (tm_link t1 t2) v
| ev_linkevent t1 t2 E1 v
  (MOD : eval σ t1 (vl_ev E1))
  (IMP : eval (nv_ev E1) t2 v)
: eval σ (tm_link t1 t2) v
| ev_mt
: eval σ tm_mt (vl_exp nv_mt)
| ev_bind x t1 t2 ℓ v1 σ2
  (FRESH : ~ In ℓ (floc_nv σ))
  (BIND : eval (nv_floc x ℓ σ) t1 v1)
  (MOD : eval (nv_bval x (wvl_recv (close_vl 0 ℓ v1)) σ) t2 (vl_exp σ2))
: eval σ (tm_bind x t1 t2) (vl_exp (nv_bval x (wvl_recv (close_vl 0 ℓ v1)) σ2))
| ev_bindevent x t1 t2 ℓ v1 E2
  (FRESH : ~ In ℓ (floc_nv σ))
  (BIND : eval (nv_floc x ℓ σ) t1 v1)
  (MOD : eval (nv_bval x (wvl_recv (close_vl 0 ℓ v1)) σ) t2 (vl_ev E2))
: eval σ (tm_bind x t1 t2) (vl_exp (nv_bval x (wvl_recv (close_vl 0 ℓ v1)) (nv_ev E2)))
.

Lemma read_env_lc {var loc lang} `{Eq var} (σ : nv var loc lang) (Σ : env σ) :
  forall x w (READ : read_env σ x = Env_wvl w), wvalue w.
Proof.
  induction σ; ii; ss;
  des_ifs; inv Σ; repeat econstructor; auto;
  eqb2eq var; clarify; eauto.
Qed.

Lemma eval_lc {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall (LC : env σ), value v.
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_lc in READ; eauto. inv READ. auto.
  - eapply read_env_lc in READ; eauto.
    inversion READ; clarify.
    gensym_tac (L ++ floc_vl v) ν.
    assert (subst_intro_vl _ _ _ v) by eapply subst_intro.
    rw; eauto.
    eapply subst_wvl_lc; eauto.
  - econstructor. auto.
  - apply IHEVAL3. econstructor.
    econstructor. apply IHEVAL2. auto.
    exploit IHEVAL1; eauto. intros LC'.
    inv LC'. auto.
  - specialize (IHEVAL1 LC). specialize (IHEVAL2 LC).
    inv IHEVAL1. repeat econstructor; eauto.
  - apply IHEVAL2. exploit IHEVAL1; eauto.
    intros LC'. inv LC'. auto.
  - apply IHEVAL2. exploit IHEVAL1; eauto.
    intros LC'. inv LC'. econstructor; eauto.
  - repeat constructor.
  - assert (wvalue (wvl_recv (close_vl 0 ℓ v1))).
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl _ _ _ v1) by eapply close_open_loc_eq; rw.
    exploit IHEVAL1; eauto. constructor; auto. intros VAL1.
    assert (open_loc_lc_vl _ _ _ v1 VAL1) by (eapply open_loc_lc; auto).
    rw.
    eapply subst_loc_lc. auto.
    repeat constructor; eauto.
    exploit IHEVAL2.
    constructor; auto.
    intros VAL. inv VAL. auto.
  - assert (wvalue (wvl_recv (close_vl 0 ℓ v1))).
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl _ _ _ v1) by eapply close_open_loc_eq; rw.
    exploit IHEVAL1; eauto. constructor; auto. intros VAL1.
    assert (open_loc_lc_vl _ _ _ v1 VAL1) by (eapply open_loc_lc; auto).
    rw.
    eapply subst_loc_lc. auto.
    repeat constructor; eauto.
    exploit IHEVAL2.
    constructor; auto.
    intros VAL. inv VAL. auto.
Qed.

Lemma read_env_map {var loc lang} `{Eq var} `{Eq loc} (σ : nv var loc lang) :
  forall φ w x (READ : read_env σ x = Env_wvl w),
    read_env (map_nv φ σ) x = Env_wvl (map_wvl φ w).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  des_ifs; eqb2eq var; clarify;
  try eqb2eq loc; clarify; eauto.
Qed.

Lemma read_env_subst_loc {var loc lang} `{Eq var} `{Eq loc} (σ : nv var loc lang) x :
 forall r ν ℓ (READ : read_env σ x = r),
    read_env (subst_loc_nv ν ℓ σ) x =
    match r with
    | Env_err => Env_err
    | Env_loc ℓ' =>
      if eqb ℓ ℓ' then Env_loc ν else Env_loc ℓ'
    | Env_wvl u =>
      Env_wvl (subst_loc_wvl ν ℓ u)
    end.
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  des_ifs; exploit IHσ; eauto;
  ss; repeat rw; eauto.
Qed.

Lemma read_env_subst_wvl {var loc lang} `{Eq var} `{Eq loc} (σ : nv var loc lang) x :
  forall r w ℓ (READ : read_env σ x = r),
    read_env (subst_wvl_nv w ℓ σ) x =
    match r with
    | Env_err => Env_err
    | Env_loc ℓ' =>
      if eqb ℓ ℓ' then Env_wvl w else Env_loc ℓ'
    | Env_wvl u =>
      Env_wvl (subst_wvl_wvl w ℓ u)
    end.
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  des_ifs; exploit IHσ; eauto;
  ss; repeat rw; eauto.
Qed.


Lemma read_env_floc {var loc lang} `{Eq var} `{Eq loc} (σ : nv var loc lang) :
  forall w ℓ x (READ : read_env σ x = Env_wvl w) (IN : In ℓ (floc_wvl w)),
    In ℓ (floc_nv σ).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  eqb2eq var; clarify; eauto;
  rewrite in_app_iff; eauto.
Qed.

Lemma eval_floc_dec {var loc} `{Eq var} `{Eq loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall ℓ (IN : In ℓ (floc_vl v)), In ℓ (floc_nv σ).
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_floc; eauto.
  - eapply open_wvl_floc in IN.
    ss; des; eapply read_env_floc; eauto.
  - apply IHEVAL3 in IN.
    rewrite in_app_iff in IN; des; auto.
  - rewrite in_app_iff in IN; des; auto.
  - rewrite in_app_iff in *.
    des; eauto.
    eapply close_floc in IN. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
    exploit IHEVAL2; eauto. intros IN'.
    rewrite in_app_iff in *.
    des; eauto.
    eapply close_floc in IN'. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
  - rewrite in_app_iff in *.
    des; eauto.
    eapply close_floc in IN. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
    exploit IHEVAL2; eauto. intros IN'.
    rewrite in_app_iff in *.
    des; eauto.
    eapply close_floc in IN'. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
Qed.

Lemma eval_map {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall φ (INJ : oto φ),
    eval (map_nv φ σ) t (map_vl φ v).
Proof.
  induction EVAL; ii; ss; try solve [econstructor; eauto].
  - econstructor. exploit (read_env_map σ); eauto.
  - assert (map_open_wvl_vl _ _ _ v) by (eapply map_open_wvl).
    rw. eapply ev_rec.
    exploit (read_env_map σ); eauto.
  - assert (map_close_vl _ _ _ v1) by (eapply map_close).
    rw; eauto.
    econstructor; eauto.
    red. intros IN. eapply map_floc in IN; eauto.
    rrw; eauto.
  - assert (map_close_vl _ _ _ v1) by (eapply map_close).
    rw; eauto.
    eapply ev_bindevent; eauto.
    red. intros IN. eapply map_floc in IN; eauto.
    rrw; eauto.
Qed.

Lemma eval_map_subst_loc {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall φ (INJ : oto φ) ν ℓ',
    eval (subst_loc_nv ν ℓ' (map_nv φ σ)) t (subst_loc_vl ν ℓ' (map_vl φ v)).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - econstructor 1.
    eapply read_env_map with (φ := φ) in READ. ss.
    erewrite read_env_subst_loc; eauto.
    ss.
  - assert (map_open_wvl_vl _ _ _ v) by (eapply map_open_wvl; auto).
    rw. s.
    assert (open_wvl_subst_loc_vl _ _ _ (map_vl φ v)) by (eapply open_wvl_subst_loc; auto).
    rw; eauto.
    econstructor 2.
    eapply read_env_map with (φ := φ) in READ. ss.
    erewrite read_env_subst_loc; eauto.
    ss.
  - specialize (IHEVAL2 φ INJ ν ℓ').
    assert (map_close_vl _ _ _ v1) as RR by (eapply map_close; auto).
    rewrite RR in *; auto. clear RR.
    gensym_tac (ℓ' :: φ ℓ :: ν :: floc_nv (map_nv φ σ)) ℓ''.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    replace 
      (close_vl 0 (φ ℓ) (map_vl φ v1)) with
      (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1))) in *.
    replace 
      (subst_loc_vl ν ℓ' (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) with
      (close_vl 0 ℓ'' (subst_loc_vl ν ℓ' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) in *.
    constructor; auto.
    { intro IN. eapply floc_subst_loc in IN. des; auto. }
    { set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
      replace (map_nv φ σ) with (map_nv φ' σ).
      replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)) with (map_vl φ' v1).
      exploit (IHEVAL1 φ' _ ν).
      subst φ'. unfold compose, swap, id.
      ii; ss; des_ifs;
      repeat match goal with
      | _ => eqb2eq loc
      | H : φ _ = φ _ |- _ => apply INJ in H
      | _ => clean_set
      | _ => clarify
      end.
      instantiate (1 := ℓ').
      replace (eqb ℓ' (φ' ℓ)) with false.
      replace (φ' ℓ) with ℓ''. auto.
      1, 2: subst φ'; unfold compose, swap, id; s; des_ifs; eqb2eq loc; clarify.
      symmetry. apply eqb_neq. auto.
      { assert (swap_is_subst_vl _ _ _ (map_vl φ v1)) as RR by eapply swap_is_subst.
        specialize (RR id).
        exploit RR; eauto. unfold oto. auto.
        instantiate (1 := φ ℓ).
        replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
        unfold id at 2. unfold id at 2.
        intro. rrw.
        subst φ'. symmetry. eapply map_compose. }
      { eapply map_ext.
        ii. subst φ'. unfold compose, swap, id.
        des_ifs; eqb2eq loc; clarify.
        eapply floc_map in DOM; eauto.
        instantiate (1 := φ) in DOM.
        clean_set. contradict.
        exploit INJ; eauto. ii; clarify. } }
    { eapply subst_loc_close; auto. }
    { eapply subst_loc_close_eq; auto. }
  - specialize (IHEVAL2 φ INJ ν ℓ').
    assert (map_close_vl _ _ _ v1) as RR by (eapply map_close; auto).
    rewrite RR in *; auto. clear RR.
    gensym_tac (ℓ' :: φ ℓ :: ν :: floc_nv (map_nv φ σ)) ℓ''.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    replace 
      (close_vl 0 (φ ℓ) (map_vl φ v1)) with
      (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1))) in *.
    replace 
      (subst_loc_vl ν ℓ' (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) with
      (close_vl 0 ℓ'' (subst_loc_vl ν ℓ' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) in *.
    apply ev_bindevent; auto.
    { intro IN. eapply floc_subst_loc in IN. des; auto. }
    { set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
      replace (map_nv φ σ) with (map_nv φ' σ).
      replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)) with (map_vl φ' v1).
      exploit (IHEVAL1 φ' _ ν).
      subst φ'. unfold compose, swap, id.
      ii; ss; des_ifs;
      repeat match goal with
      | _ => eqb2eq loc
      | H : φ _ = φ _ |- _ => apply INJ in H
      | _ => clean_set
      | _ => clarify
      end.
      instantiate (1 := ℓ').
      replace (eqb ℓ' (φ' ℓ)) with false.
      replace (φ' ℓ) with ℓ''. auto.
      1, 2: subst φ'; unfold compose, swap, id; s; des_ifs; eqb2eq loc; clarify.
      symmetry. apply eqb_neq. auto.
      { assert (swap_is_subst_vl _ _ _ (map_vl φ v1)) as RR by eapply swap_is_subst.
        specialize (RR id).
        exploit RR; eauto. unfold oto. auto.
        instantiate (1 := φ ℓ).
        replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
        unfold id at 2. unfold id at 2.
        intro. rrw.
        subst φ'. symmetry. eapply map_compose. }
      { eapply map_ext.
        ii. subst φ'. unfold compose, swap, id.
        des_ifs; eqb2eq loc; clarify.
        eapply floc_map in DOM; eauto.
        instantiate (1 := φ) in DOM.
        clean_set. contradict.
        exploit INJ; eauto. ii; clarify. } }
    { eapply subst_loc_close; auto. }
    { eapply subst_loc_close_eq; auto. }
Qed.

Lemma eval_subst_loc {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall ν ℓ', eval (subst_loc_nv ν ℓ' σ) t (subst_loc_vl ν ℓ' v).
Proof.
  intros.
  replace σ with (map_nv id σ) by apply map_id_is_id.
  replace v with (map_vl id v) by apply map_id_is_id.
  eapply eval_map_subst_loc; try intro; auto.
Qed.

Lemma eval_map_subst_wvl {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall φ (INJ : oto φ)
    u (U : wvalue u) ℓ',
    eval (subst_wvl_nv u ℓ' (map_nv φ σ)) t (subst_wvl_vl u ℓ' (map_vl φ v)).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - econstructor 1.
    eapply read_env_map with (φ := φ) in READ.
    erewrite read_env_subst_wvl; eauto.
    ss.
  - assert (map_open_wvl_vl _ _ _ v) by (eapply map_open_wvl; auto).
    rw. s.
    assert (open_wvl_subst_wvl_vl _ _ _ (map_vl φ v)) by (eapply open_wvl_subst_wvl; auto).
    rw; eauto.
    econstructor 2.
    eapply read_env_map with (φ := φ) in READ.
    erewrite read_env_subst_wvl; eauto.
    ss.
  - specialize (IHEVAL2 φ INJ u U ℓ').
    assert (map_close_vl _ _ _ v1) as RR by (eapply map_close; auto).
    rewrite RR in *; auto. clear RR.
    gensym_tac (ℓ' :: φ ℓ :: floc_wvl u ++ floc_nv (map_nv φ σ)) ℓ''.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    replace 
      (close_vl 0 (φ ℓ) (map_vl φ v1)) with
      (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1))) in *.
    replace 
      (subst_wvl_vl u ℓ' (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) with
      (close_vl 0 ℓ'' (subst_wvl_vl u ℓ' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) in *.
    constructor; auto.
    { intro IN. eapply floc_subst_wvl in IN. des; auto. }
    { set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
      replace (map_nv φ σ) with (map_nv φ' σ).
      replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)) with (map_vl φ' v1).
      exploit (IHEVAL1 φ' _ u U).
      subst φ'. unfold compose, swap, id.
      ii; ss; des_ifs;
      repeat match goal with
      | _ => eqb2eq loc
      | H : φ _ = φ _ |- _ => apply INJ in H
      | _ => clean_set
      | _ => clarify
      end.
      instantiate (1 := ℓ').
      replace (eqb ℓ' (φ' ℓ)) with false.
      replace (φ' ℓ) with ℓ''. auto.
      1, 2: subst φ'; unfold compose, swap, id; s; des_ifs; eqb2eq loc; clarify.
      symmetry. apply eqb_neq. auto.
      { assert (swap_is_subst_vl _ _ _ (map_vl φ v1)) as RR by eapply swap_is_subst.
        specialize (RR id).
        exploit RR; eauto. unfold oto. auto.
        instantiate (1 := φ ℓ).
        replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
        unfold id at 2. unfold id at 2.
        intro. rrw.
        subst φ'. symmetry. eapply map_compose. }
      { eapply map_ext.
        ii. subst φ'. unfold compose, swap, id.
        des_ifs; eqb2eq loc; clarify.
        eapply floc_map in DOM; eauto.
        instantiate (1 := φ) in DOM.
        clean_set. contradict.
        exploit INJ; eauto. ii; clarify. } }
    { eapply subst_wvl_close; auto. }
    { eapply subst_loc_close_eq; auto. }
  - specialize (IHEVAL2 φ INJ u U ℓ').
    assert (map_close_vl _ _ _ v1) as RR by (eapply map_close; auto).
    rewrite RR in *; auto. clear RR.
    gensym_tac (ℓ' :: φ ℓ :: floc_wvl u ++ floc_nv (map_nv φ σ)) ℓ''.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    replace 
      (close_vl 0 (φ ℓ) (map_vl φ v1)) with
      (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1))) in *.
    replace 
      (subst_wvl_vl u ℓ' (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) with
      (close_vl 0 ℓ'' (subst_wvl_vl u ℓ' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)))) in *.
    apply ev_bindevent; auto.
    { intro IN. eapply floc_subst_wvl in IN. des; auto. }
    { set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
      replace (map_nv φ σ) with (map_nv φ' σ).
      replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)) with (map_vl φ' v1).
      exploit (IHEVAL1 φ' _ u U).
      subst φ'. unfold compose, swap, id.
      ii; ss; des_ifs;
      repeat match goal with
      | _ => eqb2eq loc
      | H : φ _ = φ _ |- _ => apply INJ in H
      | _ => clean_set
      | _ => clarify
      end.
      instantiate (1 := ℓ').
      replace (eqb ℓ' (φ' ℓ)) with false.
      replace (φ' ℓ) with ℓ''. auto.
      1, 2: subst φ'; unfold compose, swap, id; s; des_ifs; eqb2eq loc; clarify.
      symmetry. apply eqb_neq. auto.
      { assert (swap_is_subst_vl _ _ _ (map_vl φ v1)) as RR by eapply swap_is_subst.
        specialize (RR id).
        exploit RR; eauto. unfold oto. auto.
        instantiate (1 := φ ℓ).
        replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
        unfold id at 2. unfold id at 2.
        intro. rrw.
        subst φ'. symmetry. eapply map_compose. }
      { eapply map_ext.
        ii. subst φ'. unfold compose, swap, id.
        des_ifs; eqb2eq loc; clarify.
        eapply floc_map in DOM; eauto.
        instantiate (1 := φ) in DOM.
        clean_set. contradict.
        exploit INJ; eauto. ii; clarify. } }
    { eapply subst_wvl_close; auto. }
    { eapply subst_loc_close_eq; auto. }
Qed.

Lemma eval_subst_wvl {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall u (U : wvalue u) ℓ',
    eval (subst_wvl_nv u ℓ' σ) t (subst_wvl_vl u ℓ' v).
Proof.
  intros.
  replace σ with (map_nv id σ) by apply map_id_is_id.
  replace v with (map_vl id v) by apply map_id_is_id.
  eapply eval_map_subst_wvl; try intro; auto.
Qed.

