From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.

Inductive eval' {var lbl loc} `{Eq var} `{Eq lbl} `{Eq loc}
  (σ : nv var (@ltm var lbl) loc (@val var lbl)): ltm -> (vl var (@ltm var lbl) loc val) -> Prop :=
| ev_id' p x v (READ : read_env σ x = Env_wvl (wvl_v v))
: eval' σ (lblled p (tm_var x)) v
| ev_rec' p x p' v (READ : read_env σ x = Env_wvl (wvl_recv p' v))
: eval' σ (lblled p (tm_var x)) (open_wvl_vl 0 (wvl_recv p' v) v)
| ev_fn' p x t
: eval' σ (lblled p (tm_lam x t)) (vl_clos (v_fn x t) σ)
| ev_app' p t1 t2 x e σ1 v2 v
  (FN : eval' σ t1 (vl_clos (v_fn x e) σ1))
  (ARG : eval' σ t2 v2)
  (BODY : eval' (nv_bval x (wvl_v v2) σ1) e v)
: eval' σ (lblled p (tm_app t1 t2)) v
| ev_appevent' p t1 t2 E1 v2
  (FN : eval' σ t1 (vl_ev E1))
  (ARG : eval' σ t2 v2)
: eval' σ (lblled p (tm_app t1 t2)) (vl_ev (Call E1 v2))
| ev_link' p t1 t2 σ1 v
  (MOD : eval' σ t1 (vl_exp σ1))
  (IMP : eval' σ1 t2 v)
: eval' σ (lblled p (tm_link t1 t2)) v
| ev_linkevent' p t1 t2 E1 v
  (MOD : eval' σ t1 (vl_ev E1))
  (IMP : eval' (nv_ev E1) t2 v)
: eval' σ (lblled p (tm_link t1 t2)) v
| ev_mt' p
: eval' σ (lblled p tm_mt) (vl_exp nv_mt)
| ev_bind' p x t1 t2 L v1 σ2
  (BIND : forall ℓ (nIN : ~ In ℓ L),
    eval' (nv_floc x (ℓ, t1) σ) t1 (open_loc_vl 0 (ℓ, t1) v1))
  (MOD : eval' (nv_bval x (wvl_recv t1 v1) σ) t2 (vl_exp σ2))
: eval' σ (lblled p (tm_bind x t1 t2)) (vl_exp (nv_bval x (wvl_recv t1 v1) σ2))
| ev_bindevent' p x t1 t2 L v1 E2
  (BIND : forall ℓ (nIN : ~ In ℓ L),
    eval' (nv_floc x (ℓ, t1) σ) t1 (open_loc_vl 0 (ℓ, t1) v1))
  (MOD : eval' (nv_bval x (wvl_recv t1 v1) σ) t2 (vl_ev E2))
: eval' σ (lblled p (tm_bind x t1 t2)) (vl_exp (nv_bval x (wvl_recv t1 v1) (nv_ev E2)))
| ev_zero' p
: eval' σ (lblled p tm_zero) (vl_nat 0)
| ev_succ' p t n
  (PRED : eval' σ t (vl_nat n))
: eval' σ (lblled p (tm_succ t)) (vl_nat (S n))
| ev_succevent' p t E
  (PRED : eval' σ t (vl_ev E))
: eval' σ (lblled p (tm_succ t)) (vl_ev (SuccE E))
| ev_casezero' p t z n s v
  (MATCH : eval' σ t (vl_nat 0))
  (ZERO : eval' σ z v)
: eval' σ (lblled p (tm_case t z n s)) v
| ev_casesucc' p t z n s m v
  (MATCH' : eval' σ t (vl_nat (S m)))
  (SUCC' : eval' (nv_bval n (wvl_v (vl_nat m)) σ) s v)
: eval' σ (lblled p (tm_case t z n s)) v
| ev_casezeroevent' p t z n s E v
  (MATCH : eval' σ t (vl_ev E))
  (ZERO : eval' σ z v)
: eval' σ (lblled p (tm_case t z n s)) v
| ev_casesuccevent' p t z n s E v
  (MATCH : eval' σ t (vl_ev E))
  (SUCC : eval' (nv_bval n (wvl_v (vl_ev (predE E))) σ) s v)
: eval' σ (lblled p (tm_case t z n s)) v
.

Lemma equiv_l {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc}
  t (σ : nv var (@ltm var lbl) loc val) (Σ : env σ) v (EVAL : eval σ t v) :
  forall φ (INJ : oto φ), eval' (map_nv φ σ) t (map_vl φ v).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - apply read_env_map with (φ := φ) in READ.
    ss. econstructor; eauto.
  - apply read_env_map with (φ := φ) in READ.
    ss. 
    assert (map_open_wvl_vl v) by eapply map_open_wvl.
    rw.
    eapply ev_rec'; ss; eauto.
  - apply eval_lc in EVAL1 as V1; eauto. inv V1.
    apply eval_lc in EVAL2 as V2; eauto.
    exploit IHEVAL3; eauto. repeat constructor; auto.
    econstructor; eauto.
  - apply eval_lc in EVAL1 as Σ1; eauto. inv Σ1.
    econstructor; eauto.
  - apply eval_lc in EVAL1 as Σ1; eauto. inv Σ1.
    exploit IHEVAL2; eauto. constructor; auto.
    eapply ev_linkevent'; eauto.
  - apply eval_lc in EVAL1 as V1; try solve [repeat constructor; auto].
    assert (value (map_vl φ v1)) as V1' by (eapply map_lc; auto).
    assert (wvalue (wvl_recv t1 (close_vl 0 (ℓ, t1) v1))) as V1''.
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl v1) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl v1 V1) by (eapply open_loc_lc; eauto). rw.
    eapply subst_loc_lc. auto.
    repeat match goal with
    | IH : env ?σ -> _ |- _ =>
      assert (env σ) as Σ' by repeat (constructor; auto);
      specialize (IH Σ'); clear Σ'
    end.
    eapply ev_bind'; eauto.
    instantiate (1 := φ ℓ :: floc_nv (map_nv φ σ)).
    intros ℓ'' nIN. split_nIn.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    assert (map_close_vl v1) by eapply map_close.
    rw; eauto.
    assert (close_open_loc_eq_vl (map_vl φ v1)) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl (map_vl φ v1) V1') by (eapply open_loc_lc; eauto). rw.
    set (swap id ℓ'' (φ ℓ) <*> φ) as φ'.
    replace (map_nv φ σ) with (map_nv φ' σ).
    replace (subst_loc_vl (ℓ'', t1) (φ ℓ, t1) (map_vl φ v1)) with (map_vl φ' v1).
    exploit (IHEVAL1 φ').
    + subst φ'. unfold compose, swap, id.
      ii; ss; des_ifs;
      repeat match goal with
      | _ => eqb2eq loc
      | H : φ _ = φ _ |- _ => apply INJ in H
      | _ => clarify
      end.
    + replace (φ' ℓ) with ℓ''; auto.
      subst φ'; unfold compose, swap, id; s.
      des_ifs; eqb2eq loc; clarify.
    + assert (swap_is_subst_vl (map_vl φ v1)) as RR by eapply swap_is_subst.
      specialize (RR id).
      exploit RR; eauto. unfold oto. auto.
      instantiate (1 := t1). instantiate (1 := φ ℓ).
      * intros p' IN.
        apply eval_map with (φ := φ) in EVAL1; eauto.
        eapply eval_flloc_dec in EVAL1; eauto. ss; des; des_ifs.
        apply (in_map fst) in EVAL1; ss.
        assert (trans_floc_nv (map_nv φ σ)) as RR' by apply trans_floc.
        rewrite <- RR' in EVAL1. eapply map_floc in EVAL1; eauto. clarify.
      * replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
        unfold id at 2. unfold id at 2.
        intro. rrw.
        subst φ'. symmetry. eapply map_compose.
    + eapply map_ext.
      ii. subst φ'. unfold compose, swap, id.
      des_ifs; eqb2eq loc; clarify.
      eapply floc_map in DOM; eauto. contradict.
      exploit INJ; eauto. ii; clarify.
  - apply eval_lc in EVAL1 as V1; try solve [repeat constructor; auto].
    assert (value (map_vl φ v1)) as V1' by (eapply map_lc; auto).
    assert (wvalue (wvl_recv t1 (close_vl 0 (ℓ, t1) v1))) as V1''.
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl v1) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl v1 V1) by (eapply open_loc_lc; eauto). rw.
    eapply subst_loc_lc. auto.
    repeat match goal with
    | IH : env ?σ -> _ |- _ =>
      assert (env σ) as Σ' by repeat (constructor; auto);
      specialize (IH Σ'); clear Σ'
    end.
    eapply ev_bindevent'; eauto.
    instantiate (1 := φ ℓ :: floc_nv (map_nv φ σ)).
    intros ℓ'' nIN. split_nIn.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    assert (map_close_vl v1) by eapply map_close.
    rw; eauto.
    assert (close_open_loc_eq_vl (map_vl φ v1)) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl (map_vl φ v1) V1') by (eapply open_loc_lc; eauto). rw.
    set (swap id ℓ'' (φ ℓ) <*> φ) as φ'.
    replace (map_nv φ σ) with (map_nv φ' σ).
    replace (subst_loc_vl (ℓ'', t1) (φ ℓ, t1) (map_vl φ v1)) with (map_vl φ' v1).
    exploit (IHEVAL1 φ').
    + subst φ'. unfold compose, swap, id.
      ii; ss; des_ifs;
      repeat match goal with
      | _ => eqb2eq loc
      | H : φ _ = φ _ |- _ => apply INJ in H
      | _ => clarify
      end.
    + replace (φ' ℓ) with ℓ''; auto.
      subst φ'; unfold compose, swap, id; s.
      des_ifs; eqb2eq loc; clarify.
    + assert (swap_is_subst_vl (map_vl φ v1)) as RR by eapply swap_is_subst.
      specialize (RR id).
      exploit RR; eauto. unfold oto. auto.
      instantiate (1 := t1). instantiate (1 := φ ℓ).
      * intros p' IN.
        apply eval_map with (φ := φ) in EVAL1; eauto.
        eapply eval_flloc_dec in EVAL1; eauto. ss; des; des_ifs.
        apply (in_map fst) in EVAL1; ss.
        assert (trans_floc_nv (map_nv φ σ)) as RR' by apply trans_floc.
        rewrite <- RR' in EVAL1. eapply map_floc in EVAL1; eauto. clarify.
      * replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
        unfold id at 2. unfold id at 2.
        intro. rrw.
        subst φ'. symmetry. eapply map_compose.
    + eapply map_ext.
      ii. subst φ'. unfold compose, swap, id.
      des_ifs; eqb2eq loc; clarify.
      eapply floc_map in DOM; eauto. contradict.
      exploit INJ; eauto. ii; clarify.
  - apply eval_lc in EVAL1 as Σ1; eauto. inv Σ1.
    exploit IHEVAL2; eauto. repeat constructor; auto.
    eapply ev_casesucc'; eauto.
  - apply eval_lc in EVAL1 as Σ1; eauto. inv Σ1.
    exploit IHEVAL2; eauto. repeat constructor; auto. i.
    eapply ev_casesuccevent'; eauto.
    rewrite predE_map in *; auto.
Qed.

Lemma equiv_r {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc}
  t (σ : nv var (@ltm var lbl) loc val) v (EVAL : eval' σ t v) :
  eval σ t v.
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - gensym_tac (floc_nv σ ++ floc_vl v1 ++ L) ℓ.
    assert (close_vl 0 (ℓ, t1) (open_loc_vl 0 (ℓ, t1) v1) = v1) as RR.
    { assert (open_loc_close_vl v1) by eapply open_loc_close.
      rw. eapply close_fresh; eauto. }
    rewrite <- RR.
    eapply ev_bind; eauto.
    rw. auto.
  - gensym_tac (floc_nv σ ++ floc_vl v1 ++ L) ℓ.
    assert (close_vl 0 (ℓ, t1) (open_loc_vl 0 (ℓ, t1) v1) = v1) as RR.
    { assert (open_loc_close_vl v1) by eapply open_loc_close.
      rw. eapply close_fresh; eauto. }
    rewrite <- RR.
    eapply ev_bindevent; eauto.
    rw. auto.
Qed.

Lemma equiv_semantics {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc}
  t (σ : nv var (@ltm var lbl) loc val) (Σ : env σ) v :
  eval σ t v <-> eval' σ t v.
Proof.
  split.
  - intro.
    replace σ with (map_nv id σ) by apply map_id_is_id.
    replace v with (map_vl id v) by apply map_id_is_id.
    eapply equiv_l; eauto. ii; ss.
  - eapply equiv_r.
Qed.

Lemma eval_lc' {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc} t (σ : nv var (@ltm var lbl) loc val) v (EVAL : eval' σ t v) :
  forall (LC : env σ), value v.
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_lc in READ; eauto. inv READ. auto.
  - eapply read_env_lc in READ; eauto.
    inversion READ; clarify.
    gensym_tac (L ++ floc_vl v) ν.
    assert (subst_intro_vl v) by eapply subst_intro.
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
  - assert (wvalue (wvl_recv t1 v1)).
    + econstructor. instantiate (1 := L).
      intros.
      assert (env (nv_floc x (ℓ, t1) σ)).
      repeat (econstructor; eauto).
      auto.
    + repeat (constructor; auto).
      exploit IHEVAL.
      repeat (constructor; auto).
      intro LC'.
      inv LC'. auto.
  - assert (wvalue (wvl_recv t1 v1)).
    + econstructor. instantiate (1 := L).
      intros.
      assert (env (nv_floc x (ℓ, t1) σ)).
      repeat (econstructor; eauto).
      auto.
    + repeat (constructor; auto).
      exploit IHEVAL.
      repeat (constructor; auto).
      intro LC'.
      inv LC'. auto.
  - repeat constructor.
  - repeat constructor.
  - exploit IHEVAL; eauto. intro LC'.
    inversion LC'; repeat constructor; auto.
  - apply IHEVAL2. repeat constructor; auto.
  - apply IHEVAL2. repeat constructor; auto.
    exploit IHEVAL1; eauto. intro LC'.
    inversion LC'; auto.
Qed.

Lemma eval_subst_loc' {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc} t (σ : nv var (@ltm var lbl) loc val) v (EVAL : eval' σ t v) :
  forall ν ℓ', eval' (subst_loc_nv ν ℓ' σ) t (subst_loc_vl ν ℓ' v).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - econstructor 1.
    erewrite read_env_subst_loc; eauto.
    ss.
  - assert (open_wvl_subst_loc_vl v) by (eapply open_wvl_subst_loc; auto).
    rw; eauto.
    econstructor 2.
    erewrite read_env_subst_loc; eauto.
    ss.
  - eapply ev_bind'; eauto.
    instantiate (1 := fst ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN)
    end.
    instantiate (1 := ℓ'). instantiate (1 := ν).
    rewrite <- eqb_neq in nIN.
    destruct ℓ'; ss; rw.
    assert (open_loc_subst_loc_vl v1) by eapply open_loc_subst_loc.
    rw. s. rw. auto.
  - eapply ev_bindevent'; eauto.
    instantiate (1 := fst ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN)
    end.
    instantiate (1 := ℓ'). instantiate (1 := ν).
    rewrite <- eqb_neq in nIN.
    destruct ℓ'; ss; rw.
    assert (open_loc_subst_loc_vl v1) by eapply open_loc_subst_loc.
    rw. s. rw. auto.
  - eapply ev_casesuccevent'; auto.
    specialize (IHEVAL2 ν ℓ').
    rewrite predE_subst_loc in *. auto.
Qed.

Lemma eval_subst_wvl' {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc} t (σ : nv var (@ltm var lbl) loc val) v (EVAL : eval' σ t v) :
  forall u (U : wvalue u) ℓ', eval' (subst_wvl_nv u ℓ' σ) t (subst_wvl_vl u ℓ' v).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - econstructor 1.
    erewrite read_env_subst_wvl; eauto.
    ss.
  - assert (open_wvl_subst_wvl_vl v) by (eapply open_wvl_subst_wvl; auto).
    rw; eauto.
    econstructor 2.
    erewrite read_env_subst_wvl; eauto.
    ss.
  - eapply ev_bind'; eauto.
    instantiate (1 := fst ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN); eauto
    end.
    instantiate (1 := ℓ').
    rewrite <- eqb_neq in nIN.
    destruct ℓ'; ss; rw.
    assert (open_loc_subst_wvl_vl v1) by (eapply open_loc_subst_wvl; eauto).
    rw; ii; ss; eqb2eq loc; clarify.
  - eapply ev_bindevent'; eauto.
    instantiate (1 := fst ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN); eauto
    end.
    instantiate (1 := ℓ').
    rewrite <- eqb_neq in nIN.
    destruct ℓ'; ss; rw.
    assert (open_loc_subst_wvl_vl v1) by (eapply open_loc_subst_wvl; eauto).
    rw; ii; ss; eqb2eq loc; clarify.
  - eapply ev_casesuccevent'; auto.
    exploit IHEVAL2; eauto. instantiate (1 := ℓ').
    rewrite predE_subst_wvl. auto.
Qed.

Notation " σ '⊢' t '⇓' v " := (eval' σ t v)
  (at level 100, t at next level, v at next level, right associativity).

