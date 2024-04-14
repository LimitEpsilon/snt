From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.

Inductive Eval {var loc} `{Eq var} `{Eq loc} (σ : nv var loc (@val var)): tm -> (vl var loc val) -> Prop :=
| Ev_id x v (READ : read_env σ x = Env_wvl (wvl_v v))
: Eval σ (tm_var x) v
| Ev_rec x v (READ : read_env σ x = Env_wvl (wvl_recv v))
: Eval σ (tm_var x) (open_wvl_vl 0 (wvl_recv v) v)
| Ev_fn x t
: Eval σ (tm_lam x t) (vl_clos (v_fn x t) σ)
| Ev_app t1 t2 x e σ1 v2 v
  (FN : Eval σ t1 (vl_clos (v_fn x e) σ1))
  (ARG : Eval σ t2 v2)
  (BODY : Eval (nv_bval x (wvl_v v2) σ1) e v)
: Eval σ (tm_app t1 t2) v
| Ev_appevent t1 t2 E1 v2
  (FN : Eval σ t1 (vl_ev E1))
  (ARG : Eval σ t2 v2)
: Eval σ (tm_app t1 t2) (vl_ev (Call E1 v2))
| Ev_link t1 t2 σ1 v
  (MOD : Eval σ t1 (vl_exp σ1))
  (IMP : Eval σ1 t2 v)
: Eval σ (tm_link t1 t2) v
| Ev_linkevent t1 t2 E1 v
  (MOD : Eval σ t1 (vl_ev E1))
  (IMP : Eval (nv_ev E1) t2 v)
: Eval σ (tm_link t1 t2) v
| Ev_mt
: Eval σ tm_mt (vl_exp nv_mt)
| Ev_bind x t1 t2 L v1 σ2
  (BIND : forall ℓ (nIN : ~ In ℓ L),
    Eval (nv_floc x ℓ σ) t1 (open_loc_vl 0 ℓ v1))
  (MOD : Eval (nv_bval x (wvl_recv v1) σ) t2 (vl_exp σ2))
: Eval σ (tm_bind x t1 t2) (vl_exp (nv_bval x (wvl_recv v1) σ2))
| Ev_bindevent x t1 t2 L v1 E2
  (BIND : forall ℓ (nIN : ~ In ℓ L),
    Eval (nv_floc x ℓ σ) t1 (open_loc_vl 0 ℓ v1))
  (MOD : Eval (nv_bval x (wvl_recv v1) σ) t2 (vl_ev E2))
: Eval σ (tm_bind x t1 t2) (vl_exp (nv_bval x (wvl_recv v1) (nv_ev E2)))
.

Lemma equiv_l {var loc} `{Eq var} `{Name loc}
  t (σ : nv var loc (@val var)) (Σ : env σ) v (EVAL : eval σ t v) :
  forall φ (INJ : oto φ), Eval (map_nv φ σ) t (map_vl φ v).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - apply read_env_map with (φ := φ) in READ.
    ss. econstructor; eauto.
  - apply read_env_map with (φ := φ) in READ.
    ss. 
    assert (map_open_wvl_vl _ _ _ v) by eapply map_open_wvl.
    rw.
    eapply Ev_rec; ss; eauto.
  - apply eval_lc in EVAL1 as V1; eauto. inv V1.
    apply eval_lc in EVAL2 as V2; eauto.
    exploit IHEVAL3; eauto. repeat constructor; auto.
    econstructor; eauto.
  - apply eval_lc in EVAL1 as Σ1; eauto. inv Σ1.
    econstructor; eauto.
  - apply eval_lc in EVAL1 as Σ1; eauto. inv Σ1.
    exploit IHEVAL2; eauto. constructor; auto.
    eapply Ev_linkevent; eauto.
  - apply eval_lc in EVAL1 as V1; try solve [repeat constructor; auto].
    assert (value (map_vl φ v1)) as V1' by (eapply map_lc; auto).
    assert (wvalue (wvl_recv (close_vl 0 ℓ v1))) as V1''.
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl _ _ _ v1) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl _ _ _ v1 V1) by (eapply open_loc_lc; eauto). rw.
    eapply subst_loc_lc. auto.
    repeat match goal with
    | IH : env ?σ -> _ |- _ =>
      assert (env σ) as Σ' by repeat (constructor; auto);
      specialize (IH Σ'); clear Σ'
    end.
    eapply Ev_bind; eauto.
    instantiate (1 := φ ℓ :: floc_nv (map_nv φ σ)).
    intros ℓ'' nIN. split_nIn.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    assert (map_close_vl _ _ _ v1) by eapply map_close.
    rw; eauto.
    assert (close_open_loc_eq_vl _ _ _ (map_vl φ v1)) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl _ _ _ (map_vl φ v1) V1') by (eapply open_loc_lc; eauto). rw.
    set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
    replace (map_nv φ σ) with (map_nv φ' σ).
    replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)) with (map_vl φ' v1).
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
    + assert (swap_is_subst_vl _ _ _ (map_vl φ v1)) as RR by eapply swap_is_subst.
      specialize (RR id).
      exploit RR; eauto. unfold oto. auto.
      instantiate (1 := φ ℓ).
      replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
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
    assert (wvalue (wvl_recv (close_vl 0 ℓ v1))) as V1''.
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl _ _ _ v1) by eapply close_open_loc_eq.
    rw.
    assert (open_loc_lc_vl _ _ _ v1 V1) by (eapply open_loc_lc; eauto).
    rw.
    eapply subst_loc_lc. auto.
    repeat match goal with
    | IH : env ?σ -> _ |- _ =>
      assert (env σ) as Σ' by repeat (constructor; auto);
      specialize (IH Σ'); clear Σ'
    end.
    eapply Ev_bindevent; eauto.
    instantiate (1 := φ ℓ :: floc_nv (map_nv φ σ)).
    intros ℓ'' nIN. split_nIn.
    assert (~ In ℓ'' (floc_vl (map_vl φ v1))) as HINT.
    { intro. apply eval_map with (φ := φ) in EVAL1; auto.
      eapply eval_floc_dec in EVAL1; eauto. ss. des; ss. }
    assert (map_close_vl _ _ _ v1) by eapply map_close. rw; eauto.
    assert (close_open_loc_eq_vl _ _ _ (map_vl φ v1)) by eapply close_open_loc_eq. rw.
    assert (open_loc_lc_vl _ _ _ (map_vl φ v1) V1') by (eapply open_loc_lc; eauto). rw.
    set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
    replace (map_nv φ σ) with (map_nv φ' σ).
    replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v1)) with (map_vl φ' v1).
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
    + assert (swap_is_subst_vl _ _ _ (map_vl φ v1)) as RR by eapply swap_is_subst.
      specialize (RR id).
      exploit RR; eauto. unfold oto. auto.
      instantiate (1 := φ ℓ).
      replace (map_vl id (map_vl φ v1)) with (map_vl φ v1) by (symmetry; eapply map_id_is_id).
      unfold id at 2. unfold id at 2.
      intro. rrw.
      subst φ'. symmetry. eapply map_compose. 
    + eapply map_ext.
      ii. subst φ'. unfold compose, swap, id.
      des_ifs; eqb2eq loc; clarify.
      eapply floc_map in DOM; eauto. contradict.
      exploit INJ; eauto. ii; clarify.
Qed.

Lemma equiv_r {var loc} `{Eq var} `{Name loc}
  t (σ : nv var loc (@val var)) v (EVAL : Eval σ t v) :
  eval σ t v.
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - gensym_tac (floc_nv σ ++ floc_vl v1 ++ L) ℓ.
    assert (close_vl 0 ℓ (open_loc_vl 0 ℓ v1) = v1) as RR.
    { assert (open_loc_close_vl _ _ _ v1) by eapply open_loc_close.
      rw. eapply close_fresh; eauto. }
    rewrite <- RR.
    eapply ev_bind; eauto.
    rw. auto.
  - gensym_tac (floc_nv σ ++ floc_vl v1 ++ L) ℓ.
    assert (close_vl 0 ℓ (open_loc_vl 0 ℓ v1) = v1) as RR.
    { assert (open_loc_close_vl _ _ _ v1) by eapply open_loc_close.
      rw. eapply close_fresh; eauto. }
    rewrite <- RR.
    eapply ev_bindevent; eauto.
    rw. auto.
Qed.

Lemma equiv_semantics {var loc} `{Eq var} `{Name loc}
  t (σ : nv var loc (@val var)) (Σ : env σ) v :
  eval σ t v <-> Eval σ t v.
Proof.
  split.
  - intro.
    replace σ with (map_nv id σ) by apply map_id_is_id.
    replace v with (map_vl id v) by apply map_id_is_id.
    eapply equiv_l; eauto. ii; ss.
  - eapply equiv_r.
Qed.

Lemma Eval_lc {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : Eval σ t v) :
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
  - assert (wvalue (wvl_recv v1)).
    + econstructor. instantiate (1 := L).
      intros.
      assert (env (nv_floc x ℓ σ)).
      repeat (econstructor; eauto).
      auto.
    + repeat (constructor; auto).
      exploit IHEVAL.
      repeat (constructor; auto).
      intro LC'.
      inv LC'. auto.
  - assert (wvalue (wvl_recv v1)).
    + econstructor. instantiate (1 := L).
      intros.
      assert (env (nv_floc x ℓ σ)).
      repeat (econstructor; eauto).
      auto.
    + repeat (constructor; auto).
      exploit IHEVAL.
      repeat (constructor; auto).
      intro LC'.
      inv LC'. auto.
Qed.

Lemma Eval_subst_loc {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : Eval σ t v) :
  forall ν ℓ', Eval (subst_loc_nv ν ℓ' σ) t (subst_loc_vl ν ℓ' v).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - econstructor 1.
    erewrite read_env_subst_loc; eauto.
    ss.
  - assert (open_wvl_subst_loc_vl _ _ _ v) by (eapply open_wvl_subst_loc; auto).
    rw; eauto.
    econstructor 2.
    erewrite read_env_subst_loc; eauto.
    ss.
  - eapply Ev_bind; eauto.
    instantiate (1 := ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN)
    end.
    instantiate (1 := ℓ'). instantiate (1 := ν).
    rewrite <- eqb_neq in nIN.
    rw.
    assert (open_loc_subst_loc_vl _ _ _ v1) by eapply open_loc_subst_loc.
    rw. rw. auto.
  - eapply Ev_bindevent; eauto.
    instantiate (1 := ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN)
    end.
    instantiate (1 := ℓ'). instantiate (1 := ν).
    rewrite <- eqb_neq in nIN.
    rw.
    assert (open_loc_subst_loc_vl _ _ _ v1) by eapply open_loc_subst_loc.
    rw. rw. auto.
Qed.

Lemma Eval_subst_wvl {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : Eval σ t v) :
  forall u (U : wvalue u) ℓ', Eval (subst_wvl_nv u ℓ' σ) t (subst_wvl_vl u ℓ' v).
Proof.
  induction EVAL; ii; ss;
  try solve [econstructor; eauto].
  - econstructor 1.
    erewrite read_env_subst_wvl; eauto.
    ss.
  - assert (open_wvl_subst_wvl_vl _ _ _ v) by (eapply open_wvl_subst_wvl; auto).
    rw; eauto.
    econstructor 2.
    erewrite read_env_subst_wvl; eauto.
    ss.
  - eapply Ev_bind; eauto.
    instantiate (1 := ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN); eauto
    end.
    instantiate (1 := ℓ').
    des_goal; eqb2eq loc; clarify.
    assert (open_loc_subst_wvl_vl _ _ _ v1) by (eapply open_loc_subst_wvl; eauto).
    rw; eauto.
  - eapply Ev_bindevent; eauto.
    instantiate (1 := ℓ' :: L).
    ii. split_nIn.
    match goal with
    | IH : forall _, ~ In _ ?L -> _, nIN : ~ In ?ν ?L |- _ =>
      exploit (IH ν nIN); eauto
    end.
    instantiate (1 := ℓ').
    des_goal; eqb2eq loc; clarify.
    assert (open_loc_subst_wvl_vl _ _ _ v1) by (eapply open_loc_subst_wvl; eauto).
    rw; eauto.
Qed.

Notation " σ '⊢' t '⇓' v " := (Eval σ t v)
  (at level 100, t at next level, v at next level, right associativity).

