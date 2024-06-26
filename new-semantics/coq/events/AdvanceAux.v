From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import EquivSemantics.
From With_events Require Import LinkDefs.
From With_events Require Import LinkFacts.
From With_events Require Import EquivLink.

Local Create HintDb advance.
Hint Constructors eval' : advance.
Hint Constructors link' : advance.

Section AdvanceAux.
  Context {var lbl loc : Type}.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Ltac inv_link :=
    match goal with
    | LINK : _ ⋊ wvl_v (vl_clos _ _) ∋ wvl_v (vl_clos _ _) |- _ => inv LINK
    | LINK : _ ⋊ wvl_v (vl_nat _) ∋ wvl_v (vl_nat _) |- _ => inv LINK
    end.

  Ltac solve_link :=
    match goal with
    | _ : _ ⋊ wvl_v (vl_nat _) ∋ _ |- _ ⋊ _ ∋ wvl_v (vl_exp _) =>
      eapply link_bval'; eauto; eapply link_nat'; eauto
    | _ : _ ⋊ wvl_v (vl_ev _) ∋ wvl_v (vl_nat _) |- _ ⋊ _ ∋ wvl_v (vl_exp _) =>
      eapply link_bval'; eauto; eapply link_predENat'; eauto
    | _ : _ ⋊ wvl_v (vl_ev _) ∋ wvl_v (vl_ev _) |- context [predE] =>
      eapply link_bval'; eauto; eapply link_predEEvent'; eauto
    | _ => eauto with advance
    end.

  Ltac t :=
    try match goal with
    | IHEVAL1 : forall _ : nv _ _ _ _, (_ ⋊ _ ∋ _) -> _,
      IHEVAL2 : forall _ : nv _ _ _ _, (_ ⋊ _ ∋ _) -> _,
      IHEVAL3 : forall _ : nv _ _ _ _, (_ ⋊ _ ∋ _) -> _ |- _
      => solve [
      exploit IHEVAL1; eauto with advance;
      intros (v1' & EVAL1' & LINK1);
      destruct v1'; try solve [inv LINK1];
      exploit IHEVAL2;
      first [solve [solve_link] | intros (v2' & EVAL2' & LINK2)];
      try (inv_link; exploit IHEVAL3; eauto with advance; intros (v3' & EVAL3' & LINK3));
      eexists; split;
      solve [eauto with advance]
      ]
    | IHEVAL1 : forall _ : nv _ _ _ _, (_ ⋊ _ ∋ _) -> _,
      IHEVAL2 : forall _ : nv _ _ _ _, (_ ⋊ _ ∋ _) -> _ |- _
      => solve [
      exploit IHEVAL1; eauto with advance;
      intros (v1' & EVAL1' & LINK1);
      destruct v1'; try solve [inv LINK1];
      exploit IHEVAL2;
      first [solve [solve_link] | intros (v2' & EVAL2' & LINK2)];
      try inv_link; eexists; split;
      solve [eauto with advance]
      ]
    | IHEVAL : forall _ : nv _ _ _ _, (_ ⋊ _ ∋ _) -> _ |- _
      => solve [
      exploit IHEVAL; eauto with advance;
      intros (v' & EVAL' & LINK');
      destruct v'; try solve [inv LINK'];
      try inv_link; eexists; split;
      solve [eauto with advance]
      ]
    | _ => solve [eexists; split; eauto with advance]
    end.

  Lemma advance_aux `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 σ' : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) v' t (EVAL : σ' ⊢ t ⇓ v') :
    forall (σ : nv var (@ltm var lbl) loc _) (LINK : σ0 ⋊ σ ∋ σ'),
      exists v, (σ ⊢ t ⇓ v) /\ (σ0 ⋊ v ∋ v').
  Proof.
    induction EVAL; ii; ss; t.
    - exploit (link_read' σ0); eauto; ss.
      intro READ'. specialize (READ' x v READ).
      des; ss.
      eexists; split; eauto.
      destruct w; ss.
      + econstructor 1; auto.
      + econstructor 2; auto.
    - exploit (link_read' σ0); eauto; ss.
      intro READ'. specialize (READ' x (wvl_recv p' v) READ).
      des; ss.
      eexists; split; eauto.
      destruct w; ss.
      + econstructor 1; auto.
      + econstructor 2; auto.
    - gensym_tac (L ++ floc_nv σ0 ++ floc_nv σ1 ++ floc_vl v1) ν.
      match goal with
      | IH : forall _, ~ In _ ?L -> _, ν : loc, nIN : ~ In ν ?L |- _ =>
        exploit (IH ν nIN);
        first [eapply link_floc'; eauto | idtac]
      end.
      intros (v1' & EVAL1 & LINK1).
      eapply link_lc' in LINK as Σ1. inv Σ1. inv VAL.
      eapply eval_lc' in EVAL1 as V1; try solve [econstructor; eauto].
      assert (forall ℓ p' (FREE : ~ In ℓ (floc_nv σ1)),
        open_loc_vl 0 (ℓ, p') (close_vl 0 (ν, t1) v1') = subst_loc_vl (ℓ, p') (ν, t1) v1') as RR.
      { intros.
        assert (close_open_loc_eq_vl v1') by eapply close_open_loc_eq. rw.
        assert (open_loc_lc_vl v1' V1) by (eapply open_loc_lc; eauto). rw.
        reflexivity. }
      assert (forall ℓ p' (FREE : ~ In ℓ (floc_nv σ1)),
        (nv_floc x (ℓ, p') σ1 ⊢ t1 ⇓ open_loc_vl 0 (ℓ, p') (close_vl 0 (ν, t1) v1'))).
      { intros. apply eval_subst_loc' with (ν := (ℓ, p')) (ℓ' := (ν, t1)) in EVAL1.
        ss. assert (@eqb_ltm var lbl _ _ = eqb) as HINT by reflexivity.
        rewrite HINT in *.
        repeat rewrite eqb_refl in EVAL1. ss.
        assert (RR' : subst_loc_fresh_nv σ1) by eapply subst_loc_fresh.
        rewrite RR' in EVAL1; eauto.
        rewrite RR; eauto. }
      assert (forall ℓ p' (FREE : ~ In ℓ (floc_nv σ1)),
        σ0 ⋊ open_loc_vl 0 (ℓ, p') (close_vl 0 (ν, t1) v1') ∋ open_loc_vl 0 (ℓ, p') v1).
      { intros. apply link_subst_loc' with (ν := (ℓ, p')) (ℓ' := (ν, t1)) in LINK1; eauto.
        assert (open_loc_subst_loc_vl v1) as RR' by eapply open_loc_subst_loc.
        simpl in LINK1. rewrite RR' in LINK1. clear RR'.
        repeat rewrite eqb_refl in LINK1. ss.
        rewrite RR; eauto.
        assert (subst_loc_fresh_nv σ0) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. clear RR'.
        assert (subst_loc_fresh_vl v1) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. }
      assert (σ0 ⋊ wvl_recv t1 (close_vl 0 (ν, t1) v1') ∋ wvl_recv t1 v1).
      { econstructor; eauto. }
      exploit (IHEVAL (nv_bval x (wvl_recv t1 (close_vl 0 (ν, t1) v1')) σ1)).
      + econstructor; eauto.
      + intros (v2' & EVAL2 & LINK2).
        destruct v2'; try solve [inv LINK2].
        * exists (nv_bval x (wvl_recv t1 (close_vl 0 (ν, t1) v1')) (nv_ev E)).
          split. eapply ev_bindevent'; eauto.
          econstructor; eauto.
          econstructor; eauto.
        * exists (nv_bval x (wvl_recv t1 (close_vl 0 (ν, t1) v1')) σ3).
          split. econstructor; eauto.
          econstructor; eauto.
    - gensym_tac (L ++ floc_nv σ0 ++ floc_nv σ1 ++ floc_vl v1) ν.
      match goal with
      | IH : forall _, ~ In _ ?L -> _, ν : loc, nIN : ~ In ν ?L |- _ =>
        exploit (IH ν nIN);
        first [eapply link_floc'; eauto | idtac]
      end.
      intros (v1' & EVAL1 & LINK1).
      eapply link_lc' in LINK as Σ1. inv Σ1. inv VAL.
      eapply eval_lc' in EVAL1 as V1; try solve [econstructor; eauto].
      assert (forall ℓ p' (FREE : ~ In ℓ (floc_nv σ1)),
        open_loc_vl 0 (ℓ, p') (close_vl 0 (ν, t1) v1') = subst_loc_vl (ℓ, p') (ν, t1) v1') as RR.
      { intros.
        assert (close_open_loc_eq_vl v1') by eapply close_open_loc_eq. rw.
        assert (open_loc_lc_vl v1' V1) by (eapply open_loc_lc; eauto). rw.
        reflexivity. }
      assert (forall ℓ p' (FREE : ~ In ℓ (floc_nv σ1)),
        (nv_floc x (ℓ, p') σ1 ⊢ t1 ⇓ open_loc_vl 0 (ℓ, p') (close_vl 0 (ν, t1) v1'))).
      { intros. apply eval_subst_loc' with (ν := (ℓ, p')) (ℓ' := (ν, t1)) in EVAL1.
        ss. assert (@eqb_ltm var lbl _ _ = eqb) as HINT by reflexivity.
        rewrite HINT in *.
        repeat rewrite eqb_refl in EVAL1. ss.
        assert (RR' : subst_loc_fresh_nv σ1) by eapply subst_loc_fresh.
        rewrite RR' in EVAL1; eauto.
        rewrite RR; eauto. }
      assert (forall ℓ p' (FREE : ~ In ℓ (floc_nv σ1)),
        σ0 ⋊ open_loc_vl 0 (ℓ, p') (close_vl 0 (ν, t1) v1') ∋ open_loc_vl 0 (ℓ, p') v1).
      { intros. apply link_subst_loc' with (ν := (ℓ, p')) (ℓ' := (ν, t1)) in LINK1; eauto.
        assert (open_loc_subst_loc_vl v1) as RR' by eapply open_loc_subst_loc.
        simpl in LINK1. rewrite RR' in LINK1. clear RR'.
        repeat rewrite eqb_refl in LINK1. ss.
        rewrite RR; eauto.
        assert (subst_loc_fresh_nv σ0) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. clear RR'.
        assert (subst_loc_fresh_vl v1) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. }
      assert (σ0 ⋊ wvl_recv t1 (close_vl 0 (ν, t1) v1') ∋ wvl_recv t1 v1).
      { econstructor; eauto. }
      exploit (IHEVAL (nv_bval x (wvl_recv t1 (close_vl 0 (ν, t1) v1')) σ1)).
      + econstructor; eauto.
      + intros (v2' & EVAL2 & LINK2).
        destruct v2'; try solve [inv LINK2].
        exists (nv_bval x (wvl_recv t1 (close_vl 0 (ν, t1) v1')) (nv_ev E)).
        split. eapply ev_bindevent'; eauto.
        econstructor; eauto.
        eapply link_holeEvent'.
        assumption.
  Qed.
End AdvanceAux.

