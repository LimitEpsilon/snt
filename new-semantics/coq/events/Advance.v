From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import EquivSemantics.
From With_events Require Import LinkDefs.
From With_events Require Import LinkFacts.
From With_events Require Import EquivLink.

Section Advance.
  Variable var : Type.
  Variable loc : Type.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Lemma advance_Eval `{Name loc} `{Eq var}
    (σ0 σ' : nv var loc _) (Σ0 : env σ0) v' t (EVAL : σ' ⊢ t ⇓ v') :
    forall (σ : nv var loc _) (LINK : σ0 ⋊ σ ∋ σ'),
      exists v, Eval σ t v /\ (σ0 ⋊ v ∋ v').
  Proof.
    induction EVAL; ii; ss.
    - exploit Link_read; eauto; ss.
      intro READ'. specialize (READ' x v READ).
      des; ss.
      eexists; split; eauto.
      destruct w; ss.
      + econstructor 1; auto.
      + econstructor 2; auto.
    - exploit Link_read; eauto; ss.
      intro READ'. specialize (READ' x (wvl_recv v) READ).
      des; ss.
      eexists; split; eauto.
      destruct w; ss.
      + econstructor 1; auto.
      + econstructor 2; auto.
    - eexists; split; econstructor; eauto.
    - exploit IHEVAL1; eauto.
      exploit IHEVAL2; eauto.
      intros (v2' & EVAL2' & LINK2).
      intros (v1' & EVAL1' & LINK1).
      destruct v1'; try solve [inv LINK1].
      + exists (Call E v2').
        split. eapply Ev_appevent; eauto.
        econstructor; eauto.
      + inv LINK1.
        exploit IHEVAL3; eauto.
        eapply Link_bval; eauto.
        intros (v' & EVAL' & LINK').
        exists v'. split; try econstructor; eauto.
    - exploit IHEVAL1; eauto.
      exploit IHEVAL2; eauto.
      intros (v2' & EVAL2' & LINK2).
      intros (v1' & EVAL1' & LINK1).
      destruct v1'; try solve [inv LINK1].
      eexists. split.
      eapply Ev_appevent; eauto.
      eapply Link_CallEvent; eauto.
    - exploit IHEVAL1; eauto.
      intros (v1' & EVAL1' & LINK1).
      destruct v1'; try solve [inv LINK1].
      + specialize (IHEVAL2 (nv_ev E)).
        exploit IHEVAL2.
        econstructor; eauto.
        ii; des; eexists.
        split. eapply Ev_linkevent; eauto. auto.
      + exploit IHEVAL2; eauto; ii; des; eexists.
        split. eapply Ev_link; eauto.
        auto.
    - exploit IHEVAL1; eauto.
      intros (v1' & EVAL1' & LINK1).
      destruct v1'; try solve [inv LINK1].
      specialize (IHEVAL2 (nv_ev E)).
      exploit IHEVAL2.
      apply Link_holeEvent; auto.
      ii; des; eexists.
      split. eapply Ev_linkevent; eauto. auto.
    - exists nv_mt. split; econstructor; eauto.
    - gensym_tac (L ++ floc_nv σ0 ++ floc_nv σ1 ++ floc_vl v1) ν.
      match goal with
      | IH : forall _, ~ In _ ?L -> _, ν : loc, nIN : ~ In ν ?L |- _ =>
        exploit (IH ν nIN);
        first [eapply Link_floc; eauto | idtac]
      end.
      intros (v1' & EVAL1 & LINK1).
      eapply Link_lc in LINK as Σ1. inv Σ1. inv VAL.
      eapply Eval_lc in EVAL1 as V1; try solve [econstructor; eauto].
      assert (forall ℓ (FREE : ~ In ℓ (floc_nv σ1)),
        open_loc_vl 0 ℓ (close_vl 0 ν v1') = subst_loc_vl ℓ ν v1') as RR.
      { intros.
        assert (close_open_loc_eq_vl _ _ _ v1') by eapply close_open_loc_eq. rw.
        assert (open_loc_lc_vl _ _ _ v1' V1) by (eapply open_loc_lc; eauto). rw.
        reflexivity. }
      assert (forall ℓ (FREE : ~ In ℓ (floc_nv σ1)),
        Eval (nv_floc x ℓ σ1) t1 (open_loc_vl 0 ℓ (close_vl 0 ν v1'))).
      { intros. apply Eval_subst_loc with (ν := ℓ) (ℓ' := ν) in EVAL1.
        ss. rewrite eqb_refl in EVAL1.
        assert (RR' : subst_loc_fresh_nv _ _ _ σ1) by eapply subst_loc_fresh.
        rewrite RR' in EVAL1; eauto.
        rewrite RR; eauto. }
      assert (forall ℓ (FREE : ~ In ℓ (floc_nv σ1)),
        σ0 ⋊ open_loc_vl 0 ℓ (close_vl 0 ν v1') ∋ open_loc_vl 0 ℓ v1).
      { intros. apply Link_subst_loc with (ν := ℓ) (ℓ' := ν) in LINK1; eauto.
        assert (open_loc_subst_loc_vl _ _ _ v1) as RR' by eapply open_loc_subst_loc.
        simpl in LINK1. rewrite RR' in LINK1. clear RR'.
        rewrite eqb_refl in LINK1.
        rewrite RR; eauto.
        assert (subst_loc_fresh_nv _ _ _ σ0) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. clear RR'.
        assert (subst_loc_fresh_vl _ _ _ v1) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. }
      assert (σ0 ⋊ wvl_recv (close_vl 0 ν v1') ∋ wvl_recv v1).
      { econstructor; eauto. }
      exploit (IHEVAL (nv_bval x (wvl_recv (close_vl 0 ν v1')) σ1)).
      + econstructor; eauto.
      + intros (v2' & EVAL2 & LINK2).
        destruct v2'; try solve [inv LINK2].
        * exists (nv_bval x (wvl_recv (close_vl 0 ν v1')) (nv_ev E)).
          split. eapply Ev_bindevent; eauto.
          econstructor; eauto.
          econstructor; eauto.
        * exists (nv_bval x (wvl_recv (close_vl 0 ν v1')) σ3).
          split. econstructor; eauto.
          econstructor; eauto.
    - gensym_tac (L ++ floc_nv σ0 ++ floc_nv σ1 ++ floc_vl v1) ν.
      match goal with
      | IH : forall _, ~ In _ ?L -> _, ν : loc, nIN : ~ In ν ?L |- _ =>
        exploit (IH ν nIN);
        first [eapply Link_floc; eauto | idtac]
      end.
      intros (v1' & EVAL1 & LINK1).
      eapply Link_lc in LINK as Σ1. inv Σ1. inv VAL.
      eapply Eval_lc in EVAL1 as V1; try solve [econstructor; eauto].
      assert (forall ℓ (FREE : ~ In ℓ (floc_nv σ1)),
        open_loc_vl 0 ℓ (close_vl 0 ν v1') = subst_loc_vl ℓ ν v1') as RR.
      { intros.
        assert (close_open_loc_eq_vl _ _ _ v1') by eapply close_open_loc_eq. rw.
        assert (open_loc_lc_vl _ _ _ v1' V1) by (eapply open_loc_lc; eauto). rw.
        reflexivity. }
      assert (forall ℓ (FREE : ~ In ℓ (floc_nv σ1)),
        Eval (nv_floc x ℓ σ1) t1 (open_loc_vl 0 ℓ (close_vl 0 ν v1'))).
      { intros. apply Eval_subst_loc with (ν := ℓ) (ℓ' := ν) in EVAL1.
        ss. rewrite eqb_refl in EVAL1.
        assert (RR' : subst_loc_fresh_nv _ _ _ σ1) by eapply subst_loc_fresh.
        rewrite RR' in EVAL1; eauto.
        rewrite RR; eauto. }
      assert (forall ℓ (FREE : ~ In ℓ (floc_nv σ1)),
        σ0 ⋊ open_loc_vl 0 ℓ (close_vl 0 ν v1') ∋ open_loc_vl 0 ℓ v1).
      { intros. apply Link_subst_loc with (ν := ℓ) (ℓ' := ν) in LINK1; eauto.
        assert (open_loc_subst_loc_vl _ _ _ v1) as RR' by eapply open_loc_subst_loc.
        simpl in LINK1. rewrite RR' in LINK1. clear RR'.
        rewrite eqb_refl in LINK1.
        rewrite RR; eauto.
        assert (subst_loc_fresh_nv _ _ _ σ0) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. clear RR'.
        assert (subst_loc_fresh_vl _ _ _ v1) as RR' by eapply subst_loc_fresh.
        rewrite RR' in LINK1; eauto. }
      assert (σ0 ⋊ wvl_recv (close_vl 0 ν v1') ∋ wvl_recv v1).
      { econstructor; eauto. }
      exploit (IHEVAL (nv_bval x (wvl_recv (close_vl 0 ν v1')) σ1)).
      + econstructor; eauto.
      + intros (v2' & EVAL2 & LINK2).
        destruct v2'; try solve [inv LINK2].
        exists (nv_bval x (wvl_recv (close_vl 0 ν v1')) (nv_ev E)).
        split. eapply Ev_bindevent; eauto.
        econstructor; eauto.
        eapply Link_holeEvent.
        assumption.
  Qed.

  Theorem advance `{Name loc} `{Eq var}
    (σ0 σ' : nv var loc _) (Σ0 : env σ0) v' t (EVAL : eval σ' t v') :
    forall (σ : nv var loc _) (LINK : link σ0 σ σ'),
      exists v, eval σ t v /\ (link σ0 v v').
  Proof.
    intros.
    erewrite equiv_semantics in EVAL; eauto.
    erewrite equiv_link in LINK; eauto.
    eapply advance_Eval in EVAL; eauto.
    destruct EVAL as (v & EVAL & LINK').
    erewrite <- equiv_semantics in EVAL; eauto.
    erewrite <- equiv_link in LINK'; eauto.
    eapply Link_lc in LINK. inv LINK. inv VAL. auto.
    eapply linked_lc_wvl in LINK; eauto. inv LINK. inv VAL. auto.
  Qed.
End Advance.

