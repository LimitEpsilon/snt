From Basics Require Import Basics.
From Without_events Require Import Defs.
From Without_events Require Import SubstFacts.

Section SimFacts.
  Variable var : Type.
  Variable loc : Type.
  Variable lang : Type.

  Ltac sim_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | L : list loc, H : forall _, ~ In _ _ -> _ |- _ =>
      instantiate (1 := L); ii; exploit H; eauto; ii
    end.

  Lemma sim_lc_wvl `{Eq loc} (w : wvl var loc lang) :
    forall f v' m (SIM : sim w f v' m),
      wvalue w.
  Proof.
    ii. induction SIM;
    repeat econstructor;
    sim_lc_tac.
  Qed.

  Lemma sim_lc_nv `{Eq loc} :
    forall (σ : nv var loc lang) f v' m
      (SIM : sim (wvl_v (vl_exp σ)) f v' m),
    env σ.
  Proof. ii. eapply sim_lc_wvl in SIM. sim_lc_tac. Qed.

  Lemma sim_lc_vl `{Eq loc} :
    forall (v : vl var loc lang) f v' m
      (SIM : sim (wvl_v v) f v' m),
    value v.
  Proof. ii. eapply sim_lc_wvl in SIM. sim_lc_tac. Qed.

  Lemma sim_floc_free `{Name loc} (w : wvl var loc lang) f v' m (SIM : sim w f v' m) :
    forall ℓ (FREEw : In ℓ (floc_wvl w)) (FREEf : f ℓ = None),
    m ℓ = None.
  Proof.
    induction SIM; ii; ss; des; clarify; eauto.
    - rewrite in_app_iff in *; des; eauto.
    - gensym_tac (L ++ floc_vl v) ν.
      exploit SIM; eauto. ii.
      match goal with | H : forall _, ~ In _ _ -> _ |- _=> exploit H; eauto end.
      apply open_inc_floc; eauto.
      unfold update. des_goal; eqb2eq loc; clarify.
  Qed.

  (* safe for future worlds that preserve free locations *)
  Lemma sim_m_ext `{Eq loc} (w : wvl var loc lang) f v' m (SIM : sim w f v' m) :
    forall m'
      (EXT : forall ℓ, m ℓ <> None -> m' ℓ = m ℓ)
      (AVOID : forall ℓ (FREEw : In ℓ (floc_wvl w)) (FREEf : f ℓ = None), m' ℓ = None),
    sim w f v' m'.
  Proof.
    induction SIM; ii; ss.
    - econstructor.
    - econstructor; eauto.
      ii. exploit EXT; eauto. rw. eauto.
    - eapply sim_floc; eauto.
    - econstructor.
      instantiate (1 := v').
      erewrite EXT; ii; clarify.
      eapply IHSIM1; eauto.
      ii. apply AVOID; eauto. rewrite in_app_iff; eauto.
      eapply IHSIM2; eauto.
      ii. apply AVOID; eauto. rewrite in_app_iff; eauto.
    - econstructor; eauto.
      instantiate (1 := ℓ').
      rewrite EXT; ii; clarify.
      instantiate (1 := L).
      ii.
      match goal with | H : forall _, ~ In _ _ -> _ |- _=> exploit H; eauto end.
      ii. eapply open_floc in FREEw.
      des; clarify.
      unfold update in FREEf. rewrite eqb_refl in FREEf. clarify.
      unfold update in FREEf. des_hyp; eqb2eq loc; clarify.
      apply AVOID; eauto.
    - econstructor; eauto.
  Qed.

  Lemma sim_f_ext `{Eq loc} (w : wvl var loc lang) f v' m (SIM : sim w f v' m) :
    forall f'
      (EXT : forall ℓ (DOM : In ℓ (floc_wvl w)), f ℓ = f' ℓ),
    sim w f' v' m.
  Proof.
    induction SIM; ii.
    - econstructor.
    - econstructor; eauto.
      erewrite <- EXT; eauto. s. eauto.
      eapply IHSIM.
      ii. apply EXT; ss; eauto.
    - eapply sim_floc; eauto.
      erewrite <- EXT; eauto. s. eauto.
      eapply IHSIM.
      ii. apply EXT; ss; eauto.
    - econstructor; eauto.
      eapply IHSIM1. ii. apply EXT; ss; rewrite in_app_iff; eauto.
      eapply IHSIM2. ii. apply EXT; ss; rewrite in_app_iff; eauto.
    - econstructor; eauto.
      instantiate (1 := L ++ floc_vl v). ss.
      ii.
      match goal with | H : forall _, ~ In _ _ -> _ |- _=> eapply H end.
      split_nIn; auto.
      ii. apply open_floc in DOM.
      des; clarify; unfold update;
      try solve [rewrite eqb_refl; eauto | des_goal; eqb2eq loc; auto].
    - econstructor; eauto.
  Qed.

  Lemma extend_m_floc `{Eq loc} (w : wvl var loc lang) f v' m (SIM : sim w f v' m) :
    forall ℓ u' (FREEm : m ℓ = None) (FREEf : f ℓ = None),
      sim w (ℓ !-> ℓ ; f) v' (ℓ !-> u' ; m).
  Proof.
    induction SIM; ii; ss.
    - econstructor.
    - econstructor.
      all: solve [unfold update; des_goal; eqb2eq loc; clarify | eauto].
    - match goal with ℓ : loc, ν : loc |- _ => case_eqb ℓ ν end.
      + eapply sim_bloc.
        all: solve [unfold update; rewrite eqb_refl; ii; clarify | eauto].
      + eapply sim_floc.
        all: solve [unfold update; des_goal; eqb2eq loc; clarify | eauto].
    - econstructor.
      instantiate (1 := v').
      unfold update. des_goal; eqb2eq loc; clarify.
      all:eauto.
    - econstructor. instantiate (1 := ℓ').
      unfold update. des_goal; eqb2eq loc; clarify.
      instantiate (1 := ℓ :: L).
      ii. split_nIn.
      match goal with | H : forall _, ~ In _ _ -> _ |- _=> exploit H; eauto end.
      unfold update. des_goal; eqb2eq loc; clarify.
      instantiate (1 := u').
      ii.
      eapply sim_f_ext; eauto.
      ii. erewrite update_comm; eauto.
    - econstructor; eauto.
  Qed.

  Lemma reduce_f_bloc `{Name loc} (w : wvl var loc lang) f v' m (SIM : sim w f v' m) :
    forall ℓ ℓ' u u'
      (BOUNDf : f ℓ = Some ℓ')
      (BOUNDm : m ℓ' = Some u')
      (SIMu : sim u (f !! ℓ) u' m),
    sim (subst_wvl_wvl u ℓ w) (f !! ℓ) v' m.
  Proof.
    induction SIM; ii; ss.
    - econstructor.
    - des_goal; eqb2eq loc; clarify.
      + econstructor; eauto.
      + econstructor; eauto.
        unfold remove. des_goal; eqb2eq loc; clarify.
    - des_goal; eqb2eq loc; clarify.
      eapply sim_floc; eauto.
      unfold remove. des_goal; eqb2eq loc; clarify.
    - econstructor; eauto.
    - econstructor; eauto.
      instantiate (1 := ℓ :: L ++ floc_wvl u).
      ii. split_nIn.
      match goal with 
      | H : forall _, ~ In _ ?L -> _, FREE : ?ℓ <> ?ν, FREE' : ~ In ?ν ?L |- _=>
        exploit (H ν FREE' ℓ _ u); eauto 
      end.
      unfold update. des_goal; eqb2eq loc; clarify.
      eapply sim_f_ext; eauto.
      ii. unfold update, remove.
      repeat des_goal; eqb2eq loc; clarify.
      assert (open_loc_subst_wvl_vl _ _ _ v) as RR.
      eapply open_loc_subst_wvl; eauto.
      rewrite RR; eauto.
      ii. eapply sim_f_ext; eauto.
      ii. apply remove_update_assoc; eauto.
      eapply sim_lc_wvl; eauto.
    - econstructor; eauto.
  Qed.

  Lemma sim_loc_subst `{Eq loc} (w : wvl var loc lang) f v' m (SIM : sim w f v' m) :
    forall ℓ ν
      (FRESH : ~ In ν (floc_wvl w))
      (DOMf : f ℓ <> None),
    sim (subst_loc_wvl ν ℓ w) (swap f ν ℓ) v' m.
  Proof.
    induction SIM; ii; ss;
    try solve [econstructor; eauto].
    - split_nIn. des_goal; eqb2eq loc; clarify.
      + econstructor; eauto. unfold swap. rewrite eqb_refl. auto.
      + econstructor; eauto. unfold swap.
        repeat (des_goal; eqb2eq loc; clarify).
    - split_nIn. des_goal; eqb2eq loc; clarify.
      eapply sim_floc; eauto. unfold swap.
      repeat (des_goal; eqb2eq loc; clarify).
    - rewrite in_app_iff in FRESH. split_nIn.
      econstructor; eauto.
    - econstructor; eauto.
      instantiate (1 := ℓ :: ν :: L ++ floc_vl v).
      ii. split_nIn.
      match goal with
      | |- context [open_loc_vl ?i ?ℓ' (subst_loc_vl ?ν ?ℓ ?v)] =>
        let RR := fresh "RR" in
        assert (open_loc_subst_loc_vl _ _ _ v) as RR by (eapply open_loc_subst_loc; eauto);
        specialize (RR i ℓ ℓ' ν)
      end.
      des_ifs; eqb2eq loc; clarify. rrw.
      match goal with 
      | H : forall _, ~ In _ ?L -> _, DOM : _ ?ℓ <> None,
        FREE : ~ In ?ν ?L, _ : ?ℓ' <> ?ν |- _=>
        lazymatch ℓ' with ℓ => fail | _ => idtac end;
        exploit (H ν FREE ℓ ℓ'); eauto; ii
      end.
      match goal with
      | H : In _ (floc_vl (open_loc_vl _ _ _)) |- _ => eapply open_floc in H
      end.
      des; clarify.
      unfold update in *. des_ifs.
      eapply sim_f_ext; eauto.
      ii. eapply swap_update_assoc; eauto.
  Qed.
End SimFacts.
