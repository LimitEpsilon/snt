From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import LinkDefs.

Section LinkFacts.
  Context {var lbl loc : Type}.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Ltac link_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | _ => instantiate (1 := [])
    end.

  Lemma link_lc `{Eq var} `{Eq lbl} `{Eq loc} (σ0 : nv var (@ltm var lbl) loc _) (w : wvl var _ loc _) :
    forall w' (LINK : link σ0 w w'), wvalue w.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    link_lc_tac; ii.
    all: match goal with
    | RR : _ = open_loc_vl 0 ?ν ?v |- value (open_loc_vl 0 ?ℓ ?v) =>
      assert (value (open_loc_vl 0 ν v)) by (rewrite <- RR; constructor; auto);
      replace (open_loc_vl 0 ℓ v) with (subst_loc_vl ℓ ν (open_loc_vl 0 ν v))
    end.
    all: try match goal with
    | V : value ?v |- value (subst_loc_vl _ _ ?v) =>
      assert (subst_loc_lc_vl v V) by eapply subst_loc_lc; auto
    | |- context [subst_loc_vl ?ℓ ?ν (open_loc_vl 0 ?ν ?v)] =>
      assert (open_loc_subst_loc_vl v) by eapply open_loc_subst_loc;
      rw; rewrite eqb_refl;
      f_equal; eapply subst_loc_fresh; auto
    end.
  Qed.

  Ltac linked_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | _ => instantiate (1 := [])
    end.

  Lemma linked_lc `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) (w : wvl var _ loc _) :
    forall w' (LINK : link σ0 w w'), wvalue w'.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    linked_lc_tac; ii.
    - eapply read_env_lc in READ; auto.
      destruct w; inv READ; ss.
      assert (subst_intro_vl v) by eapply subst_intro.
      gensym_tac (L ++ floc_vl v) ℓ.
      rw; eauto.
      eapply subst_wvl_lc; eauto.
      econstructor; eauto.
    - eapply eval_lc in EVAL; eauto.
      repeat econstructor; eauto.
    - assert (close_open_loc_eq_vl v') by eapply close_open_loc_eq.
      rw.
      assert (open_loc_lc_vl v' VAL) by (eapply open_loc_lc; eauto).
      rw.
      eapply subst_loc_lc; auto.
  Qed.

  Lemma map_unroll {lang} `{Eq var} `{Eq lbl} `{Eq loc} φ (w : wvl var (@ltm var lbl) loc lang) :
    unroll (map_wvl φ w) = map_vl φ (unroll w).
  Proof.
    destruct w; ss.
    assert (map_open_wvl_vl v) by eapply map_open_wvl.
    rw; ss.
  Qed.

  Lemma subst_loc_unroll {lang} `{Eq var} `{Eq lbl} `{Eq loc}
    ℓ ν (w : wvl var (@ltm var lbl) loc lang) :
    unroll (subst_loc_wvl ν ℓ w) = subst_loc_vl ν ℓ (unroll w).
  Proof.
    destruct w; ss.
    match goal with
    | |- context [subst_loc_vl _ _ (open_wvl_vl _ _ ?v)] =>
      assert (open_wvl_subst_loc_vl v)
        by (eapply open_wvl_subst_loc; eauto);
      rw; ss
    end.
  Qed.

  Lemma subst_wvl_unroll {lang} `{Eq var} `{Eq lbl} `{Name loc}
    ℓ (u w : wvl var (@ltm var lbl) loc lang) (U : wvalue u) :
    unroll (subst_wvl_wvl u ℓ w) = subst_wvl_vl u ℓ (unroll w).
  Proof.
    destruct w; ss.
    match goal with
    | |- context [subst_wvl_vl _ _ (open_wvl_vl _ _ ?v)] =>
      assert (open_wvl_subst_wvl_vl v)
        by (eapply open_wvl_subst_wvl; eauto);
      rw; ss
    end.
  Qed.

  Lemma unroll_flloc {lang} ℓ (w : wvl var (@ltm var lbl) loc lang) :
    In ℓ (flloc_wvl w) <-> In ℓ (flloc_vl (unroll w)).
  Proof.
    split; intro IN; destruct w; ss.
    - eapply open_wvl_inc_flloc. auto.
    - eapply open_wvl_flloc in IN. des; auto.
  Qed.

  Lemma link_flloc_dec `{Eq var} `{Eq lbl} `{Eq loc}
    (σ0 : nv var (@ltm var lbl) loc _) (w w' : wvl var _ loc _) (LINK : link σ0 w w') :
    forall ℓ (IN : In ℓ (flloc_wvl w')), In ℓ (flloc_nv σ0) \/ In ℓ (flloc_wvl w).
  Proof.
    induction LINK; ii; ss;
    repeat rewrite in_app_iff in *; eauto.
    - rewrite <- unroll_flloc in IN.
      eapply read_env_flloc in READ; eauto.
    - eapply eval_flloc_dec in EVAL; eauto; ss.
      rewrite in_app_iff in EVAL; des.
      + exploit IHLINK2; ii; des; eauto.
      + exploit IHLINK1; ii; des; eauto.
    - des.
      exploit IHLINK1; ii; des; eauto.
      exploit IHLINK2; ii; des; eauto.
    - des; clarify. auto.
      exploit IHLINK; ii; des; eauto.
    - des.
      exploit IHLINK1; ii; des; eauto.
      exploit IHLINK2; ii; des; eauto.
    - eapply close_flloc in IN. destruct IN as [nEQ IN].
      exploit IHLINK; ii; des; eauto.
      match goal with
      | H : In ?ℓ (flloc_vl (open_loc_vl _ _ _)) |- _ =>
        eapply open_loc_flloc in H; des; clarify
      end.
      eauto.
    - destruct E'; simpl in *; auto.
  Qed.

  Lemma link_map `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (w w' : wvl var _ loc _) (LINK : link σ0 w w') :
    forall φ (INJ : oto φ),
      link (map_nv φ σ0) (map_wvl φ w) (map_wvl φ w').
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - rewrite <- map_unroll.
      apply read_env_map with (φ := φ) in READ.
      econstructor; eauto.
    - specialize (IHLINK1 φ INJ).
      specialize (IHLINK2 φ INJ).
      eapply link_CallEval; eauto.
      eapply eval_map with (φ := φ) in EVAL; eauto.
    - des_goal; ss; econstructor; eauto.
    - assert (map_close_vl v') by (eapply map_close; eauto).
      rw; eauto.
      econstructor; eauto;
      match goal with
      | |- ~ In _ _ =>
        intro IN; eapply map_floc in IN; eauto
      | _ =>
        specialize (IHLINK φ INJ);
        assert (map_open_loc_vl v) as RR by (eapply map_open_loc; eauto);
        rewrite RR in *; auto
      end.
    - rewrite predE_map. econstructor; auto.
  Qed.
End LinkFacts.

