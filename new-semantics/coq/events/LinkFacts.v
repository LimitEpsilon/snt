From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import LinkDefs.

Section LinkFacts.
  Variable var : Type.
  Variable loc : Type.

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

  Lemma link_lc `{Eq loc} `{Eq var} (σ0 : nv var loc _) (w : wvl var loc _) :
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
      assert (subst_loc_lc_vl _ _ _ v V) by eapply subst_loc_lc; auto
    | |- context [subst_loc_vl ?ℓ ?ν (open_loc_vl 0 ?ν ?v)] =>
      assert (open_loc_subst_loc_vl _ _ _ v) by eapply open_loc_subst_loc;
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

  Lemma linked_lc_wvl `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (Σ0 : env σ0) (w : wvl var loc _) :
    forall w' (LINK : link σ0 w w'), wvalue w'.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    linked_lc_tac; ii.
    - eapply read_env_lc in READ; auto.
      destruct w; inv READ; ss.
      assert (subst_intro_vl _ _ _ v) by eapply subst_intro.
      gensym_tac (L ++ floc_vl v) ℓ.
      rw; eauto.
      eapply subst_wvl_lc; eauto.
      econstructor; eauto.
    - eapply eval_lc in EVAL; eauto.
      repeat econstructor; eauto.
    - assert (close_open_loc_eq_vl _ _ _ v') by eapply close_open_loc_eq.
      rw.
      assert (open_loc_lc_vl _ _ _ v' VAL) by (eapply open_loc_lc; eauto).
      rw.
      eapply subst_loc_lc; auto.
  Qed.

  Lemma map_unroll {lang} `{Eq loc} φ (w : wvl var loc lang) :
    unroll (map_wvl φ w) = map_vl φ (unroll w).
  Proof.
    destruct w; ss.
    assert (map_open_wvl_vl _ _ _ v) by eapply map_open_wvl.
    rw; ss.
  Qed.

  Lemma subst_loc_unroll {lang} `{Eq loc}
    ℓ ν (w : wvl var loc lang) :
    unroll (subst_loc_wvl ν ℓ w) = subst_loc_vl ν ℓ (unroll w).
  Proof.
    destruct w; ss.
    match goal with
    | |- context [subst_loc_vl _ _ (open_wvl_vl _ _ ?v)] =>
      assert (open_wvl_subst_loc_vl _ _ _ v)
        by (eapply open_wvl_subst_loc; eauto);
      rw; ss
    end.
  Qed.

  Lemma subst_wvl_unroll {lang} `{Name loc}
    ℓ (u w : wvl var loc lang) (U : wvalue u) :
    unroll (subst_wvl_wvl u ℓ w) = subst_wvl_vl u ℓ (unroll w).
  Proof.
    destruct w; ss.
    match goal with
    | |- context [subst_wvl_vl _ _ (open_wvl_vl _ _ ?v)] =>
      assert (open_wvl_subst_wvl_vl _ _ _ v)
        by (eapply open_wvl_subst_wvl; eauto);
      rw; ss
    end.
  Qed.

  Lemma unroll_floc {lang} ℓ (w : wvl var loc lang) :
    In ℓ (floc_wvl w) <-> In ℓ (floc_vl (unroll w)).
  Proof.
    split; intro IN; destruct w; ss.
    - eapply open_wvl_inc_floc. auto.
    - eapply open_wvl_floc in IN. ss; des; auto.
  Qed.

  Lemma link_map `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (w w' : wvl var loc _) (LINK : link σ0 w w') :
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
    - assert (map_close_vl _ _ _ v') by (eapply map_close; eauto).
      rw; eauto.
      econstructor; eauto;
      match goal with
      | |- ~ In _ _ =>
        intro IN; eapply map_floc in IN; eauto
      | _ =>
        specialize (IHLINK φ INJ);
        assert (map_open_loc_vl _ _ _ v) as RR by (eapply map_open_loc; eauto);
        rewrite RR in *; auto
      end.
  Qed.
End LinkFacts.

