From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import EquivSemantics.
From With_events Require Import LinkDefs.
From With_events Require Import LinkFacts.
From With_events Require Import EquivLink.
From With_events Require Import AdvanceAux.

Section Advance.
  Context {var lbl loc : Type}.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Theorem advance `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 σ' : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) v' t (EVAL : eval σ' t v') :
    forall (σ : nv var (@ltm var lbl) loc _) (LINK : link σ0 σ σ'),
      exists v, eval σ t v /\ link σ0 v v'.
  Proof.
    intros.
    erewrite equiv_semantics in EVAL; eauto.
    erewrite equiv_link in LINK; eauto.
    eapply advance_aux in EVAL; eauto.
    destruct EVAL as (v & EVAL & LINK').
    erewrite <- equiv_semantics in EVAL; eauto.
    erewrite <- equiv_link in LINK'; eauto.
    eapply link_lc' in LINK. inv LINK. inv VAL. auto.
    eapply linked_lc in LINK; eauto. inv LINK. inv VAL. auto.
  Qed.
End Advance.

