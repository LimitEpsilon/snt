From Coq Require Import Utf8 Lia Eqdep.
From Paco Require Import paco.

Set Primitive Projections.
Unset Elimination Schemes.

#[local] Lemma mp : forall P Q, P -> (P -> Q) -> Q. intuition. Qed.

Ltac exploit H := eapply mp; [eapply H |].
(* uses eq_rect_eq *)
Ltac clear_sig :=
  repeat match goal with
  | H : existT _ ?x _ = existT _ ?x _ |- _ =>
    apply inj_pair2 in H; subst
  end.

Variant CTreeF {E : Type → Type} {R : Type} {CTree : Type} :=
| Ret (v : R)
| Vis {A} (e : E A) (k : A → CTree)
| Zero
| Choice (k : nat → CTree)
.

Arguments CTreeF : clear implicits.

CoInductive CTree {E : Type → Type} {R : Type} : Type :=
  mkCTree { obs_ctree : CTreeF E R CTree }
.

Arguments CTree : clear implicits.

Definition CTree' E R := CTreeF E R (CTree E R).

(* order between extended natural numbers, with None meaning ∞ *)
Definition olt (x y : option nat) :=
  match x, y with
  | Some m, Some n => m < n
  | None, _ => False
  | _,None => True
  end.

Infix "≺" := olt (at level 40).

Definition ole x y := olt x y ∨ x = y.

Infix "≼" := ole (at level 40).

(* ≺ is a strict total order *)
Lemma olt_irreflexive x : olt x x → False.
Proof. destruct x; simpl; lia. Qed.

Lemma olt_assymmetric x y : olt x y → olt y x → False.
Proof. destruct x, y; simpl; lia. Qed.

Lemma olt_transitive x y z : olt x y → olt y z → olt x z.
Proof. destruct x, y, z; simpl; lia. Qed.

Lemma olt_connected x y : (x ≠ y) → olt x y ∨ olt y x.
Proof.
  destruct x as [x|], y as [y|]; simpl; eauto.
  destruct (PeanoNat.Nat.eq_dec x y); subst; [congruence|lia].
Qed.

Lemma olt_wf : well_founded olt.
Proof.
  assert (∀ m, Acc olt (Some m)).
  { induction m using (well_founded_induction Wf_nat.lt_wf).
    constructor. destruct y; auto.
    destruct 1. }
  repeat intro.
  destruct a as [n|]; eauto.
  constructor; destruct y; eauto.
  destruct 1.
Qed.

(* ≼ is a total order *)
Lemma ole_reflexive x : ole x x.
Proof. right. auto. Qed.

Lemma ole_transitive x y z : ole x y → ole y z → ole x z.
Proof.
  unfold ole. intuition auto; subst; eauto.
  left. eapply olt_transitive; eauto.
Qed.

Lemma ole_antisymmetric x y : ole x y → ole y x → x = y.
Proof.
  unfold ole. intuition auto; subst; eauto.
  exfalso. eapply olt_assymmetric; eauto.
Qed.

Lemma ole_connected x y : ole x y ∨ ole y x.
Proof.
  unfold ole.
  destruct x as [x|], y as [y|]; simpl; eauto.
  destruct (PeanoNat.Nat.eq_dec x y); subst; eauto.
  lia.
Qed.

Lemma ole_or_olt x y : ole x y ∨ olt y x.
Proof.
  unfold ole, olt.
  destruct x as [x|], y as [y|]; simpl; eauto.
  destruct (PeanoNat.Nat.eq_dec x y); subst; eauto.
  lia.
Qed.

Lemma ole_top x : ole x None.
Proof. destruct x; cbv; eauto. Qed.

(* from FreeSim (Stuttering for Free) *)
(* infinite silent steps should be equivalent only to infinite silent steps *)
Inductive SimF {R1 R2 E r sim}
  : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop :=
| refine_prog p1 p2 t1 t2 p1' p2'
  (* only rule that strictly decrements the progress indices*)
  (LT1 : p1' ≺ p1) (LT2 : p2' ≺ p2)
  (SIM : sim p1' p2' t1 t2)
: SimF p1 p2 t1 t2
| refine_ret p1 p2 x y
  (RET : r x y : Prop)
: SimF p1 p2 (Ret x) (Ret y)
| refine_vis p1 p2 p1' p2' {A} (e : E A) k1 k2
  (CONT : ∀ a, sim p1' p2' (obs_ctree (k1 a)) (obs_ctree (k2 a)))
: SimF p1 p2 (Vis e k1) (Vis e k2)
| refine_zero p1 p2 t2
: SimF p1 p2 Zero t2
| refine_choiceL p1 p2 p1' t2 k
  (CHOICE : ∀ c, SimF p1' p2 (obs_ctree (k c)) t2)
: SimF p1 p2 (Choice k) t2
| refine_choiceR p1 p2 p2' t1 k
  c (CHOICE : SimF p1 p2' t1 (obs_ctree (k c)))
: SimF p1 p2 t1 (Choice k)
.

Arguments SimF {_ _ _} _ _.

Section IND.
  Context {R1 R2 E} (r : R1 → R2 → Prop) (sim : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop).
  Context (P : ∀ p1 p2 t1 t2, SimF r sim p1 p2 t1 t2 → Prop).
  Context (Pprog : ∀ p1 p2 t1 t2 p1' p2' LT1 LT2 SIM, P _ _ _ _ (refine_prog p1 p2 t1 t2 p1' p2' LT1 LT2 SIM))
          (Pret : ∀ p1 p2 x y RET, P _ _ _ _ (refine_ret p1 p2 x y RET))
          (Pvis : ∀ p1 p2 p1' p2' A (e : E A) k1 k2 CONT, P _ _ _ _ (refine_vis p1 p2 p1' p2' e k1 k2 CONT))
          (Pzero : ∀ p1 p2 t2, P _ _ _ _ (refine_zero p1 p2 t2))
          (PL : ∀ p1 p2 p1' t2 k CHOICE (IHk : ∀ c, P _ _ _ _ (CHOICE c)), P _ _ _ _ (refine_choiceL p1 p2 p1' t2 k CHOICE))
          (PR : ∀ p1 p2 p2' t1 k c CHOICE (IHk : P _ _ _ _ CHOICE), P _ _ _ _ (refine_choiceR p1 p2 p2' t1 k c CHOICE)).
  Fixpoint SimF_ind p1 p2 t1 t2 pf : P p1 p2 t1 t2 pf.
  Proof.
    destruct pf.
    - apply Pprog.
    - apply Pret.
    - apply Pvis.
    - apply Pzero.
    - apply PL. intros. apply SimF_ind.
    - apply PR. intros. apply SimF_ind.
  Qed.
End IND.

Definition BisimF {R1 R2 E} (φ : R1 → R2 → Prop) sim p1 p2 t1 t2 :=
  SimF (E := E) φ sim p1 p2 t1 t2 ∧
  SimF
    (fun r1 r2 => φ r2 r1)
    (fun p1 p2 t1 t2 => sim p2 p1 t2 t1)
    p2 p1 t2 t1
.

(* divergence predicate *)
Variant divF {E R sim} : CTree' E R → Prop :=
| div_intro k c (SIM : sim (obs_ctree (k c)) : Prop)
: divF (Choice k)
.

Arguments divF {_ _} _ _.

Lemma divF_monotone {E R} : monotone1 (@divF E R).
Proof. repeat intro. destruct IN. econstructor; eauto. Qed.

Hint Resolve divF_monotone : paco.

Lemma SimF_monotone R1 R2 E r : monotone4 (@SimF R1 R2 E r).
Proof.
  repeat intro. revert r' LE. induction IN; intros.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
Qed.

Hint Resolve SimF_monotone : paco.

Lemma BisimF_monotone R1 R2 E φ : monotone4 (@BisimF R1 R2 E φ).
Proof.
  repeat intro.
  destruct IN as (IN & IN').
  split; eapply SimF_monotone; eauto.
Qed.

Hint Resolve BisimF_monotone : paco.

Definition Sim {R1 R2 E} r := paco4 (@SimF R1 R2 E r) bot4.

Definition Bisim {R1 R2 E} r := paco4 (@BisimF R1 R2 E r) bot4.

Definition div {E R} := paco1 (@divF E R) bot1.

Lemma Sim_postfix {R1 R2 E} (φ : R1 → R2 → Prop) :
  Sim (E := E) φ <4= SimF φ (Sim φ).
Proof.
  repeat intro. punfold PR.
  eapply SimF_monotone; eauto.
  intros. pclearbot. auto.
Qed.

Lemma Bisim_postfix {R1 R2 E} (φ : R1 → R2 → Prop) :
  Bisim (E := E) φ <4= SimF φ (Bisim φ).
Proof.
  repeat intro.
  punfold PR. destruct PR.
  eapply SimF_monotone; eauto.
  intros. pclearbot. auto.
Qed.

Lemma Bisim_postfix_flipped {R1 R2 E} (φ : R1 → R2 → Prop) :
  (fun p1 p2 t1 t2 => Bisim (E := E) φ p2 p1 t2 t1) <4=
  SimF (fun r1 r2 => φ r2 r1) (fun p1 p2 t1 t2 => Bisim φ p2 p1 t2 t1).
Proof.
  repeat intro.
  punfold PR. destruct PR.
  eapply SimF_monotone; eauto.
  intros. pclearbot. auto.
Qed.

Lemma BisimF_postfix {R1 R2 E} (φ : R1 → R2 → Prop) :
  Bisim (E := E) φ <4= BisimF φ (Bisim φ).
Proof.
  repeat intro; split.
  - apply Bisim_postfix; eauto.
  - apply Bisim_postfix_flipped; eauto.
Qed.

Definition comp2 {R1 R2 R3 : Type}
  (r12 : R1 → R2 → Prop) (r23 : R2 → R3 → Prop) v1 v3 :=
  ∃ v2, r12 v1 v2 ∧ r23 v2 v3
.

Definition comp4 {E R1 R2 R3}
  (sim12 : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop)
  (sim23 : option nat → option nat → CTree' E R2 → CTree' E R3 → Prop)
  p11 p22 t1 t3 :=
  ∃ p12 p21 t2, sim12 p11 p12 t1 t2 ∧ sim23 p21 p22 t2 t3
.

Lemma SimF_index_mono {R1 R2 E} φ (sim : _ → _ → _ → _ → Prop) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : SimF φ sim p1 p2 t1 t2)
    p1' p2' (LE1 : p1 ≼ p1') (LE2 : p2 ≼ p2'),
    SimF φ sim p1' p2' t1 t2.
Proof.
  do 4 intro. induction 1.
  - intros p1'' p2'' ? ?.
    econstructor 1; eauto.
    destruct LE1; subst; eauto. eapply olt_transitive; eauto.
    destruct LE2; subst; eauto. eapply olt_transitive; eauto.
  - intros. econstructor 2; eauto.
  - intros. econstructor 3; eauto.
  - intros. econstructor 4; eauto. 
  - intros. econstructor 5; eauto.
    intros. eapply IHk; eauto. right; auto.
  - intros. econstructor 6; eauto.
    intros. eapply IHREFINE; eauto. right; auto.
Qed.

Lemma SimF_contR {R1 R2 E φ sim} (POSTFIX : sim <4= SimF φ sim) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2' : CTree' E R2)
    (* if t1 refines t2', *)
    (REFINE : SimF φ sim p1 p2 t1 t2')
    (* for any t2 that may continue as t2', *)
    t2 k2 (OBS : t2 = Choice k2) c2 (BR : t2' = obs_ctree (k2 c2))
    (* t1 must refine t2 *)
    p1' p2', SimF φ sim p1' p2' t1 t2.
Proof.
  induction p1 using (well_founded_induction olt_wf).
  rename H into IHp1.
  do 4 intro. revert IHp1.
  induction REFINE; intros; subst.
  - eauto.
  - econstructor 6; eauto. rewrite <- BR.
    econstructor 2; eauto.
  - econstructor 6; eauto. rewrite <- BR.
    econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 6; eauto. instantiate (1 := c2).
    econstructor 5; eauto.
  - econstructor 6; eauto.
  Unshelve. all: exact None.
Qed.

Lemma SimF_index_insensitive {R1 R2 E φ sim} (POSTFIX : sim <4= SimF φ sim) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : SimF φ sim p1 p2 t1 t2)
    p1' p2',
    SimF φ sim p1' p2' t1 t2.
Proof.
  do 2 intro. revert p1.
  induction p2 using (well_founded_induction olt_wf).
  rename H into IHp2.
  do 4 intro. revert IHp2.
  induction REFINE.
  - eauto.
  - intros. econstructor 2; eauto.
  - intros. econstructor 3; eauto.
  - intros. econstructor 4; eauto.
  - intros. econstructor 5; eauto.
  - intros. eapply SimF_contR; eauto.
  Unshelve. all: exact None.
Qed.

Lemma BisimF_index_insensitive {R1 R2 E φ sim} (POSTFIX : sim <4= BisimF φ sim) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : BisimF φ sim p1 p2 t1 t2)
    p1' p2',
    BisimF φ sim p1' p2' t1 t2.
Proof.
  intros. destruct REFINE.
  split; eapply SimF_index_insensitive; eauto; intros; apply POSTFIX; auto.
Qed.

Definition Sim_index_insensitive {R1 R2 E} φ :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : Sim φ p1 p2 t1 t2)
    p1' p2',
    Sim φ p1' p2' t1 t2.
Proof.
  pose proof (SimF_index_insensitive (E := E) (Sim_postfix φ)).
  intros. punfold REFINE. pfold.
  eapply SimF_monotone.
  { eapply H. eapply SimF_monotone; eauto. intros. pclearbot. auto. }
  eauto.
Qed.

Definition Bisim_index_insensitive {R1 R2 E} φ :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (BISIM : Bisim φ p1 p2 t1 t2)
    p1' p2',
    Bisim φ p1' p2' t1 t2.
Proof.
  pose proof (BisimF_index_insensitive (E := E) (BisimF_postfix φ)).
  intros. punfold BISIM. pfold.
  eapply BisimF_monotone.
  { eapply H. eapply BisimF_monotone; eauto. intros. pclearbot. auto. }
  eauto.
Qed.

Lemma Sim_refl {R E} φ (R_REFL : ∀ v, φ v v) :
  ∀ p1 p2 (t : CTree' E R), Sim φ p1 p2 t t.
Proof.
  pcofix CIH.
  intros. pfold. destruct t.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto. intros.
    econstructor 6; eauto. instantiate (1 := c).
    apply refine_prog with (p1' := Some 0) (p2' := Some 0); cbv; eauto.
    all: instantiate (1 := None); simpl; auto.
  Unshelve. all: exact None.
Qed.

Lemma Bisim_refl {R E} φ (R_REFL : ∀ v, φ v v) :
  ∀ p1 p2 (t : CTree' E R), Bisim φ p1 p2 t t.
Proof.
  pcofix CIH.
  intros. pfold. destruct t.
  - split; econstructor 2; eauto.
  - split; econstructor 3; eauto.
  - split; econstructor 4; eauto.
  - split; econstructor 5; eauto; intros;
    econstructor 6; eauto; instantiate (1 := c);
    apply refine_prog with (p1' := Some 0) (p2' := Some 0); cbv; eauto.
    all: instantiate (1 := None); simpl; auto.
  Unshelve. all: exact None.
Qed.

Lemma Sim_inv_retL E R0 R1 R2
  (φ0 : R0 → R2 → Prop) (φ1 : R1 → R2 → Prop)
  (sim0 : _ → _ → _ → _ → Prop)
  (POSTFIX : sim0 <4= SimF φ0 sim0)
  (sim1 : _ → _ → _ → _ → Prop) :
  ∀ p0' p1' t0 t1 (REFINE : SimF (E := E) φ0 sim0 p0' p1' t0 t1) t0' r0 r1
    (IMPLφ : ∀ r2, φ0 r0 r2 → φ1 r1 r2)
    (OBS0 : t0 = Ret r0) (OBS0' : t0' = Ret r1)
    p0 p1,
    SimF (E := E) φ1 sim1 p0 p1 t0' t1.
Proof.
  do 5 intro.
  apply SimF_index_insensitive with (p1' := Some 0) (p2' := p1') in REFINE; auto.
  clear p0'. remember (Some 0) as p0' in REFINE. revert Heqp0'.
  induction REFINE.
  - intros; subst. cbv in LT1. destruct p1'; lia.
  - inversion 3; subst. intros; subst.
    econstructor 2; eauto.
  - inversion 3.
  - inversion 3.
  - inversion 3.
  - intros; subst. econstructor 6; eauto.
  Unshelve. exact None.
Qed.

Lemma Sim_inv_retR E R0 R1 R2
  (φ0 : R0 → R1 → Prop) (φ1 : R0 → R2 → Prop)
  (sim0 : _ → _ → _ → _ → Prop)
  (POSTFIX : sim0 <4= SimF φ0 sim0)
  (sim1 : _ → _ → _ → _ → Prop) :
  ∀ p0' p1' t0 t1 (REFINE : SimF (E := E) φ0 sim0 p0' p1' t0 t1) t1' r1 r2
    (IMPLφ : ∀ r0, φ0 r0 r1 → φ1 r0 r2)
    (OBS0 : t1 = Ret r1) (OBS0' : t1' = Ret r2)
    p0 p1,
    SimF (E := E) φ1 sim1 p0 p1 t0 t1'.
Proof.
  do 5 intro.
  apply SimF_index_insensitive with (p1' := p0') (p2' := Some 0) in REFINE; auto.
  clear p1'. remember (Some 0) as p1' in REFINE. revert Heqp1'.
  induction REFINE.
  - intros; subst. cbv in LT2. destruct p2'; lia.
  - inversion 3; intros; subst.
    econstructor 2; eauto.
  - inversion 3.
  - intros; subst. econstructor 4; eauto.
  - intros; subst. econstructor 5; eauto.
  - inversion 3.
  Unshelve. exact None.
Qed.

Lemma Sim_inv_zeroR E R0 R1 R2 sim (sim' : _ → _ → _ → _ → Prop)
  (φ : R0 → R1 → Prop) (φ' : R0 → R2 → Prop)
  (POSTFIX : sim <4= SimF φ sim) :
  ∀ p0 p1 t0 t1 (REFINE : SimF (E := E) φ sim p0 p1 t0 t1)
    (OBS0 : t1 = Zero)
    p0' p1' t1',
    SimF (E := E) φ' sim' p0' p1' t0 t1'.
Proof.
  do 5 intro.
  apply SimF_index_insensitive with (p1' := p0) (p2' := Some 0) in REFINE; auto.
  remember (Some 0) as p1' in REFINE.
  revert Heqp1'. clear p1.
  induction REFINE.
  - intros; subst. cbv in LT2. destruct p2'; lia.
  - inversion 2.
  - inversion 2.
  - intros; subst. econstructor 4; eauto.
  - intros; subst. econstructor 5; eauto.
  - inversion 2.
  Unshelve. all:exact None.
Qed.

Lemma Sim_inv_choiceL E R0 R1 sim (φ : R0 → R1 → Prop)
  (POSTFIX : sim <4= SimF φ sim) :
  ∀ p0 p1 t0 t1 (REFINE : SimF (E := E) φ sim p0 p1 t0 t1)
    k (OBS0 : t0 = Choice k)
    c,
    SimF (E := E) φ sim p0 p1 (obs_ctree (k c)) t1.
Proof.
  do 5 intro.
  apply SimF_index_insensitive with (p1' := Some 0) (p2' := p1) in REFINE; auto.
  intros.
  apply SimF_index_insensitive with (p1 := Some 0) (p2 := p1); auto.
  clear p0. revert p1 t0 t1 REFINE k OBS0 c.
  remember (Some 0) as p0. do 4 intro. revert Heqp0.
  induction REFINE.
  - intros; subst. cbv in LT1. destruct p1'; lia.
  - inversion 2.
  - inversion 2.
  - inversion 2.
  - inversion 2; subst; clear_sig.
    intros. eapply SimF_index_insensitive; eauto.
  - intros; subst.
    exploit IHREFINE; eauto. instantiate (1 := c0).
    intros.
    econstructor 6; eauto.
Qed.

Lemma Sim_inv_divL E R0 R1 sim (φ : R0 → R1 → Prop)
  (POSTFIX : sim <4= SimF φ sim) :
  ∀ p0 p1 t0 t1 (REFINE : SimF (E := E) φ sim p0 p1 t0 t1)
    (DIV0 : div t0),
    div t1.
Proof.
  pcofix CIH.
  do 5 intro.
  apply SimF_index_insensitive with (p1' := p0) (p2' := Some 0) in REFINE; auto.
  clear p1. remember (Some 0) as p1 in REFINE. revert Heqp1.
  induction REFINE; intros; subst; try solve [punfold DIV0; inversion DIV0].
  - cbv in LT2. destruct p2'; lia.
  - punfold DIV0; inversion DIV0; subst; pclearbot; eauto.
  - pfold. econstructor; eauto.
Qed.

Variant State {E : Type → Type} {R : Type} :=
| IntS (t : CTree' E R) (* internal activity *)
| ExtS {A} (k : A → CTree E R) (* waiting for external response *)
.

Arguments State : clear implicits.

Variant Label {E : Type → Type} {R : Type} :=
| RetL (r : R)
| QueL {A} (e : E A)
| AnsL {A} (a : A)
| TauL
.

Arguments Label : clear implicits.

(* we emit a τ only when the path taken may diverge *)
Inductive Step {E : Type → Type} {R : Type}
: State E R → Label E R → State E R → Prop :=
| RetStep r
: Step (IntS (Ret r)) (RetL r) (IntS Zero)
| VisStep {A} (e : E A) k
: Step (IntS (Vis e k)) (QueL e) (ExtS k)
| AnsStep {A} k (a : A)
: Step (ExtS k) (AnsL a) (IntS (obs_ctree (k a)))
| DivStep k (DIV : div (Choice k))
: Step (IntS (Choice k)) TauL (IntS (Choice k))
| ChoiceStep k c ℓ s' (STEP : Step (IntS (obs_ctree (k c))) ℓ s')
: Step (IntS (Choice k)) ℓ s'
.

Section IND.
  Context {R : Type} {E : Type → Type}.
  Context (P : ∀ s ℓ s', @Step E R s ℓ s' → Prop).
  Context (PRetStep : ∀ r, P _ _ _ (RetStep r))
          (PVisStep : ∀ {A} (e : E A) k, P _ _ _ (VisStep e k))
          (PAnsStep : ∀ {A} k (a : A), P _ _ _ (AnsStep k a))
          (PDivStep : ∀ k DIV, P _ _ _ (DivStep k DIV))
          (PChoiceStep : ∀ k c ℓ s' STEP (IHSTEPk : P _ _ _ STEP), P _ _ _ (ChoiceStep k c ℓ s' STEP)).
  Fixpoint Step_ind s ℓ s' pf : P s ℓ s' pf.
  Proof.
    destruct pf.
    - apply PRetStep.
    - apply PVisStep.
    - apply PAnsStep.
    - apply PDivStep.
    - apply PChoiceStep. apply Step_ind.
  Qed.
End IND.

Definition RelLabel {E R1 R2} (φ : R1 → R2 → Prop) (ℓ1 : Label E R1) (ℓ2 : Label E R2) :=
  match ℓ1 with
  | RetL r1 => match ℓ2 with RetL r2 => φ r1 r2 | _ => False end
  | QueL e1 => match ℓ2 with QueL e2 => existT _ _ e1 = existT _ _ e2 | _ => False end
  | AnsL a1 => match ℓ2 with AnsL a2 => existT _ _  a1 = existT _ _ a2 | _ => False end
  | TauL => match ℓ2 with TauL => True | _ => False end
  end.

Definition SimLTSF {E R1 R2} (φ : R1 → R2 → Prop)
  (sim : State E R1 → State E R2 → Prop) s1 s2 :=
  ∀ ℓ1 s1' (STEP1 : Step s1 ℓ1 s1'),
    ∃ ℓ2 s2', RelLabel φ ℓ1 ℓ2 ∧ Step s2 ℓ2 s2' ∧ sim s1' s2'
.

Variant lift_sim {E R1 R2 φ sim} : State E R1 → State E R2 → Prop :=
| sim_Int p1 p2 t1 t2
  (SIM : SimF φ sim p1 p2 t1 t2)
: lift_sim (IntS t1) (IntS t2)
| sim_Ext {A} (p1 p2 : option nat) k1 k2
  (SIM : ∀ a : A, sim p1 p2 (obs_ctree (k1 a)) (obs_ctree (k2 a)))
: lift_sim (ExtS k1) (ExtS k2)
.

Arguments lift_sim {_ _ _} _ _.

Lemma SimF_SimLTSF {E R1 R2}
  (φ : R1 → R2 → Prop) sim (POSTFIX : sim <4= SimF (E := E) φ sim) :
  ∀ p1 p2 t1 t2 (SIM : SimF φ sim p1 p2 t1 t2),
    SimLTSF φ (lift_sim φ sim) (IntS t1) (IntS t2).
Proof.
  intros.
  apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2) in SIM; auto.
  clear p1. remember (Some 0) as p1. revert Heqp1.
  induction SIM; intros; subst.
  - cbv in LT1. destruct p1'; lia.
  - red. inversion 1; subst.
    exists (RetL y), (IntS Zero).
    constructor. eauto.
    constructor. repeat constructor.
    econstructor. econstructor 4.
  - red. inversion 1; subst; clear_sig.
    exists (QueL e), (ExtS k2).
    repeat econstructor; eauto.
  - red. inversion 1.
  - repeat intro. clear IHk.
    remember (IntS (Choice k)) as s1 in STEP1.
    assert match s1 with
    | IntS (Choice k) => ∀ n, SimF φ sim p1' p2 (obs_ctree (k n)) t2
    | _ => False
    end by (subst; auto).
    clear Heqs1 CHOICE k.
    rename H into CHOICE.
    revert CHOICE.
    induction STEP1; try solve [destruct 1]; intros.
    { punfold DIV. inversion DIV; subst. pclearbot.
      specialize (CHOICE c) as CHOICE'.
      eapply Sim_inv_divL in CHOICE' as DIV'; eauto.
      punfold DIV'. inversion DIV'; subst. pclearbot. clear DIV'.
      exists TauL, (IntS (Choice k0)).
      split. cbv; auto.
      split. constructor. pfold; econstructor; eauto.
      econstructor. econstructor 5; eauto. }
    { specialize (CHOICE c). destruct (obs_ctree (k c)).
      { inversion STEP1; subst. clear STEP1 IHSTEP1.
        remember (Ret v) as t1 in CHOICE.
        apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2) in CHOICE; auto.
        clear p1'.
        remember (Some 0) as p1. revert Heqt1 Heqp1.
        induction CHOICE; try solve [inversion 1].
        { intros; subst. cbv in LT1. destruct p1'; lia. }
        { inversion 1; intros; subst.
          exists (RetL y), (IntS Zero).
          constructor; eauto.
          constructor. repeat econstructor; eauto.
          econstructor. econstructor 4; eauto. }
        { intros; subst.
          destruct (IHCHOICE eq_refl eq_refl) as (ℓ2 & s2' & ? & ? & ?).
          exists ℓ2, s2'.
          constructor; eauto.
          constructor; eauto.
          econstructor 5; eauto. } }
      { inversion STEP1; subst; clear_sig. clear STEP1 IHSTEP1.
        remember (Vis e k0) as t1 in CHOICE.
        apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2) in CHOICE; auto.
        clear p1'.
        remember (Some 0) as p1. revert Heqt1 Heqp1.
        induction CHOICE; try solve [inversion 1].
        { intros; subst. cbv in LT1. destruct p1'; lia. }
        { inversion 1; intros; subst; clear_sig.
          exists (QueL e), (ExtS k2).
          repeat econstructor; eauto. }
        { intros; subst.
          destruct (IHCHOICE eq_refl eq_refl) as (ℓ2 & s2' & ? & ? & ?).
          exists ℓ2, s2'.
          constructor; eauto.
          constructor; eauto.
          econstructor 5; eauto. } }
      { inversion STEP1. }
      { apply IHSTEP1. intros. eapply Sim_inv_choiceL; eauto. } }
  - red. intros. specialize (IHSIM eq_refl _ _ STEP1).
    destruct IHSIM as (ℓ2 & s2' & ? & ? & ?).
    exists ℓ2, s2'.
    constructor; eauto.
    constructor; eauto.
    econstructor 5; eauto.
  Unshelve. all: exact None.
Qed.

(* why separate φ and sim when sim is enough to express the relation between return values? *)
Lemma SimF_transL {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3),
    SimF (comp2 φ12 φ23) (comp4 (SimF φ12 sim12) sim23) p11 p22 t1 t3.
Proof.
  do 5 intro. induction REFINE1.
  - do 4 intro. apply POSTFIX12 in SIM. revert t1 SIM. induction REFINE2.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros.
      eapply Sim_inv_retR; first [eassumption | reflexivity | idtac].
      cbv [comp2]; eauto. }
    { intros.
      apply SimF_index_insensitive with (p1' := Some 0) (p2' := Some 0) in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Vis e k1) as t2 in SIM. revert Heqt2.
      induction SIM.
      { intros; subst. cbv in LT3. destruct p2'1; lia. }
      { inversion 1. }
      { inversion 1. intros; subst. clear_sig.
        intros. econstructor 3; eauto. intros.
        cbv [comp4]. exists p2'1, p1'0, (obs_ctree (k1 a)). eauto. }
      { intros. subst. econstructor 4; eauto. }
      { intros; subst. econstructor 5; eauto. }
      { inversion 1. } }
    { intros. eapply Sim_inv_zeroR; eauto. }
    { intros.
      apply SimF_index_insensitive with (p1' := Some 0) (p2' := Some 0) in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Choice k) as t2' in SIM. revert Heqt2'.
      induction SIM.
      { intros; subst. cbv in LT3. destruct p2'0; lia. }
      { inversion 1. }
      { inversion 1. }
      { intros. subst. econstructor 4; eauto. }
      { intros. subst. econstructor 5; eauto. }
      { inversion 1; intros; subst. clear_sig. apply (IHk c).
        eapply SimF_index_insensitive; eauto. } }
    { intros. econstructor 6; eauto. }
  - intros; subst.
    eapply Sim_inv_retL; first [eassumption | reflexivity | idtac].
    cbv [comp2]. eauto.
  - intros.
    apply SimF_index_insensitive with (p1' := Some 0) (p2' := p22) in REFINE2; auto.
    remember (Some 0) as o' in REFINE2. revert Heqo'.
    remember (Vis e k2) as t2 in REFINE2. revert Heqt2.
    induction REFINE2.
    { intros; subst. cbv in LT1. destruct p1'0; lia. }
    { inversion 1. }
    { inversion 1; subst; clear_sig.
      intros; subst.
      econstructor 3; eauto. intros.
      specialize (CONT a). apply POSTFIX12 in CONT.
      cbv [comp4]. eauto. }
    { inversion 1. }
    { inversion 1. }
    { intros. econstructor 6; eauto. }
  - intros. econstructor 4; eauto.
  - intros. econstructor 5; eauto.
  - intros. eapply IHREFINE1. eapply Sim_inv_choiceL in REFINE2; eauto.
Qed.

Lemma SimF_transR {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3),
    SimF (comp2 φ12 φ23) (comp4 sim12 (SimF φ23 sim23)) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - do 4 intro. apply POSTFIX23 in SIM. revert t2 SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros. eapply Sim_inv_retL; eauto.
      cbv [comp2]; eauto. }
    { intros. clear LT1 LT2 p1 p3.
      apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2') in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Vis e k2) as t1 in SIM. revert Heqt1.
      induction SIM.
      { intros; subst. cbv in LT1. destruct p1'1; lia. }
      { inversion 1. }
      { inversion 1. intros; subst. clear_sig.
        intros. econstructor 3; eauto. intros.
        specialize (CONT0 a). apply POSTFIX23 in CONT0.
        cbv [comp4]; eauto. }
      { inversion 1. }
      { inversion 1. }
      { intros. subst. econstructor 6; eauto. } }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { intros. eauto using Sim_inv_choiceL. }
  - intros; subst. eapply Sim_inv_retR; eauto.
    cbv [comp2]. eauto.
  - intros.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Vis e k1) as t2 in REFINE1. revert Heqt2.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'0; lia. }
    { inversion 1. }
    { inversion 1; subst; clear_sig.
      intros; subst.
      econstructor 3; eauto. intros.
      specialize (CONT a). apply POSTFIX23 in CONT.
      cbv [comp4]. eauto. }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { inversion 1. }
  - intros. eapply Sim_inv_zeroR; eauto.
  - intros.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Choice k) as t2' in REFINE1. revert Heqt2'.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'; lia. }
    { inversion 1. }
    { inversion 1. }
    { intros; subst. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; intros; subst; clear_sig. eauto. }
  - intros. econstructor 6; eauto.
Qed.

Lemma BisimF_trans_not_choice {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3)
    (NCHOICE : match t2 with Choice _ => False | _ => True end),
    SimF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - do 4 intro. revert t2 SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros. eapply Sim_inv_retL; eauto.
      cbv [comp2]; eauto. }
    { intros. clear LT1 LT2 p1 p3. apply POSTFIX23 in SIM.
      apply SimF_index_insensitive with (p1' := Some 0) (p2' := Some 1) in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Some 1) as o'' in SIM. clear Heqo''.
      remember (Vis e k2) as t1 in SIM. revert Heqt1.
      induction SIM.
      { intros; subst. cbv in LT1. destruct p1'1; lia. }
      { inversion 1. }
      { inversion 1. intros; subst. clear_sig.
        intros. econstructor 3; eauto.
        cbv [comp4]; eauto. }
      { inversion 1. }
      { inversion 1. }
      { intros. subst. econstructor 6; eauto. } }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { destruct 2. }
  - intros; subst. eapply Sim_inv_retR; eauto.
    cbv [comp2]. eauto.
  - intros.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Vis e k1) as t2 in REFINE1. revert Heqt2.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'0; lia. }
    { inversion 1. }
    { inversion 1; subst; clear_sig.
      intros; subst.
      econstructor 3; eauto.
      cbv [comp4]. eauto. }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { inversion 1. }
  - intros. eapply Sim_inv_zeroR; eauto.
  - destruct 2.
  - intros. econstructor 6; eauto.
Qed.

Lemma BisimF_trans {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3),
    SimF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - do 4 intro. revert t2 SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros. eapply Sim_inv_retL; eauto.
      cbv [comp2]; eauto. }
    { intros. clear LT1 LT2 p1 p3. apply POSTFIX23 in SIM.
      apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2') in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Vis e k2) as t1 in SIM. revert Heqt1.
      induction SIM.
      { intros; subst. cbv in LT1. destruct p1'1; lia. }
      { inversion 1. }
      { inversion 1. intros; subst. clear_sig.
        intros. econstructor 3; eauto.
        cbv [comp4]; eauto. }
      { inversion 1. }
      { inversion 1. }
      { intros. subst. econstructor 6; eauto. } }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { admit. }
  - intros; subst. eapply Sim_inv_retR; eauto. 
    cbv [comp2]. eauto.
  - intros.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Vis e k1) as t2 in REFINE1. revert Heqt2.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'0; lia. }
    { inversion 1. }
    { inversion 1; subst; clear_sig.
      intros; subst.
      econstructor 3; eauto.
      cbv [comp4]. eauto. }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { inversion 1. }
  - intros. eapply Sim_inv_zeroR; eauto.
  - intros.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Choice k) as t2' in REFINE1. revert Heqt2'.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'; lia. }
    { inversion 1. }
    { inversion 1. }
    { intros; subst. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; intros; subst. eauto. }
  - intros. econstructor 6; eauto.
Abort.

Lemma BisimF_trans_choice {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3)
    k (CHOICE : t2 = Choice k),
    SimF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - intros. revert k CHOICE t2 SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { inversion 1. }
    { inversion 1. }
    { intros. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; subst. clear CHOICE. intros. apply POSTFIX23 in SIM as REFINE2.
      eapply Sim_inv_choiceL with (c := c) in REFINE2; auto.
      apply SimF_index_insensitive with (p1' := p1') (p2' := p2) in REFINE2; auto.
      destruct (obs_ctree (k0 c)) eqn:OBS.
      1,2,3: eapply BisimF_trans_not_choice; eauto; simpl; auto.
      specialize (IHREFINE1 _ eq_refl). admit. }
  - inversion 2.
  - inversion 2.
  - inversion 2.
  - inversion 2; subst.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Choice k0) as t2' in REFINE1. revert Heqt2'.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'; lia. }
    { inversion 1. }
    { inversion 1. }
    { intros; subst. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; intros; subst.
      specialize (CHOICE c). specialize (IHk c).
      destruct (obs_ctree (k0 c)) eqn:OBS; eauto.
      all: eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  - intros; subst. econstructor 6; eauto.
Abort.

Lemma BisimF_trans_choice {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3)
    k (CHOICE : t2 = Choice k),
    SimF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 5 intro. induction REFINE1.
  - intros. revert k CHOICE t1 SIM. induction REFINE2.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1; subst. intros. apply POSTFIX12 in SIM.
      apply SimF_index_insensitive with (p1' := p2) (p2' := Some 0) in SIM; auto.
      clear LT2.
      remember (Some 0) as p' in SIM. revert Heqp'.
      remember (Choice k0) as t2' in SIM. revert Heqt2'.
      induction SIM.
      { intros; subst. cbv in LT2. destruct p2'0; lia. }
      { inversion 1. }
      { inversion 1. }
      { intros; econstructor 4; eauto. }
      { intros; subst. econstructor 5; eauto. }
      { inversion 1; intros; subst. specialize (CHOICE c). specialize (IHk c).
        apply SimF_index_insensitive with (p1' := p1) (p2' := p2') in SIM; auto.
        destruct (obs_ctree (k0 c)).
        1,2,3: eapply BisimF_trans_not_choice; eauto; simpl; auto.
        specialize (IHk _ eq_refl). admit. } }
    { intros; subst. econstructor 6; eauto. }
  - inversion 2.
  - inversion 2.
  - inversion 2. econstructor 4; eauto.
  - intros. econstructor 5; eauto.
  - inversion 2; subst.
    apply SimF_index_insensitive with (p1' := Some 0) (p2' := p22) in REFINE2; auto.
    remember (Some 0) as p' in REFINE2.
    remember (Choice k0) as t1' in REFINE2.
    revert Heqt1' Heqp'.
    induction REFINE2.
    { intros; subst. cbv in LT1. destruct p1'; lia. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1; subst. intros; subst. specialize (CHOICE0 c).
      destruct (obs_ctree (k0 c)); eauto.
      all: eapply BisimF_trans_not_choice; eauto; simpl; auto. }
    { intros; econstructor 6; eauto. }
Abort.

