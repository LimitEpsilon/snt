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

Inductive CTreeF {E : Type → Type} {R : Type} {CTree : Type} :=
| Ret (v : R)
| Vis {A} (e : E A) (k : A → CTree)
| Zero
| Choice (k : nat → CTreeF)
.

Arguments CTreeF : clear implicits.

Section IND.
  Context {E : Type → Type} {R : Type} {CTree : Type}.
  Context (P : CTreeF E R CTree → Prop).
  Context (PRet : ∀ v, P (Ret v))
          (PVis : ∀ {A} (e : E A) k, P (Vis e k))
          (PZero : P Zero)
          (PChoice : ∀ k (IHk : ∀ c, P (k c)), P (Choice k)).
  Fixpoint CTreeF_ind t : P t.
  Proof.
    destruct t.
    - apply PRet.
    - apply PVis.
    - apply PZero.
    - apply PChoice. intros. apply CTreeF_ind.
  Qed.
End IND.

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

Lemma ole_top x : ole x None.
Proof. destruct x; cbv; eauto. Qed.

(* from FreeSim (Stuttering for Free) *)
(* infinite silent steps should be equivalent only to infinite silent steps *)
Inductive RefineF {R1 R2 E r sim}
  : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop :=
| refine_prog p1 p2 t1 t2 p1' p2'
  (* only rule that strictly decrements the progress indices*)
  (LT1 : p1' ≺ p1) (LT2 : p2' ≺ p2)
  (SIM : sim p1' p2' t1 t2)
: RefineF p1 p2 t1 t2
| refine_ret p1 p2 x y
  (RET : r x y : Prop)
: RefineF p1 p2 (Ret x) (Ret y)
| refine_vis p1 p2 p1' p2' {A} (e : E A) k1 k2
  (CONT : ∀ a, sim p1' p2' (obs_ctree (k1 a)) (obs_ctree (k2 a)))
: RefineF p1 p2 (Vis e k1) (Vis e k2)
| refine_zero p1 p2 t2
: RefineF p1 p2 Zero t2
| refine_choiceL p1 p2 p1' t2 k
  (CHOICE : ∀ c, RefineF p1' p2 (k c) t2)
: RefineF p1 p2 (Choice k) t2
| refine_choiceR p1 p2 p2' t1 k
  c (CHOICE : RefineF p1 p2' t1 (k c))
: RefineF p1 p2 t1 (Choice k)
.

Arguments RefineF {_ _ _} _ _.

Section IND.
  Context {R1 R2 E} (r : R1 → R2 → Prop) (sim : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop).
  Context (P : ∀ p1 p2 t1 t2, RefineF r sim p1 p2 t1 t2 → Prop).
  Context (Pprog : ∀ p1 p2 t1 t2 p1' p2' LT1 LT2 SIM, P _ _ _ _ (refine_prog p1 p2 t1 t2 p1' p2' LT1 LT2 SIM))
          (Pret : ∀ p1 p2 x y RET, P _ _ _ _ (refine_ret p1 p2 x y RET))
          (Pvis : ∀ p1 p2 p1' p2' A (e : E A) k1 k2 CONT, P _ _ _ _ (refine_vis p1 p2 p1' p2' e k1 k2 CONT))
          (Pzero : ∀ p1 p2 t2, P _ _ _ _ (refine_zero p1 p2 t2))
          (PL : ∀ p1 p2 p1' t2 k CHOICE (IHk : ∀ c, P _ _ _ _ (CHOICE c)), P _ _ _ _ (refine_choiceL p1 p2 p1' t2 k CHOICE))
          (PR : ∀ p1 p2 p2' t1 k c CHOICE (IHk : P _ _ _ _ CHOICE), P _ _ _ _ (refine_choiceR p1 p2 p2' t1 k c CHOICE)).
  Fixpoint RefineF_ind p1 p2 t1 t2 pf : P p1 p2 t1 t2 pf.
  Proof.
    destruct pf.
    - apply Pprog.
    - apply Pret.
    - apply Pvis.
    - apply Pzero.
    - apply PL. intros. apply RefineF_ind.
    - apply PR. intros. apply RefineF_ind.
  Qed.
End IND.

Definition BisimF {R1 R2 E} (φ : R1 → R2 → Prop) sim p1 p2 t1 t2 :=
  RefineF (E := E) φ sim p1 p2 t1 t2 ∧
  RefineF
    (fun r1 r2 => φ r2 r1)
    (fun p1 p2 t1 t2 => sim p2 p1 t2 t1)
    p2 p1 t2 t1
.

Lemma RefineF_monotone R1 R2 E r : monotone4 (@RefineF R1 R2 E r).
Proof.
  repeat intro. revert r' LE. induction IN; intros.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
Qed.

Hint Resolve RefineF_monotone : paco.

Lemma BisimF_monotone R1 R2 E φ : monotone4 (@BisimF R1 R2 E φ).
Proof.
  repeat intro.
  destruct IN as (IN & IN').
  split; eapply RefineF_monotone; eauto.
Qed.

Hint Resolve BisimF_monotone : paco.

Definition Refine {R1 R2 E} r := paco4 (@RefineF R1 R2 E r) bot4.

Definition Bisim {R1 R2 E} r := paco4 (@BisimF R1 R2 E r) bot4.

Lemma Refine_postfix {R1 R2 E} (φ : R1 → R2 → Prop) :
  Refine (E := E) φ <4= RefineF φ (Refine φ).
Proof.
  repeat intro. punfold PR.
  eapply RefineF_monotone; eauto.
  intros. pclearbot. auto.
Qed.

Lemma Bisim_postfix {R1 R2 E} (φ : R1 → R2 → Prop) :
  Bisim (E := E) φ <4= RefineF φ (Bisim φ).
Proof.
  repeat intro.
  punfold PR. destruct PR.
  eapply RefineF_monotone; eauto.
  intros. pclearbot. auto.
Qed.

Lemma Bisim_postfix_flipped {R1 R2 E} (φ : R1 → R2 → Prop) :
  (fun p1 p2 t1 t2 => Bisim (E := E) φ p2 p1 t2 t1) <4=
  RefineF (fun r1 r2 => φ r2 r1) (fun p1 p2 t1 t2 => Bisim φ p2 p1 t2 t1).
Proof.
  repeat intro.
  punfold PR. destruct PR.
  eapply RefineF_monotone; eauto.
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

Lemma RefineF_index_mono {R1 R2 E} φ (sim : _ → _ → _ → _ → Prop) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : RefineF φ sim p1 p2 t1 t2)
    p1' p2' (LE1 : p1 ≼ p1') (LE2 : p2 ≼ p2'),
    RefineF φ sim p1' p2' t1 t2.
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

Lemma RefineF_contR {R1 R2 E φ sim} (POSTFIX : sim <4= RefineF φ sim) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2' : CTree' E R2)
    (* if t1 refines t2', *)
    (REFINE : RefineF φ sim p1 p2 t1 t2')
    (* for any t2 that may continue as t2', *)
    t2 k2 (OBS : t2 = Choice k2) c2 (BR : t2' = k2 c2)
    (* t1 must refine t2 *)
    p1' p2', RefineF φ sim p1' p2' t1 t2.
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

Lemma RefineF_index_insensitive {R1 R2 E φ sim} (POSTFIX : sim <4= RefineF φ sim) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : RefineF φ sim p1 p2 t1 t2)
    p1' p2',
    RefineF φ sim p1' p2' t1 t2.
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
  - intros. eapply RefineF_contR; eauto.
  Unshelve. all: exact None.
Qed.

Lemma BisimF_index_insensitive {R1 R2 E φ sim} (POSTFIX : sim <4= BisimF φ sim) :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : BisimF φ sim p1 p2 t1 t2)
    p1' p2',
    BisimF φ sim p1' p2' t1 t2.
Proof.
  intros. destruct REFINE.
  split; eapply RefineF_index_insensitive; eauto; intros; apply POSTFIX; auto.
Qed.

Definition Refine_index_insensitive {R1 R2 E} φ :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (REFINE : Refine φ p1 p2 t1 t2)
    p1' p2',
    Refine φ p1' p2' t1 t2.
Proof.
  pose proof (RefineF_index_insensitive (E := E) (Refine_postfix φ)).
  intros. punfold REFINE. pfold.
  eapply RefineF_monotone.
  { eapply H. eapply RefineF_monotone; eauto. intros. pclearbot. auto. }
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

Lemma Refine_refl {R E} φ (R_REFL : ∀ v, φ v v) :
  ∀ p1 p2 (t : CTree' E R), Refine φ p1 p2 t t.
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

Lemma Refine_inv_retL E R0 R1 R2
  (φ0 : R0 → R2 → Prop) (φ1 : R1 → R2 → Prop)
  (sim0 : _ → _ → _ → _ → Prop)
  (POSTFIX : sim0 <4= RefineF φ0 sim0)
  (sim1 : _ → _ → _ → _ → Prop) :
  ∀ p0' p1' t0 t1 (REFINE : RefineF (E := E) φ0 sim0 p0' p1' t0 t1) t0' r0 r1
    (IMPLφ : ∀ r2, φ0 r0 r2 → φ1 r1 r2)
    (OBS0 : t0 = Ret r0) (OBS0' : t0' = Ret r1)
    p0 p1,
    RefineF (E := E) φ1 sim1 p0 p1 t0' t1.
Proof.
  do 5 intro.
  apply RefineF_index_insensitive with (p1' := Some 0) (p2' := p1') in REFINE; auto.
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

Lemma Refine_inv_retR E R0 R1 R2
  (φ0 : R0 → R1 → Prop) (φ1 : R0 → R2 → Prop)
  (sim0 : _ → _ → _ → _ → Prop)
  (POSTFIX : sim0 <4= RefineF φ0 sim0)
  (sim1 : _ → _ → _ → _ → Prop) :
  ∀ p0' p1' t0 t1 (REFINE : RefineF (E := E) φ0 sim0 p0' p1' t0 t1) t1' r1 r2
    (IMPLφ : ∀ r0, φ0 r0 r1 → φ1 r0 r2)
    (OBS0 : t1 = Ret r1) (OBS0' : t1' = Ret r2)
    p0 p1,
    RefineF (E := E) φ1 sim1 p0 p1 t0 t1'.
Proof.
  do 5 intro.
  apply RefineF_index_insensitive with (p1' := p0') (p2' := Some 0) in REFINE; auto.
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

Lemma Refine_inv_zeroR E R0 R1 R2 sim (sim' : _ → _ → _ → _ → Prop)
  (φ : R0 → R1 → Prop) (φ' : R0 → R2 → Prop)
  (POSTFIX : sim <4= RefineF φ sim) :
  ∀ p0 p1 t0 t1 (REFINE : RefineF (E := E) φ sim p0 p1 t0 t1)
    (OBS0 : t1 = Zero)
    p0' p1' t1',
    RefineF (E := E) φ' sim' p0' p1' t0 t1'.
Proof.
  do 5 intro.
  apply RefineF_index_insensitive with (p1' := p0) (p2' := Some 0) in REFINE; auto.
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

Lemma Refine_inv_choiceL E R0 R1 sim (φ : R0 → R1 → Prop)
  (POSTFIX : sim <4= RefineF φ sim) :
  ∀ p0 p1 t0 t1 (REFINE : RefineF (E := E) φ sim p0 p1 t0 t1)
    k (OBS0 : t0 = Choice k)
    c,
    RefineF (E := E) φ sim p0 p1 (k c) t1.
Proof.
  do 5 intro.
  apply RefineF_index_insensitive with (p1' := Some 0) (p2' := p1) in REFINE; auto.
  intros.
  apply RefineF_index_insensitive with (p1 := Some 0) (p2 := p1); auto.
  clear p0. revert p1 t0 t1 REFINE k OBS0 c.
  remember (Some 0) as p0. do 4 intro. revert Heqp0.
  induction REFINE.
  - intros; subst. cbv in LT1. destruct p1'; lia.
  - inversion 2.
  - inversion 2.
  - inversion 2.
  - inversion 2; subst; clear_sig.
    intros. eapply RefineF_index_insensitive; eauto.
  - intros; subst.
    exploit IHREFINE; eauto. instantiate (1 := c0).
    intros.
    econstructor 6; eauto.
Qed.

(*
  RefineF φ sim p1 p2 t1 t2 ↔
  ∀ p1' t1', t1 => t1' → ∃ p2' t2', t2 =>* t2' ∧ sim p1' p2' t1' t2'
  and
  ∀ p1' t1' ℓ, t1 =ℓ=> t1' → ∃ p2' t2', t2 =>*ℓ=>* t2' ∧ sim p1' p2' t1' t2'
  and
  ∀ r1, t1 ⇓ r1 → ∃ t2' r2, t2 =>* t2' ∧ t2' ⇓ r2 ∧ φ r1 r2
*)

(* RefineF φ12 sim12 p11 p12 t1 t2 *)
(* RefineF φ23 sim23 p21 p22 t2 t3 *)
(* does not imply RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3 *)
(* this is because of the silent steps *)

Lemma RefineF_transL {R1 R2 R3 E} (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3),
    RefineF (comp2 φ12 φ23) (comp4 (RefineF φ12 sim12) sim23) p11 p22 t1 t3.
Proof.
  do 5 intro. induction REFINE1.
  - do 4 intro. apply POSTFIX12 in SIM. revert t1 SIM. induction REFINE2.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros.
      eapply Refine_inv_retR; first [eassumption | reflexivity | idtac].
      cbv [comp2]; eauto. }
    { intros.
      apply RefineF_index_insensitive with (p1' := Some 0) (p2' := Some 0) in SIM; auto.
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
    { intros. eapply Refine_inv_zeroR; eauto. }
    { intros.
      apply RefineF_index_insensitive with (p1' := Some 0) (p2' := Some 0) in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Choice k) as t2' in SIM. revert Heqt2'.
      induction SIM.
      { intros; subst. cbv in LT3. destruct p2'0; lia. }
      { inversion 1. }
      { inversion 1. }
      { intros. subst. econstructor 4; eauto. }
      { intros. subst. econstructor 5; eauto. }
      { inversion 1; intros; subst. clear_sig. apply (IHk c).
        eapply RefineF_index_insensitive; eauto. } }
    { intros. econstructor 6; eauto. }
  - intros; subst.
    eapply Refine_inv_retL; first [eassumption | reflexivity | idtac].
    cbv [comp2]. eauto.
  - intros.
    apply RefineF_index_insensitive with (p1' := Some 0) (p2' := p22) in REFINE2; auto.
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
  - intros. eapply IHREFINE1. eapply Refine_inv_choiceL in REFINE2; eauto.
Qed.

Lemma RefineF_transR {R1 R2 R3 E} (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3),
    RefineF (comp2 φ12 φ23) (comp4 sim12 (RefineF φ23 sim23)) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - do 4 intro. apply POSTFIX23 in SIM. revert t2 SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros. eapply Refine_inv_retL; eauto.
      cbv [comp2]; eauto. }
    { intros. clear LT1 LT2 p1 p3.
      apply RefineF_index_insensitive with (p1' := Some 0) (p2' := Some 1) in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Some 1) as o'' in SIM. clear Heqo''.
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
    { intros. clear p3. rename p2'0 into p3.
      apply IHREFINE1. eapply Refine_inv_choiceL; eauto. }
  - intros; subst. eapply Refine_inv_retR; eauto.
    cbv [comp2]. eauto.
  - intros.
    apply RefineF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
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
  - intros. eapply Refine_inv_zeroR; eauto.
  - intros.
    apply RefineF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
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
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3)
    (NCHOICE : match t2 with Choice _ => False | _ => True end),
    RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - do 4 intro. revert t2 SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { intros. eapply Refine_inv_retL; eauto.
      cbv [comp2]; eauto. }
    { intros. clear LT1 LT2 p1 p3. apply POSTFIX23 in SIM.
      apply RefineF_index_insensitive with (p1' := Some 0) (p2' := p2') in SIM; auto.
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
    { destruct 2. }
  - intros; subst. eapply Refine_inv_retR; eauto.
    cbv [comp2]. eauto.
  - intros.
    apply RefineF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    remember (Some 0) as o' in REFINE1. revert Heqo'.
    remember (Vis e k1) as t2 in REFINE1. revert Heqt2.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'0; lia. }
    { inversion 1. }
    { inversion 1; subst; clear_sig.
      intros; subst.
      econstructor 3; cbv [comp4]; eauto. }
    { intros. econstructor 4; eauto. }
    { intros. econstructor 5; eauto. }
    { inversion 1. }
  - intros. eapply Refine_inv_zeroR; eauto.
  - destruct 2.
  - intros. econstructor 6; eauto.
Qed.

Lemma BisimF_trans {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3),
    RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 4 intro. revert p11 p12 t1. induction t2.
  { intros. eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  { intros. eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  { intros. eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  remember (Choice k) as t2 eqn:CHOICE.
  intros. revert p11 p12 t1 REFINE1 CHOICE. induction REFINE2.
  - intros. clear LT1. revert CHOICE t2 p1' SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { inversion 1. }
    { inversion 1. }
    { intros. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; subst. intros. clear CHOICE.
      apply POSTFIX23 in SIM.
      eapply Refine_inv_choiceL with (c := c) in SIM; auto.
      apply RefineF_index_insensitive with (p1' := p1') (p2' := p2) in SIM; eauto. }
  - inversion 2.
  - inversion 2.
  - inversion 2.
  - inversion 2; subst. clear CHOICE0.
    apply RefineF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    clear p12. remember (Some 0) as p12 in REFINE1. revert Heqp12.
    remember (Choice k) as t2' in REFINE1. revert Heqt2'.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'; lia. }
    { inversion 1. }
    { inversion 1. }
    { intros; subst. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; intros; subst. eauto. }
  - intros; subst. econstructor 6; eauto.
Qed.

Lemma BisimF_trans'{R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3),
    RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 2 intro. revert p11. induction p12 using (well_founded_induction olt_wf).
  rename H into IHp12. induction 1.
  - intros. exploit IHp12; eauto.
    intros. eapply RefineF_index_mono; eauto.
    red. eauto.
    apply ole_reflexive.
  - intros; subst. eapply Refine_inv_retL; eauto.
    cbv [comp2]. eauto.
  - intros.
    apply RefineF_index_insensitive with (p1' := Some 0) (p2' := p22) in REFINE2; auto.
    remember (Some 0) as o' in REFINE2. revert Heqo'.
    remember (Vis e k2) as t1 in REFINE2. revert Heqt1.
    induction REFINE2.
    { intros; subst. cbv in LT1. destruct p1'0; lia. }
    { inversion 1. }
    { inversion 1; subst; clear_sig.
      intros; subst.
      econstructor 3; cbv [comp4]; eauto. }
    { inversion 1. }
    { inversion 1. }
    { intros. econstructor 6; eauto. }
  - intros. econstructor 4; eauto.
  - intros. econstructor 5; eauto.
  - intros.
    apply RefineF_index_insensitive with (p1' := Some 0) (p2' := p22) in REFINE2; auto.
    clear p21. remember (Some 0) as p21 in REFINE2. revert Heqp21.
    remember (Choice k) as t1' in REFINE2. revert Heqt1'.
    induction REFINE2.
    { intros; subst. cbv in LT1. destruct p1'; lia. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1; intros; subst.
      apply RefineF_index_insensitive with (p1' := p1) (p2' := Some 0) in REFINE1; auto.
      eapply IHp12; eauto. admit. }
    { intros; subst. econstructor 6; eauto. }
Abort.

Lemma BisimF_trans_choice {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3)
    k (CHOICE : t2 = Choice k),
    RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 5 intro. induction REFINE1.
  - intros. revert k CHOICE p1 LT1 t1 SIM. induction REFINE2.
    { intros; econstructor 1; eauto. cbv [comp4]; eauto. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1; intros; subst. apply POSTFIX12 in SIM. clear p2 LT2.
      apply RefineF_index_insensitive with (p1' := p1) (p2' := Some 0) in SIM; auto.
      remember (Some 0) as p2 in SIM. revert Heqp2.
      remember (Choice k0) as t2' in SIM. revert Heqt2'.
      induction SIM.
      { intros; subst. cbv in LT2. destruct p2'0; lia. }
      { inversion 1. }
      { inversion 1. }
      { intros; subst. econstructor 4; eauto. }
      { intros; subst. econstructor 5; eauto. }
      { inversion 1; intros; subst.
        specialize (IHk c). specialize (CHOICE c).
        apply RefineF_index_insensitive with (p1' := p3) (p2' := p2'0) in SIM; auto.
        destruct (obs_ctree (k0 c)).
        1,2,3: eapply BisimF_trans_not_choice; eauto; simpl; auto.
        specialize (IHk _ eq_refl).
        (* for any p1 such that p3 ≼ p1,
          RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p1 p0 (Choice k ⊕ t1) t2 *)
        admit. } }
    { intros; subst. econstructor 6; eauto. }
  - inversion 2.
  - inversion 2.
  - intros; subst. econstructor 4; eauto.
  - intros; subst. econstructor 5; eauto.
  - inversion 2; subst.
    eapply Refine_inv_choiceL with (c := c) in REFINE2; eauto.
    destruct (obs_ctree (k0 c)); eauto.
    all: eapply BisimF_trans_not_choice; eauto; simpl; auto.
Abort.

Lemma BisimF_trans_choice {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop)
  sim12 sim23
  (POSTFIX12 : sim12 <4= RefineF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= RefineF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : RefineF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : RefineF (E := E) φ23 sim23 p21 p22 t2 t3)
    k (CHOICE : t2 = Choice k),
    RefineF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  do 9 intro. revert p11 p12 t1 REFINE1. induction REFINE2.
  - intros. clear LT1. revert k CHOICE t2 p1' SIM. induction REFINE1.
    { intros. econstructor 1; cbv [comp4]; eauto. }
    { inversion 1. }
    { inversion 1. }
    { intros. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; subst. intros. clear CHOICE.
      apply POSTFIX23 in SIM.
      eapply Refine_inv_choiceL with (c := c) in SIM; auto.
      apply RefineF_index_insensitive with (p1' := p1') (p2' := p2) in SIM; auto.
      destruct (obs_ctree (k0 c)).
      1,2,3: eapply BisimF_trans_not_choice; eauto; simpl; auto.
      specialize (IHREFINE1 _ eq_refl). clear k0. admit. }
  - inversion 2.
  - inversion 2.
  - inversion 2.
  - inversion 2; subst.
    apply RefineF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
    clear p12. remember (Some 0) as p12 in REFINE1. revert Heqp12.
    remember (Choice k0) as t2' in REFINE1. revert Heqt2'.
    induction REFINE1.
    { intros; subst. cbv in LT2. destruct p2'; lia. }
    { inversion 1. }
    { inversion 1. }
    { intros; subst. econstructor 4; eauto. }
    { intros; subst. econstructor 5; eauto. }
    { inversion 1; intros; subst; clear_sig.
      specialize (CHOICE c). specialize (IHk c).
      destruct (obs_ctree (k0 c)) eqn:OBS; eauto.
      all: eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  - intros; subst. econstructor 6; eauto.
Abort.

CoFixpoint infND {E R} : CTree E R :=
  {| obs_ctree := Choice (fun _ => infND) |}
.

Variant isInfNDF {E R sim} : CTree' E R → Prop :=
| isInfND_intro k c
  (SIM : sim (obs_ctree (k c)) : Prop)
: isInfNDF (Choice k)
.

Arguments isInfNDF {_ _} _ _.

Lemma isInfNDF_monotone {E R} : monotone1 (@isInfNDF E R).
Proof. repeat intro. destruct IN. econstructor; eauto. Qed.

Hint Resolve isInfNDF_monotone : paco.

Definition isInfND {E R} := paco1 (@isInfNDF E R) bot1.

Lemma infND_refineL {E R1 R2 R} :
  ∀ p1 p2 (t : CTree' E R2) (REFINEL : Refine R p1 p2 (obs_ctree (infND (R := R1))) t),
    isInfND t.
Proof.
  pcofix CIH. do 2 intro. revert p1.
  induction p2 using (well_founded_induction olt_wf).
  rename H into IHp2.
  do 2 intro.
  remember infND as t' eqn:RR.
  rewrite RR in *|-.
  intros. punfold REFINEL. cbv [rel4] in *.
  remember (obs_ctree t') as t1 in REFINEL. revert Heqt1.
  revert p1 p2 t t' REFINEL IHp2 RR. induction 1; intros; subst; simpl in *.
  - pclearbot. eauto.
  - inversion Heqt1.
  - inversion Heqt1.
  - inversion Heqt1.
  - inversion Heqt1; subst. clear_sig.
    simpl in *.
    specialize (IHk 0).
    eauto.
  - pfold. econstructor; eauto. right. eapply CIH.
    pfold. apply REFINEL.
Qed.

