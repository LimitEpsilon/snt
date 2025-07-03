From Coq Require Import Utf8 Lia Eqdep PeanoNat.
From Coq Require Classical. (* don't import just yet *)
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

Definition ret {E R} (r : R) : CTree E R := {| obs_ctree := Ret r |}.
Definition vis {E R A} (e : E A) k : CTree E R := {| obs_ctree := Vis e k |}.
Definition zero {E R} : CTree E R := {| obs_ctree := Zero |}.
Definition choice {E R} k : CTree E R := {| obs_ctree := Choice k |}.

Definition CTree' E R := CTreeF E R (CTree E R).

(*order between extended natural numbers, with None meaning ∞ *)
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

(* maybe omnisemantics will help in the definition also? *)
(* from FreeSim (Stuttering for Free) *)
(* infinite silent steps should be equivalent only to infinite silent steps *)
Inductive SimF {R1 R2 E r sim}
  : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop :=
| sim_prog p1 p2 t1 t2 p1' p2'
  (* only rule that strictly decrements the progress indices*)
  (LT1 : p1' ≺ p1) (LT2 : p2' ≺ p2)
  (SIM : sim p1' p2' t1 t2 : Prop)
: SimF p1 p2 t1 t2
| sim_ret p1 p2 x y
  (RET : r x y : Prop)
: SimF p1 p2 (Ret x) (Ret y)
| sim_vis p1 p2 p1' p2' {A} (e : E A) k1 k2
  (CONT : ∀ a, sim p1' p2' (obs_ctree (k1 a)) (obs_ctree (k2 a)))
: SimF p1 p2 (Vis e k1) (Vis e k2)
| sim_zero p1 p2 t2
: SimF p1 p2 Zero t2
| sim_choiceL p1 p2 p1' t2 k
  (CHOICE : ∀ c, SimF p1' p2 (obs_ctree (k c)) t2)
: SimF p1 p2 (Choice k) t2
| sim_choiceR p1 p2 p2' t1 k
  c (CHOICE : SimF p1 p2' t1 (obs_ctree (k c)))
: SimF p1 p2 t1 (Choice k)
.

Arguments SimF {_ _ _} _ _.

Section IND.
  Context {R1 R2 E} (r : R1 → R2 → Prop) (sim : option nat → option nat → CTree' E R1 → CTree' E R2 → Prop).
  Context (P : ∀ p1 p2 t1 t2, SimF r sim p1 p2 t1 t2 → Prop).
  Context (Pprog : ∀ p1 p2 t1 t2 p1' p2' LT1 LT2 SIM, P _ _ _ _ (sim_prog p1 p2 t1 t2 p1' p2' LT1 LT2 SIM))
          (Pret : ∀ p1 p2 x y RET, P _ _ _ _ (sim_ret p1 p2 x y RET))
          (Pvis : ∀ p1 p2 p1' p2' A (e : E A) k1 k2 CONT, P _ _ _ _ (sim_vis p1 p2 p1' p2' e k1 k2 CONT))
          (Pzero : ∀ p1 p2 t2, P _ _ _ _ (sim_zero p1 p2 t2))
          (PL : ∀ p1 p2 p1' t2 k CHOICE (IHk : ∀ c, P _ _ _ _ (CHOICE c)), P _ _ _ _ (sim_choiceL p1 p2 p1' t2 k CHOICE))
          (PR : ∀ p1 p2 p2' t1 k c CHOICE (IHk : P _ _ _ _ CHOICE), P _ _ _ _ (sim_choiceR p1 p2 p2' t1 k c CHOICE)).
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

Variant TraceF {E : Type → Type} {R : Type} {Trace : Type} :=
| RetTrace (r : R)
| VisTrace {A} (e : E A) (t : A → Trace)
| DivTrace
| Rollback
.

Arguments TraceF : clear implicits.

CoInductive Trace {E R} := mkTrace { obs_trace : TraceF E R Trace }.

Arguments Trace : clear implicits.

Definition Trace' E R := TraceF E R (Trace E R).

Inductive conv {E R} : CTree' E R → Prop :=
| conv_ret r : conv (Ret r)
| conv_vis {A} (e : E A) k : conv (Vis e k)
| conv_zero : conv Zero
| conv_choice k (CONV : ∀ c, conv (obs_ctree (k c))) : conv (Choice k)
.

Scheme conv_ind := Induction for conv Sort Prop.

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

Lemma SimF_monotone_ret R1 R2 E φ φ' (LE : φ <2= φ') :
  @SimF R1 R2 E φ <5= @SimF R1 R2 E φ'.
Proof.
  repeat intro. induction PR.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
Qed.

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

Lemma conv_not_div {E R} (t : CTree' E R) (CONV : conv t) (DIV : div t) : False.
Proof.
  induction CONV; punfold DIV; inversion DIV; subst.
  pclearbot. eauto.
Qed.

Section classical.
  Import Classical.

  Lemma div_or_conv {E R} (t : CTree' E R) : div t ∨ conv t.
  Proof.
    destruct (classic (conv t)) as [?|NCONV]; eauto. left.
    revert t NCONV. pcofix CIH.
    intros. pfold.
    destruct t.
    1,2,3: exfalso; apply NCONV; constructor.
    assert (∃ c, ¬ conv (obs_ctree (k c))) as (c & ?).
    { apply not_all_ex_not. intro. apply NCONV. constructor; auto. }
    econstructor; eauto.
  Qed.
End classical.

Inductive BehF {E R sim} : CTree' E R → (Trace' E R → Prop) :=
| beh_ret v
: BehF (Ret v) (RetTrace v)
| beh_vis {A} (e : E A) k ktr
  (BEH : ∀ a, sim (obs_ctree (k a)) (obs_trace (ktr a)))
: BehF (Vis e k) (VisTrace e ktr)
| beh_zero
: BehF Zero Rollback
| beh_choice k c tr (BEH : BehF (obs_ctree (k c)) tr)
  (NROLLBACK : match tr with Rollback => False | _ => True end)
: BehF (Choice k) tr
| beh_div k c (BEH : sim (obs_ctree (k c)) DivTrace)
: BehF (Choice k) DivTrace
.

Arguments BehF {_ _} _.

Scheme BehF_ind := Induction for BehF Sort Prop.

Lemma BehF_monotone E R : monotone2 (@BehF E R).
Proof.
  repeat intro. induction IN.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
Qed.

Hint Resolve BehF_monotone : paco.

Definition Beh {E R} := paco2 (@BehF E R) bot2.

Lemma Beh_div E R : ∀ t : CTree' E R, Beh t DivTrace → div t.
Proof.
  pcofix CIH.
  intros t BEH. punfold BEH.
  remember DivTrace as tr in BEH. revert Heqtr.
  induction BEH; inversion 1; subst.
  - pfold. econstructor; eauto.
  - pclearbot. pfold. econstructor; eauto.
Qed.

Lemma div_Beh E R : ∀ t : CTree' E R, div t → Beh t DivTrace.
Proof.
  pcofix CIH. intros t DIV. pfold.
  punfold DIV. inversion DIV; subst. pclearbot.
  econstructor 5; eauto.
Qed.

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
  - constructor.
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
    apply sim_prog with (p1' := Some 0) (p2' := Some 0); cbv; eauto.
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
    apply sim_prog with (p1' := Some 0) (p2' := Some 0); cbv; eauto.
    all: instantiate (1 := None); simpl; auto.
  Unshelve. all: exact None.
Qed.

Lemma Bisim_monotone_ret {R E} φ φ' (R_IMPL : ∀ r1 r2, φ r1 r2 → φ' r1 r2) :
  ∀ p1 p2 (t1 t2 : CTree' E R) (BISIM : Bisim φ p1 p2 t1 t2),
    Bisim φ' p1 p2 t1 t2.
Proof.
  pcofix CIH.
  intros. punfold BISIM.
  pfold. destruct BISIM.
  split. eapply SimF_monotone_ret; eauto.
  eapply SimF_monotone; eauto.
  intros. pclearbot. right. eauto.
  eapply SimF_monotone_ret; eauto.
  instantiate (1 := fun r2 r1 => φ r1 r2).
  eauto.
  eapply SimF_monotone; eauto.
  simpl. intros. pclearbot. right. eauto.
Qed.

Lemma Bisim_sym {R1 R2 E} φ :
  ∀ p1 p2 (t1 : CTree' E R1) (t2 : CTree' E R2) (BISIM : Bisim φ p1 p2 t1 t2),
    Bisim (fun r2 r1 => φ r1 r2) p2 p1 t2 t1.
Proof.
  pcofix CIH.
  intros. punfold BISIM. destruct BISIM.
  pfold.
  split; eapply SimF_monotone; eauto; intros; pclearbot; right; eauto.
Qed.

Lemma Sim_inv_retL E R0 R1 R2
  (φ0 : R0 → R2 → Prop) (φ1 : R1 → R2 → Prop) sim0 sim1
  (POSTFIX : sim0 <4= SimF φ0 sim0) :
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
  (φ0 : R0 → R1 → Prop) (φ1 : R0 → R2 → Prop) sim0 sim1
  (POSTFIX : sim0 <4= SimF φ0 sim0) :
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

Lemma Sim_inv_zeroR E R0 R1 R2
  (φ : R0 → R1 → Prop) (φ' : R0 → R2 → Prop) sim sim'
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

Lemma Sim_inv_choiceL E R0 R1 (φ : R0 → R1 → Prop) sim
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

Lemma Sim_inv_divL E R0 R1 (φ : R0 → R1 → Prop) sim
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

#[local] Ltac step :=
  lazymatch goal with
  | |- SimF _ _ _ _ ?t1 ?t2 =>
    lazymatch t1 with
    | Ret _ => lazymatch t2 with Ret _ => apply sim_ret end
    | Vis _ _ =>
      lazymatch t2 with Vis _ _ =>
        apply sim_vis with (p1' := None) (p2' := None); intros; left; pfold
      end
    | Zero => apply sim_zero
    | Choice _ => apply sim_choiceL with (p1' := None); intros
    end; simpl
  end.

#[local] Ltac choose n :=
  apply sim_choiceR with (c := n) (p2' := None); simpl
.

Example gradual_commitment :
  let t1 : CTree' id nat := Choice (fun c =>
    match c with
    | 0 => choice (fun c =>
      match c with
      | 0 => vis 0 ret
      | 1 => vis 1 ret
      | _ => zero
      end)
    | 1 => vis 2 ret
    | _ => zero
    end)
  in
  let t2 : CTree' id nat := Choice (fun c =>
    match c with
    | 0 => vis 0 ret
    | 1 => vis 1 ret
    | 2 => vis 2 ret
    | _ => zero
    end)
  in
  Bisim eq None None t1 t2.
Proof.
  cbn zeta. pfold. split; step.
  - destruct c as [|[|]]; simpl; try step.
    destruct c as [|[|]]; simpl; try step.
    choose 0. step. split; step; auto.
    choose 1. step. split; step; auto.
    choose 2. step. split; step; auto.
  - destruct c as [|[|[|]]]; simpl; try step.
    choose 0. choose 0. step. split; step; auto.
    choose 0. choose 1. step. split; step; auto.
    choose 1. step. split; step; auto.
Qed.

(* why separate φ and sim when sim is enough to express the relation between return values? *)
(* because sim is the argument to the functor *)
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
      apply SimF_index_insensitive with (p1' := p0) (p2' := Some 0) in SIM; auto.
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
      apply SimF_index_insensitive with (p1' := p0) (p2' := Some 0) in SIM; auto.
      remember (Some 0) as o' in SIM. revert Heqo'.
      remember (Choice k) as t2' in SIM. revert Heqt2'.
      induction SIM.
      { intros; subst. cbv in LT3. destruct p2'0; lia. }
      { inversion 1. }
      { inversion 1. }
      { intros. subst. econstructor 4; eauto. }
      { intros. subst. econstructor 5; eauto. }
      { inversion 1; intros; subst. apply (IHk c).
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

Lemma BisimF_trans_conv {R1 R2 R3 E}
  (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) sim12 sim23
  (POSTFIX12 : sim12 <4= SimF (E := E) φ12 sim12)
  (POSTFIX23 : sim23 <4= SimF (E := E) φ23 sim23) :
  ∀ p11 p12 t1 t2 (REFINE1 : SimF (E := E) φ12 sim12 p11 p12 t1 t2)
    p21 p22 t3 (REFINE2 : SimF (E := E) φ23 sim23 p21 p22 t2 t3)
    (CONV : conv t2),
    SimF (comp2 φ12 φ23) (comp4 sim12 sim23) p11 p22 t1 t3.
Proof.
  intros. revert p11 p12 t1 REFINE1 p21 p22 t3 REFINE2. induction CONV.
  { intros. eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  { intros. eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  { intros. eapply BisimF_trans_not_choice; eauto; simpl; auto. }
  rename H into IHt2. clear CONV.
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
      eapply Sim_inv_choiceL with (c := c) in SIM; auto.
      apply SimF_index_insensitive with (p1' := p1') (p2' := p2) in SIM; eauto. }
  - inversion 2.
  - inversion 2.
  - inversion 2.
  - inversion 2; subst. clear CHOICE0.
    apply SimF_index_insensitive with (p1' := p11) (p2' := Some 0) in REFINE1; auto.
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

Inductive observable {R E} : CTree' E R → {A & E A} → Prop :=
| obs_vis {A} (e : E A) k
: observable (Vis e k) (existT _ _ e)
| obs_choice k c ev
  (OBS : observable (obs_ctree (k c)) ev)
: observable (Choice k) ev
.

Scheme observable_ind := Induction for observable Sort Prop.

Lemma SimF_observable {R1 R2 E} (φ : R1 → R2 → Prop) sim
  (POSTFIX : sim <4= SimF (E := E) φ sim) :
  ∀ t1 ev (OBS : observable t1 ev)
    p1 p2 t2 (REFINE : SimF φ sim p1 p2 t1 t2),
    observable t2 ev.
Proof.
  induction 1.
  - intros.
    apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2) in REFINE; auto.
    clear p1. remember (Some 0) as p1 in REFINE. revert Heqp1.
    remember (Vis e k) as t1 in REFINE. revert Heqt1.
    induction REFINE.
    { intros; subst. cbv in LT1. destruct p1'; lia. }
    { inversion 1. }
    { inversion 1; intros; subst; clear_sig. constructor. }
    { inversion 1. }
    { inversion 1. }
    { intros; subst. econstructor 2; eauto. }
  - intros.
    apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2) in REFINE; auto.
    clear p1. remember (Some 0) as p1 in REFINE. revert Heqp1.
    remember (Choice k) as t1 in REFINE. revert Heqt1.
    induction REFINE.
    { intros; subst. cbv in LT1. destruct p1'; lia. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1. }
    { inversion 1; intros; subst. eauto. }
    { intros; subst. econstructor 2; eauto. }
Qed.

CoFixpoint s1 n : CTree id nat := choice (fun c =>
  match c with
  | 0 => vis n ret
  | 1 => s1 (S n)
  | _ => zero
  end).

CoFixpoint s2 n : CTree id nat := choice (fun c =>
  match c with
  | 0 => vis n ret
  | 1 => vis (S n) ret
  | 2 => s2 (S (S n))
  | _ => zero
  end).

Lemma observable_s2n :
  ∀ n ev (OBS : observable (obs_ctree (s2 n)) ev),
    ∃ m, n ≤ m ∧ ev = existT _ _ m.
Proof.
  intros.
  remember (obs_ctree (s2 n)) as t in OBS.
  assert (∃ k, n ≤ k ∧ t = obs_ctree (s2 k)). { eauto. }
  clear Heqt. rename H into Heqt.
  revert Heqt.
  induction OBS; intros (o & LE & EQ).
  - inversion EQ.
  - simpl in EQ. inversion EQ; subst.
    destruct c as [|[|[|]]].
    { simpl in *. inversion OBS; subst; clear_sig. eauto. }
    { simpl in *. inversion OBS; subst; clear_sig. eauto. }
    { eapply IHOBS. eauto. }
    { simpl in *. inversion OBS. }
Qed.

Lemma s1n_bisim_s2n
  : ∀ n p1 p2, Bisim eq p1 p2 (obs_ctree (s1 n)) (obs_ctree (s2 n)).
Proof.
  pcofix CIH.
  intros. simpl. pfold. split.
  - step.
    destruct c as [|[|]]; simpl. 3: step.
    choose 0. step. split; step; auto.
    step.
    destruct c as [|[|]]; simpl. 3: step.
    choose 1. step. split; step; auto.
    choose 2. econstructor 1.
    1,2: instantiate (1 := Some 0); simpl; auto.
    right. apply (CIH (S (S n))).
  - step.
    destruct c as [|[|[|]]]; simpl. 4: step.
    choose 0. step. split; step; auto.
    choose 1. choose 0. step. split; step; auto.
    choose 1. choose 1. econstructor 1.
    1,2: instantiate (1 := Some 0); simpl; auto.
    right. apply (CIH (S (S n))).
Qed.

Lemma s2_different_parity : ∀ p1 p2 t1 t2,
  SimF eq (upaco4 (BisimF eq) bot4) p1 p2 t1 t2 →
  ∀ m n (PARITY : (Nat.Even m ∧ Nat.Odd n) ∨ (Nat.Odd m ∧ Nat.Even n)),
  t1 = obs_ctree (s2 m) →
  t2 = obs_ctree (s2 n) →
  False.
Proof.
  assert (upaco4 (BisimF eq) bot4 <4=
    @SimF nat nat id eq (upaco4 (BisimF eq) bot4))
    as POSTFIX.
  { intros. pclearbot. punfold PR. eapply PR. }
  induction 1; intros; subst.
  - pclearbot. (* either m < n or n < m, which makes Bisim impossible *)
    punfold SIM. destruct SIM.
    assert (observable (obs_ctree (s2 m)) (existT _ _ m)) as OBSm.
    { simpl. econstructor 2. instantiate (1 := 0). simpl. constructor. }
    assert (observable (obs_ctree (s2 n)) (existT _ _ n)) as OBSn.
    { simpl. econstructor 2. instantiate (1 := 0). simpl. constructor. }
    assert (m ≠ n).
    { destruct (Nat.eq_dec m n); eauto. subst.
      destruct PARITY as [(? & ?)|(? & ?)]; intro;
      eapply Nat.Even_Odd_False; eauto. }
    assert (m < n ∨ n < m) as [LT | LT] by lia.
    { eapply SimF_observable in OBSm; eauto.
      eapply observable_s2n in OBSm.
      destruct OBSm as (? & ? & ?). clear_sig. lia. }
    { eapply SimF_observable in OBSn.
      3: exact H0.
      eapply observable_s2n in OBSn.
      destruct OBSn as (? & ? & ?). clear_sig. lia.
      simpl. intros. pclearbot. eapply Bisim_sym in PR.
      punfold PR. destruct PR.
      eapply SimF_monotone; try eassumption.
      intros. pclearbot.
      left. apply Bisim_sym in PR. eauto. }
  - inversion H.
  - inversion H.
  - inversion H.
  - simpl in H. inversion H; subst.
    specialize (IHk 2 (S (S m)) n).
    eapply IHk; eauto.
    destruct PARITY as [(? & ?)|(? & ?)].
    left. split; auto. destruct H0; subst. exists (S x). simpl. lia.
    right. split; auto. destruct H0; subst. exists (S x). simpl. lia.
  - simpl in *. inversion H1; subst.
    destruct c as [|[|[|]]]; simpl in H.
    { eapply Sim_inv_choiceL with (c := 0) in H; eauto.
      eapply SimF_index_insensitive with (p1' := Some 0) (p2' := p2') in H; auto.
      inversion H; subst; clear_sig.
      cbv in LT1. destruct p1'; lia.
      destruct PARITY as [(? & ?)|(? & ?)].
      eapply Nat.Even_Odd_False; eauto.
      eapply Nat.Even_Odd_False; eauto. }
    { eapply Sim_inv_choiceL with (c := 1) in H; eauto.
      apply SimF_index_insensitive with (p1' := Some 0) (p2' := p2') in H; auto.
      inversion H; subst; clear_sig.
      cbv in LT1. destruct p1'; lia.
      inversion H5; subst.
      destruct PARITY as [(? & ?)|(? & ?)].
      eapply Nat.Even_Odd_False; eauto.
      eapply Nat.Even_Odd_False; eauto. }
    specialize (IHSimF m (S (S n))).
    eapply IHSimF; eauto.
    destruct PARITY as [(? & ?)|(? & ?)].
    left. split; auto. destruct H2; subst. exists (S x). simpl. lia.
    right. split; auto. destruct H2; subst. exists (S x). simpl. lia.
    eapply Sim_inv_choiceL in H; eauto.
    instantiate (1 := 0) in H. simpl in H.
    eapply SimF_index_insensitive with (p1' := Some 0) (p2' := p2') in H; auto.
    inversion H; subst. cbv in LT1. destruct p1'; lia.
Qed.

Lemma not_trans_aux : ∀ p1 p2 t1 t2,
  SimF eq (upaco4 (BisimF eq) bot4) p1 p2 t1 t2 →
  ∀ n,
    p1 = Some 0 →
    t1 = Choice (fun c =>
      match c with
      | 0 => vis n ret
      | 1 => s2 (S n)
      | _ => zero
      end) →
    t2 = obs_ctree (s2 n) →
    False.
Proof.
  assert (upaco4 (BisimF eq) bot4 <4=
    @SimF nat nat id eq (upaco4 (BisimF eq) bot4))
    as POSTFIX.
  { intros. pclearbot. punfold PR. eapply PR. }
  induction 1; intros; subst.
  - cbv in LT1. destruct p1'; lia.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - inversion H0; subst.
    specialize (CHOICE 1). cbn match in CHOICE.
    eapply s2_different_parity; eauto.
    destruct (Nat.Even_Odd_dec n).
    right. split; auto. destruct e; subst. exists x; lia.
    left. split; auto. destruct o; subst. exists (S x); lia.
  - simpl in *. inversion H2; subst.
    destruct c as [|[|[|]]]; simpl in *.
    { eapply Sim_inv_choiceL with (c := 1) in H; eauto.
      simpl in H.
      eapply Sim_inv_choiceL with (c := 0) in H; eauto.
      simpl in H.
      inversion H; subst; clear_sig.
      cbv in LT1. destruct p1'; lia.
      lia. }
    { eapply Sim_inv_choiceL with (c := 1) in H; eauto.
      simpl in H.
      eapply Sim_inv_choiceL with (c := 1) in H; eauto.
      simpl in H.
      inversion H; subst; clear_sig.
      cbv in LT1. destruct p1'; lia.
      lia. }
    { eapply Sim_inv_choiceL with (c := 1) in H; eauto.
      simpl in H.
      eapply s2_different_parity; eauto.
      2: instantiate (1 := S n); auto.
      2: instantiate (1 := S (S n)); auto.
      destruct (Nat.Even_Odd_dec (S n)).
      left. split; auto. destruct e as (? & ->). exists x; lia.
      right. split; auto. destruct o as (? & ->). exists (S x); lia. }
    { eapply Sim_inv_choiceL with (c := 0) in H; eauto.
      simpl in H.
      inversion H.
      cbv in LT1. destruct p1'; lia. }
Qed.

(*
         1   3   5                1      3                1   3   5
t1 = ---/---/---/--- ... t2 = ---/------/--- ... t3 = ---/---/---/--- ...
            \   \                    \      \            \   \   \
             2   4                    2      4            2   4   6
*)
Example not_trans :
  let t1 := Choice (fun c =>
    match c with
    | 0 => vis 1 ret
    | 1 => s2 2
    | _ => zero
    end) in
  let t2 := obs_ctree (s1 1) in
  let t3 := obs_ctree (s2 1) in
  Bisim eq None None t1 t2 ∧
  Bisim eq None None t2 t3 ∧
  ¬ Bisim eq None None t1 t3.
Proof.
  cbn zeta.
  split. { pfold. split.
    { step. destruct c as [|[|]]; simpl.
      choose 0. step. split; step; auto.
      choose 1. pose proof (s1n_bisim_s2n 2 None None). punfold H.
      destruct H; simpl in *.
      eapply SimF_monotone_ret.
      instantiate (1 := (fun r2 r1 => r1 = r2)). eauto.
      eapply SimF_monotone; try eassumption. simpl.
      intros. pclearbot. left.
      eapply Bisim_sym in PR.
      eapply Bisim_monotone_ret; try eassumption.
      eauto.
      econstructor 4; eauto. }
    { simpl. step. destruct c as [|[|]]; simpl.
      choose 0. step. split; step; auto.
      choose 1. pose proof (s1n_bisim_s2n 2 None None). punfold H.
      destruct H; simpl in *.
      eapply SimF_monotone_ret.
      instantiate (1 := eq). eauto.
      eapply SimF_monotone; try eassumption. simpl.
      intros. pclearbot. left.
      eapply Bisim_sym in PR.
      eapply Bisim_monotone_ret; try eassumption.
      eauto.
      econstructor 4; eauto. } }
  split. { apply s1n_bisim_s2n. }
  repeat intro.
  apply Bisim_index_insensitive with (p1' := Some 0) (p2' := None) in H.
  punfold H.
  destruct H as (CONTRA & _).
  eapply not_trans_aux; eauto.
Qed.

