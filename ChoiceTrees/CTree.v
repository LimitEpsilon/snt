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
| Choice c (k : ∀ n, n < c → CTree)
.

Arguments CTreeF : clear implicits.

CoInductive CTree {E : Type → Type} {R : Type} :=
  mkCTree { obs_ctree : CTreeF E R CTree }
.

Arguments CTree : clear implicits.

Definition ret {E R} r : CTree E R :=
  {| obs_ctree := Ret r |}
.
Definition vis {E R A} (e : E A) k : CTree E R :=
  {| obs_ctree := Vis e k |}
.
Definition choice {E R} c k : CTree E R :=
  {| obs_ctree := Choice c k |}
.

(* order between extended natural numbers, with None meaning ∞ *)
Definition olt (x y : option nat) :=
  match x, y with
  | Some m, Some n => m < n
  | None, _ => False
  | _, None => True
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

(* from FreeSim (Stuttering for Free) *)
Inductive RefineF {R1 R2 E r sim}
  : option nat → option nat → CTree E R1 → CTree E R2 → Prop :=
| refine_prog o1 o2 t1 t2 o1' o2'
  (* only rule that strictly decrements the progress indices*)
  (LT1 : o1' ≺ o1) (LT2 : o2' ≺ o2)
  (SIM : sim o1' o2' t1 t2)
: RefineF o1 o2 t1 t2
| refine_ret o1 o2 t1 t2 x y
  (OBS1 : obs_ctree t1 = Ret x) (OBS2 : obs_ctree t2 = Ret y)
  (RET : r x y : Prop)
: RefineF o1 o2 t1 t2
| refine_vis o1 o2 t1 t2 {A} (e : E A) k1 k2
  (OBS1 : obs_ctree t1 = Vis e k1) (OBS2 : obs_ctree t2 = Vis e k2)
  (CONT : ∀ a, sim None None (k1 a) (k2 a))
: RefineF o1 o2 t1 t2
| refine_choiceL o1 o2 t1 t2 c k
  (OBS1 : obs_ctree t1 = Choice c k)
  (CHOICE : ∀ n (LT : n < c), RefineF None o2 (k n LT) t2)
: RefineF o1 o2 t1 t2
| refine_choiceR o1 o2 t1 t2 c k
  (OBS2 : obs_ctree t2 = Choice c k)
  n LT (CHOICE : RefineF o1 None t1 (k n LT))
: RefineF o1 o2 t1 t2
.

Arguments RefineF {_ _ _} _ _.

Section IND.
  Context {R1 R2 E} (r : R1 → R2 → Prop) (sim : option nat → option nat → CTree E R1 → CTree E R2 → Prop).
  Context (P : ∀ o1 o2 t1 t2, RefineF r sim o1 o2 t1 t2 → Prop).
  Context (Pprog : ∀ o1 o2 t1 t2 o1' o2' LT1 LT2 SIM, P _ _ _ _ (refine_prog o1 o2 t1 t2 o1' o2' LT1 LT2 SIM))
          (Pret : ∀ o1 o2 t1 t2 x y OBS1 OBS2 RET, P _ _ _ _ (refine_ret o1 o2 t1 t2 x y OBS1 OBS2 RET))
          (Pvis : ∀ o1 o2 t1 t2 A (e : E A) k1 k2 OBS1 OBS2 CONT, P _ _ _ _ (refine_vis o1 o2 t1 t2 e k1 k2 OBS1 OBS2 CONT))
          (PL : ∀ o1 o2 t1 t2 c k OBS1 CHOICE (IHk : ∀ n LT, P _ _ _ _ (CHOICE n LT)), P _ _ _ _ (refine_choiceL o1 o2 t1 t2 c k OBS1 CHOICE))
          (PR : ∀ o1 o2 t1 t2 c k OBS2 n LT CHOICE (IHk : P _ _ _ _ CHOICE), P _ _ _ _ (refine_choiceR o1 o2 t1 t2 c k OBS2 n LT CHOICE)).
  Fixpoint RefineF_ind o1 o2 t1 t2 pf : P o1 o2 t1 t2 pf.
  Proof.
    destruct pf.
    - apply Pprog.
    - apply Pret.
    - apply Pvis.
    - apply PL. intros. apply RefineF_ind.
    - apply PR. intros. apply RefineF_ind.
  Qed.
End IND.

Definition BisimF {R1 R2 E} (φ : R1 → R2 → Prop) sim o1 o2 t1 t2 :=
  RefineF (E := E) φ sim o1 o2 t1 t2 ∧
  RefineF
    (fun r2 r1 => φ r1 r2)
    (fun o2 o1 t2 t1 => sim o1 o2 t1 t2)
    o2 o1 t2 t1
.

Lemma RefineF_monotone R1 R2 E r : monotone4 (@RefineF R1 R2 E r).
Proof.
  repeat intro. revert r' LE. induction IN; intros.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
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

Definition comp {R1 R2 R3 : Type}
  (r12 : R1 → R2 → Prop) (r23 : R2 → R3 → Prop) v1 v3 :=
  ∃ v2, r12 v1 v2 ∧ r23 v2 v3
.

Lemma RefineF_index_mono {R1 R2 E} φ (sim : _ → _ → _ → _ → Prop) :
  ∀ o1 o2 (t1 : CTree E R1) (t2 : CTree E R2) (REFINE : RefineF φ sim o1 o2 t1 t2)
    o1' o2' (LE1 : o1 ≼ o1') (LE2 : o2 ≼ o2'),
    RefineF φ sim o1' o2' t1 t2.
Proof.
  do 4 intro. induction 1.
  - intros o1'' o2'' ? ?.
    econstructor 1; eauto.
    destruct LE1; subst; eauto. eapply olt_transitive; eauto.
    destruct LE2; subst; eauto. eapply olt_transitive; eauto.
  - intros. econstructor 2; eauto.
  - intros. econstructor 3; eauto.
  - intros. econstructor 4; eauto.
    intros. eapply IHk; eauto. right; auto.
  - intros. econstructor 5; eauto.
    intros. eapply IHREFINE; eauto. right; auto.
Qed.

Lemma RefineF_inv_choiceR {R1 R2 E φ sim} (POSTFIX : sim <4= RefineF φ sim) :
  ∀ o1 o2 (t1 : CTree E R1) (t2' : CTree E R2)
    (* if t1 refines t2', *)
    (REFINE : RefineF φ sim o1 o2 t1 t2')
    (* for any t2 that may continue as t2', *)
    t2 c2 k2 (OBS : obs_ctree t2 = Choice c2 k2) n2 LT2 (BR : t2' = k2 n2 LT2)
    (* t1 must refine t2 *)
    o1' o2', RefineF φ sim o1' o2' t1 t2.
Proof.
  induction o1 using (well_founded_induction olt_wf).
  rename H into IHo1.
  do 4 intro. revert IHo1.
  induction REFINE.
  - eauto.
  - intros. econstructor 5; eauto. rewrite <- BR.
    econstructor 2; eauto.
  - intros. econstructor 5; eauto. rewrite <- BR.
    econstructor 3; eauto.
  - intros. econstructor 5; eauto. rewrite <- BR.
    econstructor 4; eauto. intros. eapply RefineF_index_mono; eauto.
    { right; auto. }
    { destruct o2; cbv; auto. }
  - intros. econstructor 5; eauto. rewrite <- BR.
    eauto.
Qed.

Lemma RefineF_index_insensitive {R1 R2 E φ sim} (POSTFIX : sim <4= RefineF φ sim) :
  ∀ o1 o2 (t1 : CTree E R1) (t2 : CTree E R2) (REFINE : RefineF φ sim o1 o2 t1 t2)
    o1' o2',
    RefineF φ sim o1' o2' t1 t2.
Proof.
  do 2 intro. revert o1.
  induction o2 using (well_founded_induction olt_wf).
  rename H into IHo2.
  do 4 intro. revert IHo2.
  induction REFINE.
  - eauto.
  - intros. econstructor 2; eauto.
  - intros. econstructor 3; eauto.
  - intros. econstructor 4; eauto.
  - intros.
    pose proof (RefineF_inv_choiceR POSTFIX o1 None t1 (k n LT)); eauto.
Qed.

Definition Refine_index_insensitive {R1 R2 E} φ :
  ∀ o1 o2 (t1 : CTree E R1) (t2 : CTree E R2) (REFINE : Refine φ o1 o2 t1 t2)
    o1' o2',
    Refine φ o1' o2' t1 t2.
Proof.
  pose proof (RefineF_index_insensitive (E := E) (Refine_postfix φ)).
  intros. punfold REFINE. pfold.
  eapply RefineF_monotone.
  { eapply H. eapply RefineF_monotone; eauto. intros. pclearbot. auto. }
  eauto.
Qed.

Lemma Refine_refl {R E} φ (R_REFL : ∀ v, φ v v) :
  ∀ o1 o2 (t : CTree E R), Refine φ o1 o2 t t.
Proof.
  pcofix CIH.
  intros. pfold. destruct (obs_ctree t) eqn:OBS.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto. intros.
    econstructor 5; eauto. instantiate (1 := LT).
    apply refine_prog with (o1' := Some 0) (o2' := Some 0); cbv; eauto.
Qed.

Lemma Refine_inv_retL E R0 R1 R2 (φ0 : R0 → R2 → Prop) (φ1 : R1 → R2 → Prop) :
  ∀ o0 o1 t0 t1 (REFINE : Refine (E := E) φ0 o0 o1 t0 t1) t0' r0 r1
    (IMPL: ∀ r2, φ0 r0 r2 → φ1 r1 r2)
    (OBS0 : obs_ctree t0 = Ret r0)
    (OBS0' : obs_ctree t0' = Ret r1),
    Refine (E:=E) φ1 o0 o1 t0' t1.
Proof.
  pcofix CIH.
  do 5 intro. punfold REFINE. induction REFINE.
  - intros. pclearbot. pfold. econstructor 1; eauto.
  - rewrite OBS1. inversion 2; subst. intros.
    pfold. econstructor 2; eauto.
  - rewrite OBS1. inversion 2.
  - rewrite OBS1. inversion 2.
  - intros. pfold. econstructor 5; eauto.
    exploit IHREFINE; eauto. intros. punfold H.
Qed.

Lemma Refine_inv_retR E R0 R1 R2 (φ0 : R0 → R1 → Prop) (φ1 : R0 → R2 → Prop) :
  ∀ o0 o1 t0 t1 (REFINE : Refine (E := E) φ0 o0 o1 t0 t1) t1' r1 r2
    (IMPL: ∀ r0, φ0 r0 r1 → φ1 r0 r2)
    (OBS0 : obs_ctree t1 = Ret r1)
    (OBS0' : obs_ctree t1' = Ret r2),
    Refine (E:=E) φ1 o0 o1 t0 t1'.
Proof.
  pcofix CIH.
  do 5 intro. punfold REFINE. induction REFINE.
  - intros. pclearbot. pfold. econstructor 1; eauto.
  - rewrite OBS2. inversion 2; subst. intros.
    pfold. econstructor 2; eauto.
  - rewrite OBS2. inversion 2.
  - intros. pfold. econstructor 4; eauto. intros.
    exploit IHk; eauto. intros. punfold H.
  - rewrite OBS2. inversion 2.
Qed.

Lemma Refine_inv_choiceL E R0 R1 (φ : R0 → R1 → Prop) :
  ∀ o0 o1 t0 t1 (REFINE : Refine (E := E) φ o0 o1 t0 t1) c k
    (OBS0 : obs_ctree t0 = Choice c k)
    n LT,
    Refine (E:=E) φ o0 o1 (k n LT) t1.
Proof.
  pcofix CIH.
  do 5 intro. punfold REFINE. induction REFINE.
  - intros. pclearbot. pfold. econstructor 1; eauto.
  - rewrite OBS1. inversion 1.
  - rewrite OBS1. inversion 1.
  - rewrite OBS1. inversion 1; subst; clear_sig.
    intros. apply paco4_mon with (r := bot4).
    eapply Refine_index_insensitive; pfold; eauto.
    destruct 1.
  - intros. pfold. econstructor 5; eauto.
    exploit IHREFINE; eauto. intros. punfold H.
Qed.

Lemma Refine_trans {R1 R2 R3 E} (φ12 : R1 → R2 → Prop) (φ23 : R2 → R3 → Prop) :
  ∀ o11 o12 t1 t2 (REFINE1 : Refine (E := E) φ12 o11 o12 t1 t2)
    o21 o22 t3 (REFINE2 : Refine (E := E) φ23 o21 o22 t2 t3),
    Refine (E := E) (comp φ12 φ23) o11 o22 t1 t3.
Proof.
  pcofix CIH.
  do 5 intro. punfold REFINE1. induction REFINE1.
  - pclearbot. do 4 intro. revert t1 SIM. punfold REFINE2. induction REFINE2.
    { pclearbot. intros. pfold. econstructor 1; eauto. }
    { intros. eapply paco4_mon.
      eapply Refine_inv_retR with (r1 := x) (r2 := y); eauto.
      eapply Refine_index_insensitive; eauto.
      cbv [comp]; eauto.
      destruct 1. }
    { intros.
      apply Refine_index_insensitive with (o1' := Some 0) (o2' := Some 0) in SIM.
      remember (Some 0) as o' in SIM. revert Heqo'.
      punfold SIM. induction SIM.
      { intros; subst. cbv in LT3. destruct o2'0; lia. }
      { rewrite OBS1 in *. inversion OBS3. }
      { rewrite OBS1 in *. inversion OBS3; subst. clear_sig.
        intros. pfold. econstructor 3; eauto. intros.
        left. pfold.
        econstructor 1; eauto. 1, 2: instantiate (1 := Some 0); cbv; auto.
        right.
        eapply CIH with (o12 := None) (o21 := None);
        try unshelve eapply Refine_index_insensitive; try exact None;
        pfold.
        { exploit CONT0; eauto. intros. pclearbot. punfold H. }
        { exploit CONT; eauto. intros. pclearbot. punfold H. } }
      { intros. subst. pfold. econstructor 4; eauto. intros.
        exploit IHk; eauto. instantiate (1 := LT).
        intros. punfold H. eapply RefineF_index_mono; eauto.
        { destruct o1; cbv; auto. } { destruct o3; cbv; auto. } }
      { rewrite OBS1 in *. inversion OBS0. } }
    { intros.
      apply Refine_index_insensitive with (o1' := Some 0) (o2' := Some 0) in SIM.
      remember (Some 0) as o' in SIM. revert Heqo'.
      punfold SIM. induction SIM.
      { intros; subst. cbv in LT3. destruct o2'0; lia. }
      { rewrite OBS1 in *. inversion OBS2. }
      { rewrite OBS1 in *. inversion OBS2. }
      { intros. subst. pfold. econstructor 4; eauto. intros.
        exploit IHk0; eauto. instantiate (1 := LT).
        intros. punfold H. eapply RefineF_index_mono; eauto.
        { destruct o1; cbv; auto. } { destruct o3; cbv; auto. } }
      { intros; subst. rewrite OBS1 in *. inversion OBS2; subst. clear_sig.
        eapply IHk. instantiate (1 := LT).
        eapply Refine_index_insensitive; pfold; eassumption. } }
    { intros. pfold. econstructor 5; eauto. instantiate (1 := LT).
      exploit IHREFINE2; eauto. intros. punfold H. }
  - intros. apply paco4_mon with (r := bot4).
    eapply Refine_index_insensitive. eapply Refine_inv_retL in REFINE2; eauto.
    { cbv [comp]. eauto. }
    { destruct 1. }
  - intros.
    apply Refine_index_insensitive with (o1' := o1) (o2' := o22) in REFINE2.
    punfold REFINE2. induction REFINE2.
    { pfold. econstructor 1; eauto. pclearbot. right. eapply CIH; eauto.
      instantiate (1 := None).
      pfold. econstructor 3; eauto. }
    { rewrite OBS2 in *. inversion OBS0. }
    { rewrite OBS2 in *. inversion OBS0; subst; clear_sig.
      pfold. econstructor 3; eauto. intros. left. pfold. econstructor 1; eauto.
      1, 2: instantiate (1 := Some 0); cbv; auto.
      right.
      eapply CIH; apply Refine_index_insensitive with (o1 := None) (o2 := None);
      pfold; eauto.
      - exploit CONT; eauto. intros. pclearbot. punfold H.
      - exploit CONT0; eauto. intros. pclearbot. punfold H.
      Unshelve. all: exact None. }
    { rewrite OBS2 in *. inversion OBS0. }
    { intros. pfold. econstructor 5; eauto. exploit IHREFINE2; eauto.
      intros. punfold H. }
  - intros. pfold. econstructor 4; eauto. intros.
    exploit IHk; eauto. instantiate (1 := LT).
    intros. punfold H.
  - intros. eapply IHREFINE1. eapply Refine_inv_choiceL in REFINE2; eauto.
Qed.

CoFixpoint infND {E R} : CTree E R :=
  choice 2 (fun _ _ => infND)
.

Variant isInfNDF {E R sim} {t : CTree E R} : Prop :=
| isInfND_intro c k n LT
  (OBS : obs_ctree t = Choice c k)
  (SIM : sim (k n LT) : Prop)
.

Arguments isInfNDF {_ _} _ _.

Lemma isInfNDF_monotone {E R} : monotone1 (@isInfNDF E R).
Proof. repeat intro. destruct IN. econstructor; eauto. Qed.

Hint Resolve isInfNDF_monotone : paco.

Definition isInfND {E R} := paco1 (@isInfNDF E R) bot1.

Lemma infND_refineL {E R1 R2 R} :
  ∀ o1 o2 (t : CTree E R2) (REFINEL : Refine R o1 o2 (infND (R := R1)) t),
    isInfND t.
Proof.
  pcofix CIH. do 2 intro. revert o1.
  induction o2 using (well_founded_induction olt_wf).
  rename H into IHo2.
  do 2 intro.
  remember infND as t' eqn:RR.
  rewrite RR in *|-.
  intros. punfold REFINEL. cbv [rel4] in *.
  revert o1 o2 t t' REFINEL IHo2 RR. induction 1; intros; subst.
  - pclearbot. eauto.
  - inversion OBS1.
  - inversion OBS1.
  - inversion OBS1; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H1;
    [subst|apply PeanoNat.Nat.eq_dec].
    simpl in *.
    eauto.
  - pfold. econstructor; eauto. right. eapply CIH.
    pfold. apply REFINEL.
Qed.

