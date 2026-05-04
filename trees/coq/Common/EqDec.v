(*! Utilities | Decidable equality typeclass !*)
Require Import Stdlib.Strings.String.
Import EqNotations.

Class EqDec (T: Type) :=
  mkEqDec { eq_dec: forall t1 t2: T, { t1 = t2 } + { t1 <> t2 } }.

Definition beq_dec {A} `{EqDec A} a1 a2 : bool :=
  if eq_dec a1 a2 then true else false.

Section UIP.
  Context {A : Type}.
  Context `{EqDec A}.
  Context {x : A}.

  Definition nu {y : A} (u : x = y) : x = y :=
    match eq_dec x y with
    | left eqxy => eqxy
    | right neqxy => False_ind _ (neqxy u)
    end.

  Lemma nu_constant {y : A} (u v : x = y) : nu u = nu v.
  Proof. cbv [nu]. destruct (eq_dec x y); eauto. exfalso; eauto. Qed.

  Let comp {x y y' : A} (eq1 : x = y) (eq2 : x = y') : y = y' := eq_trans (eq_sym eq1) eq2.

  Definition nu_inv {y : A} (v : x = y) : x = y := eq_trans (eq_sym (nu (eq_refl x))) v.

  Remark nu_left_inv_on {y : A} (u : x = y) : nu_inv (nu u) = u.
  Proof. destruct u; cbv [nu nu_inv eq_trans eq_rect]. destruct (eq_dec x x); eauto. destruct e. eauto. exfalso; eauto. Qed.

  Theorem UIP_dec {y : A} (p1 p2 : x = y) : p1 = p2.
  Proof.
    erewrite <- (nu_left_inv_on p1).
    erewrite <- (nu_left_inv_on p2).
    erewrite (nu_constant p1 p2). eauto.
  Qed.

  Lemma UIP_nu {y : A} (p : x = y) : p = nu p.
  Proof. eapply UIP_dec. Qed.

  Theorem K_dec_on (P : x = x -> Prop) (H' : P (eq_refl x)) (p : x = x) : P p.
  Proof. erewrite UIP_dec. eapply H'. Qed.
End UIP.

Section DepEq.
  Context {A : Type}.
  Context `{EqDec A}.

  Let proj {x : A} (P : A -> Type) (exP : sigT P) (def : P x) : P x :=
    match exP with
    | existT _ x' prf =>
      match eq_dec x x' with
      | left eqprf => eq_rect x' P prf x (eq_sym eqprf)
      | _ => def
      end
    end.

  Lemma inj_pair2 (P : A -> Type) (p : A) (x y : P p) :
    existT P p x = existT P p y -> x = y.
  Proof.
    intro EQsig.
    apply (f_equal (fun s => proj P s x)) in EQsig.
    cbn in EQsig. destruct (eq_dec p p).
    eapply (K_dec_on
      (fun Heq =>
        rew [P] eq_sym Heq in x = rew [P] eq_sym Heq in y ->
        x = y
      ) (fun H => H) e). eauto.
    exfalso. eauto.
  Qed.
End DepEq.

Lemma beq_dec_true {A} (EQ : EqDec A) a1 a2 :
  beq_dec a1 a2 = true -> a1 = a2.
Proof.
  unfold beq_dec; destruct eq_dec; subst; eauto; discriminate.
Qed.

Lemma beq_dec_false {A} (EQ : EqDec A) a1 a2 :
  beq_dec a1 a2 = false -> a1 <> a2.
Proof.
  unfold beq_dec; destruct eq_dec; subst; eauto; discriminate.
Qed.

Lemma beq_dec_iff {A} (EQ : EqDec A) a1 a2 :
  beq_dec a1 a2 = true <-> a1 = a2.
Proof.
  unfold beq_dec; destruct eq_dec; subst.
  - firstorder.
  - split; intro; (eauto || congruence).
Qed.

Lemma beq_dec_false_iff {A} (EQ : EqDec A) a1 a2 :
  beq_dec a1 a2 = false <-> a1 <> a2.
Proof.
  unfold beq_dec; destruct eq_dec; subst; intuition congruence.
Qed.

Hint Extern 2 (EqDec _) => econstructor; decide equality : typeclass_instances.
Hint Extern 1 ({ _ = _ } + { _ <> _ }) => apply eq_dec : typeclass_instances.

Instance EqDec_bool : EqDec bool := _.
Instance EqDec_ascii : EqDec Ascii.ascii := _.
Instance EqDec_string : EqDec string := _.
Instance EqDec_unit : EqDec unit := _.
Instance EqDec_nat : EqDec nat := {| eq_dec := PeanoNat.Nat.eq_dec |}.
Instance EqDec_pair A B `{EqDec A} `{EqDec B} : EqDec (A * B) := _.
Instance EqDec_option A `{EqDec A} : EqDec (option A) := _.
Instance EqDec_eq_true {A} (f: A -> bool) (a: A) : EqDec (f a = true).
Proof. constructor; left. apply UIP_dec. Qed.
Instance EqDec_comparison : EqDec comparison := _.
Instance EqDec_list A `{EqDec A} : EqDec (list A) := {| eq_dec := List.list_eq_dec eq_dec |}.

Lemma eq_dec_rew_type_family {T} {EQ : EqDec T} (family : T -> Type):
  forall (t : T) (Heq : t = t) (a : family t),
    rew Heq in a = a.
Proof.
  intros.
  assert (Heq = eq_refl) as -> by (apply UIP_dec).
  reflexivity.
Qed.

Lemma eq_rect_eqdec_irrel {A} {EQ : EqDec A} (x : A) {P : A -> Type} {px : P x} {y : A} :
  forall (pr2 pr1 : x = y),
    eq_rect x P px y pr1 = eq_rect x P px y pr2.
Proof.
  destruct pr1; cbn; intros.
  symmetry; apply eq_dec_rew_type_family.
Qed.

Lemma eq_rect_eqdec_irrel2 {A} {EQ : EqDec A} (x : A) {P : A -> Type} {px py : P x} {y : A}:
  forall (pr2 pr1: x = y),
    px = py ->
    eq_rect x P px y pr1 =
    eq_rect x P py y pr2.
Proof.
  destruct pr1; cbn; intros.
  erewrite eq_dec_rew_type_family. eauto.
Qed.

Lemma eq_dec_refl {A} {EQ : EqDec A}:
  forall a, eq_dec a a = left eq_refl.
Proof.
  intros.
  destruct eq_dec.
  - f_equal. apply UIP_dec.
  - exact (False_rect _ (n eq_refl)).
Qed.

Lemma beq_dec_refl {A} {EQ: EqDec A}:
  forall a, beq_dec a a = true.
Proof.
  intros. unfold beq_dec.
  now rewrite eq_dec_refl.
Qed.

Lemma beq_dec_eq {A} {EQ : EqDec A} :
  forall a b, beq_dec a b = true <-> a = b.
Proof.
  intros. unfold beq_dec. destruct (eq_dec _ _); subst; intuition congruence.
Qed.

Lemma beq_dec_neq {A} {EQ : EqDec A} :
  forall a b, beq_dec a b = false <-> a <> b.
Proof.
  intros. unfold beq_dec. destruct (eq_dec _ _); subst; intuition congruence.
Qed.

Lemma beq_dec_comm {A} {EQ : EqDec A} :
  forall a b, beq_dec a b = beq_dec b a.
Proof.
  intros. unfold beq_dec. destruct (eq_dec _ _); subst.
  - now rewrite eq_dec_refl.
  - destruct (eq_dec _ _); subst; auto; contradiction.
Qed.

Definition EqDecSig {T} `(EqDec T) {F : T -> Type} (f : forall t, EqDec (F t))
: EqDec {t & F t}.
Proof.
  split.
  set (eta (tft : {t & F t}) :=
    let (t, ft) as s return (existT F (projT1 s) (projT2 s) = s) := tft in eq_refl
  ).
  unshelve eset (projT2_eq (x y : {t & F t}) (EQ : x = y) := _ :
    forall (EQ1 : projT1 x = projT1 y), rew [F] EQ1 in projT2 x = projT2 y).
  { rewrite <- EQ. intro EQ1. rewrite (UIP_dec EQ1 eq_refl). exact eq_refl. }
  intro x. rewrite <- (eta x).
  intro y. rewrite <- (eta y).
  refine match eq_dec (projT1 y) (projT1 x) with
  | left EQm => _
  | right NEQm => right (fun contra => NEQm _)
  end.
  2:{ exact (f_equal (@projT1 _ F) (eq_sym contra)). }
  generalize (projT2 x) as ftx.
  rewrite <- EQm.
  refine (fun ftx =>
    match eq_dec ftx (projT2 y) with
    | left EQmet => left (f_equal (existT F (projT1 y)) EQmet)
    | right NEQmet => right (fun contra => NEQmet _)
    end).
  exact (projT2_eq (existT F (projT1 y) ftx) (existT F (projT1 y) (projT2 y)) contra eq_refl).
Defined.

Global Instance sigTEqDec {A} `{EqDec A} (B : A -> Type) `{!forall x, EqDec (B x)} : EqDec (sigT B) :=
  EqDecSig _ _
.

Definition cast {K} `{EqDec K} {V} {k k'} (x : V k) (pf : k = k') :=
  match eq_dec k k' with
  | left EQ => rew EQ in x
  | right NEQ => False_rect _ (NEQ pf)
  end.

Lemma cast_cast {K} `{EqDec K} {V} {k k' k''} (x : V k) (pf : k = k') (pf' : k' = k'') :
  cast (cast x pf) pf' = cast x (eq_trans pf pf').
Proof. subst; unfold cast; rewrite eq_dec_refl; reflexivity. Qed.

Lemma cast_eq {K} `{EqDec K} {V} {k} (x : V k) (pf : k = k) :
  cast x pf = x.
Proof. unfold cast. rewrite eq_dec_refl. reflexivity. Qed.

Lemma cast_irrel {K : Type} `{EqDec K} (V : K -> Type) {k k' : K} {pf pf' : k = k'} {x : V k} :
  cast x pf = cast x pf'.
Proof. subst. unfold cast. now rewrite eq_dec_refl. Qed.

Definition In_dec {T} `{EqDec T} := List.in_dec eq_dec.

Definition bIn_dec {T} `{EqDec T} (x : T) (l : list T) : bool :=
  if In_dec x l then true else false
.

