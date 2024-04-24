From Coq Require Export Bool.Bool.
From Coq Require Export Init.Nat.
From Coq Require Export Arith.Arith.
From Coq Require Export Arith.EqNat.
From Coq Require Export Lia.
From Coq Require Export Lists.List.
From Basics Require Export sflib.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Types with decidable equality *)
Class Eq T : Type :=
{
  eqb : T -> T -> bool;
  eqb_eq : forall (t t' : T), eqb t t' = true <-> t = t';
}.

Lemma eqb_comm {T} `{Eq T} :
  forall x x', eqb x x' = eqb x' x.
Proof.
  intros.
  destruct (eqb x x') eqn:EQ; destruct (eqb x' x) eqn:EQ';
  try reflexivity;
  try rewrite eqb_eq in *; subst;
  try rewrite <- EQ; try rewrite <- EQ';
  match goal with
  | |- true = _ => symmetry
  | _ => idtac
  end; rewrite eqb_eq; eauto.
Qed.

Lemma eqb_neq {T} `{Eq T} : 
  forall x x', eqb x x' = false <-> x <> x'.
Proof.
  intros; split; intros contra.
  - red; intros RR. rewrite <- eqb_eq in *.
    rewrite RR in contra. inversion contra.
  - destruct (eqb x x') eqn:EQ; try reflexivity.
    exfalso. apply contra. rewrite <- eqb_eq. eauto.
Qed.

Lemma eqb_refl {T} `{Eq T} : forall t, eqb t t = true.
Proof. intros; apply eqb_eq; eauto. Qed.

#[refine] Instance EqPair A B `{EA : Eq A} `{EB : Eq B} : Eq (A * B) :=
{ eqb := fun x y =>
    let (a, b) := x in let (a', b') := y in
    eqb a a' && eqb b b' }.
Proof.
  ii; repeat des_goal; split; intro EQ; repeat des_hyp;
  repeat first [rewrite eqb_eq in * | rewrite eqb_refl in * | clarify].
Defined.

Ltac eqb2eq T :=
  match T with
  | nat => first 
    [rewrite Nat.eqb_eq in * | 
     rewrite Nat.eqb_neq in *]
  | _ =>
    match goal with
    | H : Eq T |- _ => first 
      [rewrite H.(eqb_eq) in * | 
       rewrite (@eqb_neq T H) in *]
    end
  end.

Ltac eq2eqb T :=
  match T with
  | nat => first 
    [rewrite <- Nat.eqb_eq in * | 
     rewrite <- Nat.eqb_neq in *]
  | _ =>
    match goal with
    | H : Eq T |- _ => first 
      [rewrite <- H.(eqb_eq) in * | 
       rewrite <- (@eqb_neq T H) in *]
    end
  end.

Ltac case_eqb x y :=
  match goal with
  | _ : Eq ?T |- _ =>
    let C := fresh "CASE" in
    destruct (eqb x y) eqn:C;
    eqb2eq T; clarify
  end.

Ltac try_all := match goal with H : _ |- _ => apply H end.

Fixpoint Inb {T} `{Eq T} t (l : list T) :=
  match l with
  | [] => false
  | hd :: tl => eqb hd t || Inb t tl
  end.

Lemma Inb_In {T} `{Eq T} :
  forall (l : list T) (t : T),
    Inb t l = true <-> In t l.
Proof.
  induction l; intros; simpl in *;
  split; intros EQ; try contradict.
  - repeat des_hyp;
    simpl in *; try (inversion EQ; fail);
    match goal with
    | _ => left; rewrite <- eqb_eq; eauto; fail
    | _ => right; rewrite <- IHl; eauto; fail
    end.
  - destruct EQ as [EQhd | EQtl].
    subst. rewrite eqb_refl. eauto.
    rewrite <- IHl in EQtl. rewrite EQtl.
    des_goal; eauto.
Qed.

Lemma Inb_nIn {T} `{Eq T} :
  forall (l : list T) (t : T),
    Inb t l = false <-> ~ (In t l).
Proof.
  induction l; intros; simpl in *;
  split; intros NEQ; eauto.
  - red; intros EQ.
    destruct (eqb a t) eqn:NEQhd;
    destruct (Inb t l) eqn:NEQtl;
    try (inversion NEQ; fail).
    rewrite eqb_neq in NEQhd.
    rewrite IHl in NEQtl.
    destruct EQ as [EQhd | EQtl];
    match goal with
    | _ => apply NEQhd; eauto; fail
    | _ => apply NEQtl; eauto; fail
    end.
  - destruct (eqb a t) eqn:NEQhd;
    destruct (Inb t l) eqn:NEQtl; simpl;
    match goal with
    | _ => reflexivity; fail
    | [H : eqb _ _ = true |- _] =>
      rewrite eqb_eq in H
    | [H : Inb _ _ = true |- _] =>
      rewrite Inb_In in H
    end;
    exfalso; apply NEQ; eauto.
Qed.

Ltac Inb2In T :=
  match goal with
  | H : Eq T |- _ => first 
    [rewrite (@Inb_In T H) in * | 
     rewrite (@Inb_nIn T H) in *]
  end.

Ltac In2Inb T :=
  match goal with
  | H : Eq T |- _ => first 
    [rewrite <- (@Inb_In T H) in * | 
     rewrite <- (@Inb_nIn T H) in *]
  end.

(* Infinite set that can be used as names *)
Class Name T `{Eq T} : Type :=
{
  gensym : list T -> T;
  gensym_spec : forall l, ~ In (gensym l) l
}.

#[local] Lemma for_split P Q :
  ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof. tauto. Qed.

Ltac split_nIn :=
  ss; repeat rewrite in_app_iff in *;
  repeat match goal with
  | H : ~ (?A \/ ?B) |- _ =>
    let H' := fresh H in
    apply for_split in H;
    destruct H as (H & H')
  end.

Ltac gensym_tac L ℓ :=
  set (gensym L) as ℓ;
  match goal with
  | ℓ := gensym ?l |- _ =>
    assert (~ In ℓ l) by (subst ℓ; apply gensym_spec; auto);
    split_nIn
  end.

Ltac clean_set :=
  match goal with
  | ℓ := _ |- _ =>
    match goal with
    | H : _ = ℓ |- _ => repeat rewrite <- H in *; clear H
    | H : ℓ = _ |- _ => repeat rewrite H in *; clear H
    end
  end.

