Require Import List PeanoNat.
Import ListNotations.

Ltac ss := simpl in *.
Ltac ii := repeat intro.
Ltac inv H := inversion H; subst; clear H.
Ltac des :=
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  | H : _ /\ _ |- _ =>
    let H' := fresh H in
    destruct H as [H H']
  | H : exists _, _ |- _ =>
    let x := fresh "x" in
    destruct H as [x H]
  end.
Ltac clarify :=
  repeat match goal with
  | H : ?A _ = ?A _ |- _ => injection H; clear H; ii; subst
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => solve [inversion H]
  | H : False |- _ => inversion H
  | H : True |- _ => clear H
  | H : _ <> _ |- _ => specialize (H eq_refl)
  end; subst.
Ltac rw :=
  match goal with RR : _ |- _ => rewrite RR in * end.
Ltac rrw :=
  match goal with RR : _ |- _ => rewrite <- RR in * end.
Ltac des_ifs :=
  let EQ := fresh "EQ" in
  repeat match goal with
  | H : context [match ?x with _ => _ end] |- _ => destruct x eqn:EQ
  | |- context [match ?x with _ => _ end] => destruct x eqn:EQ
  end; clarify.

Inductive repeats {X} : list X -> Prop :=
  | repeats_hd x l (IN : In x l) : repeats (x :: l)
  | repeats_tl x l (REP : repeats l) : repeats (x :: l)
.

Fixpoint nth_error {X} (n : nat) (l : list X) :=
  match n, l with
  | _, [] => None
  | O, x :: _ => Some x
  | S n', _ :: l' => nth_error n' l'
  end.

Lemma exist_idx {X} (l : list X) :
  forall x (IN : In x l),
    exists n, nth_error n l = Some x.
Proof.
  induction l; ii; ss; des; clarify.
  - exists 0. eauto.
  - specialize (IHl x IN). des.
    eexists (S _). eauto.
Qed.

Lemma idx_In {X} (l : list X) :
  forall x n (IDX : nth_error n l = Some x),
    In x l.
Proof.
  induction l; ii; ss; destruct n; ss; clarify; eauto.
Qed.

(* idx is an index representation of l1 under l2 *)
Fixpoint is_idx_repr {X} (l1 l2 : list X) idx :=
  match l1, idx with
  | [], [] => True
  | hd :: tl, idx_hd :: idx_tl =>
    nth_error idx_hd l2 = Some hd /\
    is_idx_repr tl l2 idx_tl
  | _, _ => False
  end.

Lemma exist_idx_repr {X} (l1 : list X) :
  forall l2 (CONTAIN : forall x, In x l1 -> In x l2),
    exists idx, is_idx_repr l1 l2 idx.
Proof.
  induction l1; ii; ss.
  - exists []. auto.
  - assert (In a l2) as CONTAINa by eauto.
    assert (forall x, In x l1 -> In x l2) as CONTAINb by eauto.
    apply exist_idx in CONTAINa.
    specialize (IHl1 l2 CONTAINb). des.
    eexists (_ :: _). eauto.
Qed.

Lemma idx_repr_contain {X} (l1 : list X) :
  forall l2 idx (REPR : is_idx_repr l1 l2 idx),
    (forall x, In x l1 -> In x l2).
Proof.
  induction l1; ii; ss; des_ifs; des; clarify; eauto using idx_In.
Qed.

Lemma idx_repr_In {X} (l1 : list X) :
  forall l2 i x idx (REPR : is_idx_repr l1 l2 idx) (IN : In i idx)
    (NTH : nth_error i l2 = Some x),
  In x l1.
Proof.
  induction l1; ii; ss; des_ifs; ss; des; clarify.
  - rw. clarify; eauto.
  - eauto.
Qed.

Fixpoint remove_nth {X} n (l : list X) :=
  match n, l with
  | _, [] => []
  | O, _ :: tl => tl
  | S n', hd :: tl => hd :: remove_nth n' tl
  end.

Lemma nth_remove_preserve_In {X} (l : list X) :
  forall x i i',
    nth_error i l = Some x -> i' <> i -> In x (remove_nth i' l).
Proof.
  induction l; ii; ss.
  - destruct i; ss; clarify.
  - destruct i, i'; ss; clarify; eauto using idx_In.
    + right. eauto.
Qed.

Lemma nth_remove_decrease_length {X} (l : list X) :
  forall x i,
    nth_error i l = Some x -> length (remove_nth i l) < length l.
Proof.
  induction l; ii; ss; destruct i; ss; clarify; auto.
  rewrite <- Nat.succ_lt_mono. eauto.
Qed.

Lemma nth_remove_preserve_contain {X} (l1 : list X) :
  forall l2 idx i',
    is_idx_repr l1 l2 idx -> ~ In i' idx ->
    (forall x, In x l1 -> In x (remove_nth i' l2)).
Proof.
  induction l1; ii; ss; des_ifs; clarify.
  ss; des; clarify;
  eauto using nth_remove_preserve_In.
Qed.

Fixpoint Inb (n : nat) l :=
  match l with
  | [] => false
  | hd :: tl =>
    if Nat.eqb n hd then true else Inb n tl
  end.

Lemma Inb_In l :
  forall n, Inb n l = true <-> In n l.
Proof.
  induction l; ii; ss; split;
  ii; clarify; des_ifs;
  first [rewrite Nat.eqb_eq in * | rewrite Nat.eqb_neq in *];
  des; clarify; eauto.
  - rewrite <- IHl; eauto.
  - rewrite IHl; eauto.
Qed.

Lemma Inb_nIn l :
  forall n, Inb n l = false <-> ~ In n l.
Proof.
  intros; split; ii; rewrite <- Inb_In in *.
  - rw. clarify.
  - destruct (Inb n l); clarify; eauto.
Qed.

Theorem pigeonhole {X} :
  forall (l1 l2 : list X)
    (CONTAIN : forall x, In x l1 -> In x l2)
    (LT : length l2 < length l1), repeats l1.
Proof.
  ii.
  remember (length l1) as len eqn:EQ.
  assert (length l1 <= len) as LE. subst. eauto.
  rewrite EQ in LT. clear EQ.
  revert l1 LE l2 CONTAIN LT.
  induction len; ii; ss.
  - destruct l1; inv LE; ss; inv LT.
  - inv LE; eauto.
    destruct l1 as [|x1 l1]; ss; clarify.
    assert (length l1 <= length l1) as HINT by eauto.
    specialize (IHlen l1 HINT). clear HINT.
    inv LT.
    + (* idx1 : idx repr of x1 *)
      assert (In x1 l2) as IDX1 by eauto.
      eapply exist_idx in IDX1.
      destruct IDX1 as [idx1 IDX1].
      (* idx : idx repr of l1 *)
      assert (forall x, In x l1 -> In x l2) as IDX by eauto.
      eapply exist_idx_repr in IDX.
      destruct IDX as [idx IDX].
      (* case analysis *)
      destruct (Inb idx1 idx) eqn:CASE;
      first [rewrite Inb_In in CASE | rewrite Inb_nIn in CASE].
      (* case 1 : idx1 is in idx *)
      (* then x1 is in l1, econstructor 1 *)
      constructor 1. eapply idx_repr_In; eauto.
      (* case 2 : idx1 is not in idx *)
      (* can remove idx1 from l2, obtain list l2' such that *)
      (* forall x, In x l1 -> In x l2' *)
      (* and length l2' = length l2 - 1 < length l1 *)
      (* then repeats l1, econstructor 2 *)
      specialize (IHlen (remove_nth idx1 l2)).
      constructor 2. eapply IHlen.
      eapply nth_remove_preserve_contain; eauto.
      rrw.
      eapply nth_remove_decrease_length; eauto.
    + rewrite Nat.le_succ_l in *.
      specialize (IHlen l2).
      constructor 2. eauto.
Qed.

