(*! Utilities | Functions on Vect.index elements !*)
Require Stdlib.Vectors.FinFun.
Require Import Common Member.
Require Export Vect.

Fixpoint all_indices (bound: nat) : vect (index bound) bound :=
  match bound as n return (vect (index n) n) with
  | 0 => vect_nil
  | S bound => vect_cons thisone (vect_map anotherone (all_indices bound))
  end.

Fixpoint all_indices_eqn bound:
  forall idx, vect_nth (all_indices bound) idx = idx.
Proof.
  destruct bound, idx; cbn.
  - reflexivity.
  - rewrite vect_nth_map.
    rewrite all_indices_eqn.
    reflexivity.
Defined.

Lemma all_indices_NoDup bound:
  vect_NoDup (all_indices bound).
Proof.
  induction bound; cbn; econstructor.
  - intro.
    apply vect_to_list_In in H.
    apply vect_map_In_ex in H.
    destruct H as [t (? & ?)]; discriminate.
  - setoid_rewrite vect_to_list_map.
    apply FinFun.Injective_map_NoDup.
    + red; inversion 1; reflexivity.
    + eassumption.
Qed.

Lemma all_indices_surjective bound:
  forall idx, member idx (vect_to_list (all_indices bound)).
Proof.
  intros.
  eapply nth_member.
  rewrite vect_to_list_nth.
  f_equal.
  apply all_indices_eqn.
Defined.

Instance FiniteType_index {n} : FiniteType (Vect.index n).
Proof.
  refine {| finite_index := index_to_nat;
            finite_elements := vect_to_list (all_indices n) |}.
  - intros; rewrite vect_to_list_nth, all_indices_eqn; reflexivity.
  - apply FinFun.Injective_map_NoDup.
    red; apply index_to_nat_injective.
    apply all_indices_NoDup.
Defined.

Instance EqDec_index {n} : EqDec (Vect.index n) := _.

Fixpoint List_assoc {K V: Type} {EQ: EqDec K} (k: K) (l: list (K * V)) {struct l} : option (Vect.index (List.length l)).
Proof.
  destruct l as [| h l].
  - exact None.
  - destruct (eq_dec k (fst h)).
    + exact (Some thisone).
    + destruct (List_assoc K V EQ k l).
      * exact (Some (anotherone i)).
      * exact None.
Defined.

Fixpoint List_nth {K: Type} (l: list K) (idx: Vect.index (List.length l)) {struct l} : K.
Proof.
  destruct l as [| h l]; destruct idx.
  - exact h.
  - exact (List_nth K l a).
Defined.

Fixpoint List_nth_map_cast {A B} (f: A -> B) l:
  List.length l = List.length (List.map f l).
Proof. destruct l; cbn; auto. Defined.

Lemma List_nth_map {A B} (f: A -> B):
  forall l idx,
    f (List_nth l idx) =
    List_nth (List.map f l)
             ltac:(rewrite <- List_nth_map_cast; exact idx).
Proof.
  induction l; destruct idx; cbn;
    set (List_nth (List.map f l)) as x in *; clearbody x.
  - set (List_nth_map_cast _ _) as Heq in *; clearbody Heq.
    destruct Heq; reflexivity.
  - rewrite IHl; clear.
    set (List_nth_map_cast _ _) as Heq in *; clearbody Heq.
    destruct Heq; reflexivity.
Qed.

Lemma List_nth_firstn_1_skipn {A} (l: list A) a:
  List.firstn 1 (List.skipn (index_to_nat a) l) =
  [List_nth l a].
Proof.
  induction l; destruct a; cbn.
  - reflexivity.
  - specialize (IHl a).
    destruct (skipn _ _); inversion IHl; reflexivity.
Qed.

Lemma List_nth_skipn_cons_next {A}:
  forall (l: list A) idx,
    List_nth l idx :: (List.skipn (S (index_to_nat idx)) l) =
    List.skipn (index_to_nat idx) l.
Proof.
  induction l; destruct idx; cbn; try rewrite IHl; reflexivity.
Qed.

Lemma list_sum_member_le:
  forall l idx,
    List_nth l idx <=
    list_sum l.
Proof.
  induction l; destruct idx.
  - cbn; lia.
  - specialize (IHl a0); unfold list_sum, list_sum' in *; cbn; lia.
Qed.

Instance Show_index (n: nat) : Show (index n) :=
  { show x := show (index_to_nat x) }.

Definition index_plus_valid m {n} (i : index n) :
  index_of_nat (m + n) (m + index_to_nat i) <> None.
Proof.
  exploit (@index_of_nat_bounded (m + n)).
  2: intros (idx & ->); congruence.
  specialize (index_to_nat_bounded i). lia.
Qed.

Definition index_plus m {n} (i : index n) :=
  assert_opt (index_of_nat (m + n) (m + index_to_nat i)) (index_plus_valid _ _)
.

Lemma index_to_nat_plus m {n} (i : index n) :
  index_to_nat (index_plus m i) = m + index_to_nat i.
Proof.
  apply index_to_nat_of_nat.
  unfold index_plus. rewrite <- assert_opt_eqn.
  reflexivity.
Qed.

Lemma vect_nth_index_plus m {n} (i : index n) :
  forall {A} (u : vect A _) v,
    vect_nth (u ++ v)%vect (index_plus m i) = vect_nth v i.
Proof.
  induction m; simpl.
  - intros. f_equal. apply index_to_nat_injective. rewrite index_to_nat_plus. auto.
  - intros ? (hd & tl) v. simpl.
    destruct (index_plus _ _) eqn:EQ.
    + apply (f_equal index_to_nat) in EQ.
      rewrite index_to_nat_plus in EQ. inversion EQ.
    + apply (f_equal index_to_nat) in EQ.
      rewrite index_to_nat_plus in EQ.
      rewrite <- (IHm _ tl). f_equal.
      apply index_to_nat_injective. rewrite index_to_nat_plus.
      inversion EQ; auto.
Qed.

Definition index_extend_valid {m} (i : index m) n :
  index_of_nat (m + n) (index_to_nat i) <> None.
Proof.
  exploit (@index_of_nat_bounded (m + n)).
  2: intros (idx & ->); congruence.
  specialize (index_to_nat_bounded i). lia.
Qed.

Definition index_extend {m} (i : index m) n :=
  assert_opt (index_of_nat (m + n) (index_to_nat i)) (index_extend_valid _ _)
.

Lemma index_to_nat_extend {m} (i : index m) n :
  index_to_nat (index_extend i n) = index_to_nat i.
Proof.
  apply index_to_nat_of_nat.
  unfold index_extend. rewrite <- assert_opt_eqn.
  reflexivity.
Qed.

Lemma vect_nth_index_extend {m} (i : index m) n :
  forall {A} (u : vect A _) v,
    vect_nth (u ++ v)%vect (index_extend i n) = vect_nth u i.
Proof.
  induction m; simpl.
  - destruct i.
  - intros ? (hd & tl) v. simpl.
    destruct (index_extend _ _) eqn:EQ.
    + apply (f_equal index_to_nat) in EQ.
      rewrite index_to_nat_extend in EQ.
      simpl in EQ.
      destruct i; auto. inversion EQ.
    + apply (f_equal index_to_nat) in EQ.
      rewrite index_to_nat_extend in EQ.
      simpl in EQ.
      destruct i; inversion EQ.
      rewrite <- (IHm _ _ tl v). f_equal.
      apply index_to_nat_injective. rewrite index_to_nat_extend. auto.
Qed.

