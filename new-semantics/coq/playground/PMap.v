(** * The extensional binary tries based on a canonical representation *)

(* Authors: Andrew W. Appel, Princeton University,
            Xavier Leroy, Collège de France and Inria.
Copyright: Andrew W. Appel and Inria.
   License: BSD-3-Clause. *)

From Coq Require Import PArith.

Class map {K V} := mkMap {
  rep : Type;

(* fundamental operation, all others are axiomatized in terms of this one *)
  get: rep -> K -> option V;

  empty : rep;
  put : rep -> K -> V -> rep;
  remove : rep -> K -> rep;

  (* R is the type of the accumulator *)
  fold {R: Type} : (R -> K -> V -> R) -> R -> rep -> R;
}.

Arguments map : clear implicits.
Global Coercion rep : map >-> Sortclass.
Global Hint Mode map + + : typeclass_instances.
Local Hint Mode map - - : typeclass_instances.

Class ok {K V : Type} {map : map K V}: Prop := {
  map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
  get_empty : forall k, get empty k = None;
  get_put_same : forall m k v, get (put m k v) k = Some v;
  get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
  get_remove_same : forall m k, get (remove m k) k = None;
  get_remove_diff : forall m k k', k <> k' -> get (remove m k') k = get m k;
  fold_spec{R: Type} : forall (P: rep -> R -> Prop) (f: R -> K -> V -> R) r0,
      P empty r0 ->
      (forall k v m r, get m k = None -> P m r -> P (put m k v) (f r k v)) ->
      forall m, P m (fold f r0 m);
  (* Folding over a map preserves relations: *)
  fold_parametricity: forall {A B : Type} (R : A -> B -> Prop)
                             (fa: A -> K -> V -> A) (fb: B -> K -> V -> B),
      (forall a b k v, R a b -> R (fa a k v) (fb b k v)) ->
      forall a0 b0, R a0 b0 -> forall m, R (fold fa a0 m) (fold fb b0 m);
}.
Arguments ok {_ _} _.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Set Implicit Arguments.

Module PTree.

(** ** Representation of tries *)

(** The type [tree'] of nonempty tries *)
Inductive tree' {V : Type} : Type :=
  (* this node is nonempty *)
  | NodeM (v : V) (l r : option tree')
  (* this node is empty, the first nonempty subtrie is the left one *)
  | Node0 (l : tree') (r : option tree')
  (* this node is empty, the first nonempty subtrie is the right one *)
  | Node1 (r : tree')
.

Arguments tree' : clear implicits.

Definition tree V := option (tree' V).

Section TREE_IND.
  Context {V : Type}.
  Context (P : tree V -> Prop) (P' : tree' V -> Prop).
  Context (PNodeM : forall v l r, P l -> P r -> P' (NodeM v l r))
          (PNode0 : forall l r, P' l -> P r -> P' (Node0 l r))
          (PNode1 : forall r, P' r -> P' (Node1 r))
          (PNone : P None)
          (PSome : forall t', P' t' -> P (Some t')).

  Fixpoint _tree'_ind t' : P' t' :=
  let _tree_ind ot : P ot :=
    match ot with
    | None => PNone
    | Some t => PSome (_tree'_ind t)
    end
  in match t' with
  | NodeM v l r => PNodeM v (_tree_ind l) (_tree_ind r)
  | Node0 l' r => PNode0 (_tree'_ind l') (_tree_ind r)
  | Node1 r' => PNode1 (_tree'_ind r')
  end.
End TREE_IND.

Definition tree'_ind {V} (P' : tree' V -> Prop) PNodeM PNode0 PNode1 :=
  let P t := match t with None => True | Some t' => P' t' end in
  _tree'_ind P P' PNodeM PNode0 PNode1 I ltac:(auto).

(** A smart constructor.  Given a (possibly empty) left subtree,
    a (possibly absent) value, and a (possibly empty) right subtree,
    it builds the corresponding tree. *)

Definition Node {V} (l: tree V) (o: option V) (r: tree V) : tree V :=
  match l,o,r with
  | None, None, None => None
  | _, Some v, _ => Some (NodeM v l r)
  | Some l', None, _ => Some (Node0 l' r)
  | None, None, Some r' => Some (Node1 r')
  end.

(** ** Basic operations: [empty], [get], [set], [remove], [fold] *)

Definition empty (V : Type) : tree V := None.

(** Operations such as [get] follow a common pattern:
    first, a recursive function [get'] over nonempty tries;
    then, a non-recursive function [get] to handle empty tries too. *)

Local Open Scope positive_scope.

Fixpoint get' {V} (p : positive) (m : tree' V) : option V :=
  match p, m with
  | 1, NodeM v _ _ => Some v
  | 1, _ => None
  | q~0, NodeM _ (Some l) _
  | q~0, Node0 l _ => get' q l
  | q~0, _ => None
  | q~1, NodeM _ _ (Some r)
  | q~1, Node0 _ (Some r)
  | q~1, Node1 r => get' q r
  | q~1, _ => None
  end.

Definition get {V} (p : positive) (m : tree V) : option V :=
  match m with
  | None => None
  | Some m' => get' p m'
  end.

(** [set0 p v] constructs the singleton trie that maps [p] to [v]
    and has no other bindings. *)

Fixpoint set0 {V} (p : positive) (v : V) : tree' V :=
  match p with
  | 1 => NodeM v None None
  | q~0 => Node0 (set0 q v) None
  | q~1 => Node1 (set0 q v)
  end.

Fixpoint set' {V} (p : positive) (v : V) (m : tree' V) : tree' V :=
  let set p v m :=
    match m with
    | None => set0 p v
    | Some m' => set' p v m'
    end
  in match p, m with
  | 1, NodeM _ l r => NodeM v l r
  | 1, Node0 l r => NodeM v (Some l) r
  | 1, Node1 r => NodeM v None (Some r)
  | q~0, NodeM w l r => NodeM w (Some (set q v l)) r
  | q~0, Node0 l r => Node0 (set' q v l) r
  | q~0, Node1 r => Node0 (set0 q v) (Some r)
  | q~1, NodeM w l r => NodeM w l (Some (set q v r))
  | q~1, Node0 l r => Node0 l (Some (set q v r))
  | q~1, Node1 r => Node1 (set' q v r)
  end.

Definition put {V} p v (m : tree V) :=
  match m with
  | None => set0 p v
  | Some m' => set' p v m'
  end.

Fixpoint remove' {V} (p : positive) (m : tree' V) : tree V :=
  let remove p m :=
    match m with
    | None => None
    | Some m' => remove' p m'
    end
  in match p, m with
  | 1, NodeM _ None None => None
  | 1, NodeM _ (Some l) r => Some (Node0 l r)
  | 1, NodeM _ None (Some r) => Some (Node1 r)
  | 1, _ => Some m
  | q~0, NodeM v l r => Node (remove q l) (Some v) r
  | q~0, Node0 l r => Node (remove' q l) None r
  | q~0, _ => Some m
  | q~1, NodeM v l r => Node l (Some v) (remove q r)
  | q~1, Node0 l r => Node (Some l) None (remove q r)
  | q~1, Node1 r => Node None None (remove' q r)
  end.

(* k : positive -> positive *)
Fixpoint fold'' {R V : Type}
  (f : R -> positive -> V -> R) (acc : R) k (m' : tree' V) : R :=
  let fold' f acc k m :=
    match m with
    | None => acc
    | Some m' => fold'' f acc k m'
    end
  in match m' with
  | NodeM v l r =>
    let accl := fold' f acc (fun x => k (x~0)) l in
    let accv := f accl (k 1) v in
    fold' f accv (fun x => k (x~1)) r
  | Node0 l r =>
    let accl := fold'' f acc (fun x => k (x~0)) l in
    fold' f accl (fun x => k (x~1)) r
  | Node1 r => fold'' f acc (fun x => k (x~1)) r
  end.

Local Close Scope positive_scope.

(** ** Good variable properties for the basic operations *)

Lemma gss0: forall {V} p (x : V), get' p (set0 p x) = Some x.
Proof. induction p; simpl; auto. Qed.

Lemma gso0: forall {V} p q (x : V), p <> q -> get' p (set0 q x) = None.
Proof.
  induction p; destruct q; simpl; intros; auto; try apply IHp; congruence.
Qed.

Lemma gss V (m' : tree' V) :
  forall i x, get' i (set' i x m') = Some x.
Proof with auto using gss0.
  induction m' using tree'_ind; intros; destruct i; simpl ...
  - destruct r ...
  - destruct l ...
  - destruct r ...
Qed.

Lemma gso V (m' : tree' V) :
  forall i j x, i <> j -> get' i (set' j x m') = get' i m'.
Proof with auto using gso0.
  induction m' using tree'_ind;
  intros; destruct i, j; simpl; try contradiction ...
  all: assert (i <> j) by congruence ...
  - destruct r ...
  - destruct l ...
  - destruct r ...
Qed.

Lemma gNode :
  forall {V} (i: positive) (l: tree V) (x: option V) (r: tree V),
  get i (Node l x r) = match i with xH => x | xO j => get j l | xI j => get j r end.
Proof.
  intros. destruct l, x, r; simpl; auto; destruct i; auto.
Qed.

Lemma pNode :
  forall {V} (v : V) (a b : tree V),
  put 1 v (Node a None b) = NodeM v a b.
Proof.
  destruct a, b; auto.
Qed.

Local Opaque Node.

Lemma grs V (m' : tree' V) :
  forall i, get i (remove' i m') = None.
Proof with (try rewrite gNode; auto).
  induction m' using tree'_ind; intros; destruct i; simpl ...
  - destruct r ...
  - destruct l ...
  - destruct l ... destruct r ...
  - destruct r ...
Qed.

Lemma gro V (m' : tree' V) :
  forall i j, i <> j -> get i (remove' j m') = get' i m'.
Proof with (try rewrite gNode; auto).
  induction m' using tree'_ind;
  intros; destruct i, j; simpl; try contradiction ...
  all: try assert (i <> j) by congruence ...
  - destruct r ...
  - destruct l ... destruct r ...
  - destruct l ...
  - destruct l ... destruct r ...
  - destruct r ...
Qed.

Lemma fold''_spec {R V : Type} :
  forall (P : tree V -> R -> Prop) (f : R -> positive -> V -> R) acc k
    (PEmpty : P None acc)
    (PNodes : forall i v m r, get i m = None -> P m r -> P (Some (put i v m)) (f r (k i) v)),
    forall m, P (Some m) (fold'' f acc k m).
Proof.
  intros. generalize dependent P. revert f acc k.
  induction m using tree'_ind; intros; simpl;
  set (P0 t := match t with None => P None | Some t' => P (Some (Node0 t' None)) end);
  set (P1 t := match t with None => P None | Some t' => P (Some (Node1 t')) end).
  Local Ltac appnodes PNodes :=
  match goal with
  | |- _ (Some (?N (set' ?i _ ?l) ?r)) (_ _ (_ (?x ?i)) _) =>
    apply PNodes with (m := Some (N l r)) (i := x i); auto
  | |- _ (Some (?N (set' _ _ ?l))) (_ _ (_ (?x ?i)) _) =>
    apply PNodes with (m := Some (N l)) (i := x i); auto
  | |- _ (Some (?N (set0 ?i _) ?r)) (_ _ (_ (?x ?i)) _) =>
    apply PNodes with (m := r) (i := x i); auto
  | |- _ (Some (?N (set0 _ _))) (_ _ (_ (?x ?i)) _) =>
    apply PNodes with (m := None) (i := x i); auto
  | |- _ (Some _) (_ _ (_ xH) _) =>
    apply PNodes with (m := None) (i := xH); auto
  | |- _ (Some (?N ?v ?l (Some (_ _ _ ?r)))) (_ _ (_ (?x ?i)) _) =>
    apply PNodes with (m := Some (N v l r)) (i := (x i)); auto
  | |- _ (Some (?N ?l (Some (_ _ _ ?r)))) (_ _ (_ (?x ?i)) _) =>
     apply PNodes with (m := Some (N l r)) (i := (x i)); auto
  end.
  - destruct r; try apply H0;
    solve [
      intros; appnodes PNodes |
      destruct l; rewrite <- pNode; apply PNodes; auto;
      apply H with (P := P0); auto;
      intros ? ? [? |] ? ? ?; subst P0; simpl; appnodes PNodes
    ].
  - destruct r; try apply H;
    solve [
      intros; appnodes PNodes |
      apply IHm with (P := P0); auto;
      intros ? ? [? |] ? ? ?; subst P0; simpl; appnodes PNodes
    ].
  - apply IHm with (P := P1); auto;
    intros ? ? [? |] ? ? ?; subst P1; simpl; appnodes PNodes.
Qed.

Lemma fold''_parametricity {A B V : Type} :
  forall (R : A -> B -> Prop) (fa: A -> positive -> V -> A) (fb: B -> positive -> V -> B)
    (RApp : forall a b i v (REL : R a b), R (fa a i v) (fb b i v)),
  forall m a0 b0 k (RAcc : R a0 b0),
    R (fold'' fa a0 k m) (fold'' fb b0 k m).
Proof.
  do 4 intro.
  induction m using tree'_ind; intros;
  [destruct l, r | destruct r |]; eauto.
Qed.

Lemma tree'_nonempty {V} (m : tree' V) :
  exists k, get' k m <> None.
Proof.
  induction m using tree'_ind;
  [destruct l, r | destruct r|];
  repeat match goal with
  | H : exists _, _ |- _ =>
    let k := fresh "k" in destruct H as [k H];
    try solve [exists (xO k); eauto | exists (xI k); eauto]
  end; exists xH; intro EQ; inversion EQ.
Qed.

Lemma tree'_contradiction {V} (m : tree' V) :
  ~ forall k, get' k m = None.
Proof.
  destruct (tree'_nonempty m) as (k & ?). auto.
Qed.

Lemma tree_empty {V} (m : tree V) :
  (forall k, get k m = None) -> m = None.
Proof.
  destruct m; intros; simpl in *; auto.
  exfalso. eapply tree'_contradiction; eauto.
Qed.

Lemma tree'_ext {V} (m1 : tree' V) :
  forall m2 (EQ : forall k, get' k m1 = get' k m2),
    m1 = m2.
Proof.
  induction m1 using tree'_ind; intros; destruct m2;
  match goal with
  | |- NodeM ?v ?l ?r = NodeM ?v' ?l' ?r' =>
    assert (v = v') by
      (specialize (EQ xH); inversion EQ; auto);
    assert (forall k, get k l = get k l') by
      (intros; specialize (EQ (xO k)); eauto);
    assert (forall k, get k r = get k r') by
      (intros; specialize (EQ (xI k)); eauto);
    f_equal
  | |- Node0 ?l ?r = Node0 ?l' ?r' =>
    assert (forall k, get' k l = get' k l') by
      (intros; specialize (EQ (xO k)); eauto);
    assert (forall k, get k r = get k r') by
      (intros; specialize (EQ (xI k)); eauto);
    f_equal
  | |- Node1 ?r = Node1 ?r' =>
    assert (forall k, get' k r = get' k r') by
      (intros; specialize (EQ (xI k)); eauto);
    f_equal
  | _ => solve [specialize (EQ xH); inversion EQ]
  | |- context [Node0 ?m _] =>
    destruct (tree'_nonempty m) as (k & ?);
    specialize (EQ (xO k)); simpl in EQ;
    rewrite EQ in *; contradiction
  end; eauto;
  match goal with
  | |- ?a = ?b =>
    destruct a, b; simpl in *; auto; [
    f_equal; eauto |
    exfalso; eapply tree'_contradiction; eauto |
    symmetry; apply tree_empty; eauto]
  end.
Qed.
End PTree.

#[export] Instance PMap V : map positive V :=
{
  rep := PTree.tree V;
  get m k := PTree.get k m;
  empty := None;
  put m k v := Some (PTree.put k v m);
  remove m k :=
    match m with
    | None => None
    | Some m' => PTree.remove' k m'
    end;
  fold R f init m :=
    match m with
    | None => init
    | Some m' => PTree.fold'' f init id m'
    end;
}.

#[export, refine] Instance PMapOk V : ok (PMap V) := {}.
Proof.
  - intros. destruct m1, m2; auto.
    + f_equal. eapply PTree.tree'_ext; eauto.
    + simpl in *. exfalso. eapply PTree.tree'_contradiction. eauto.
    + simpl in *. exfalso. eapply PTree.tree'_contradiction. eauto.
  - auto.
  - intros. destruct m; simpl; auto using PTree.gss, PTree.gss0.
  - intros. destruct m; simpl; auto using PTree.gso, PTree.gso0.
  - intros. destruct m; simpl; auto using PTree.grs.
  - intros. destruct m; simpl; auto using PTree.gro.
  - intros. destruct m; simpl in *; auto.
    eapply PTree.fold''_spec; auto.
  - intros. destruct m; simpl in *; auto.
    eapply PTree.fold''_parametricity; auto.
Qed.

(* from stdpp/strings.v *)
From Coq Require Import Ascii.
From Coq Require Export String.

Local Definition funapp {A B} (f : A -> B) (x : A) := f x.
#[local] Infix "$" := funapp (at level 60, right associativity).
Local Definition bool_cons_pos (b : bool) (p : positive) : positive :=
  if b then xI p else xO p.
Local Definition ascii_cons_pos (c : ascii) (p : positive) : positive :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
     bool_cons_pos b0 $ bool_cons_pos b1 $ bool_cons_pos b2 $
       bool_cons_pos b3 $ bool_cons_pos b4 $ bool_cons_pos b5 $
       bool_cons_pos b6 $ bool_cons_pos b7 p
  end.

Fixpoint string_to_pos (s : string) : positive :=
  match s with
  | EmptyString => 1
  | String c s => ascii_cons_pos c (string_to_pos s)
  end.

(* The decoder that turns [positive] into string results in 256 cases (we need
to peel off 8 times a [~0]/[~1] constructor) and a number of fall through cases.
We avoid writing these cases explicitly by generating the definition using Ltac.
The lemma [string_of_to_pos] ensures the generated definition is correct.

Alternatively, we could implement it in two steps. Convert the [positive] to
[list bool], and convert the list to [string]. This definition will be slower
since auxilary data structures are created. *)
Local Fixpoint pos_to_string (p : positive) : string.
Proof.
  (** The argument [p] is the [positive] that we are peeling off.
  The argument [a] is the constructor [Ascii] partially applied to some number
  of Booleans (so its Coq type changes during the iteration).
  The argument [n] says how many more Booleans are needed to make this fully
  applied so that the [constr] has type ascii. *)
  let rec gen p a n :=
    lazymatch n with
    (* This character is done. Stop the ltac recursion; recursively invoke
    [pos_to_string] on the Gallina level for the remaining bits. *)
    | 0 => exact (String a (pos_to_string p))
    (* There are more bits to consume for this character, generate an
    appropriate [match] with ltac. *)
    | S ?n =>
       exact (match p with
              | 1 => EmptyString
              | p~0 => ltac:(gen p (a false) n)
              | p~1 => ltac:(gen p (a true) n)
              end%positive)
    end in
  gen p Ascii 8.
Defined.

Local Lemma pos_to_string_string_to_pos s : pos_to_string (string_to_pos s) = s.
Proof. induction s as [|[[][][][][][][][]]]; simpl; f_equal; first [reflexivity | assumption]. Qed.

