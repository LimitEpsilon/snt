From Coq Require Import
  Strings.String
  Numbers.DecimalString
  ZArith
  List.
Import ListNotations.

Local Open Scope string_scope.

Class ExpSYM repr :=
  {
    lit : Z -> repr;
    neg : repr -> repr;
    add : repr -> repr -> repr
  }.

Definition tf1 := fun {repr : Type} `{ExpSYM repr} =>
  add (lit 8) (neg (add (lit 1) (lit 2))).

Class MulSYM repr :=
  {
    mul : repr -> repr -> repr
  }.

Definition tfm1 {repr} `{ExpSYM repr} `{MulSYM repr} :=
  mul (lit 7) tf1.

#[local] Instance IntExpSYM : ExpSYM Z :=
  {
    lit := id;
    neg := Z.opp;
    add := Z.add;
  }.

Compute (@tf1 Z IntExpSYM).

#[local] Instance IntMulSYM : MulSYM Z :=
  {
    mul := Z.mul;
  }.

Compute (@tfm1 Z _ _).

Definition string_of_int n :=
  NilEmpty.string_of_int (Z.to_int n).

Definition int_of_string s :=
  match NilEmpty.int_of_string s with
  | None => None
  | Some n => Some (Z.of_int n)
  end.

#[local] Instance StringExpSYM : ExpSYM string :=
  {
    lit := string_of_int;
    neg n := "-" ++ n;
    add a b := "(" ++ a ++ "+" ++ b ++ ")";
  }.

Compute (@tf1 string _).

Inductive Tree :=
  | Leaf (s : string)
  | Node (this : string) (children : list Tree)
.

Fixpoint tree_ind (P : Tree -> Prop)
  (PLeaf : forall s, P (Leaf s))
  (PNode : forall this children,
    (forall child, In child children -> P child) ->
    P (Node this children))
  (t : Tree) : P t.
Proof.
  destruct t.
  - apply PLeaf.
  - apply PNode. induction children;
    intros ? H; simpl in H; destruct H.
    + rewrite <- H. apply tree_ind; assumption.
    + apply IHchildren. assumption.
Qed.

#[local] Instance TreeExpSYM : ExpSYM Tree :=
  {
    lit n := Node "Lit" [Leaf (string_of_int n)];
    neg e := Node "Neg" [e];
    add e1 e2 := Node "Add" [e1; e2];
  }.

Definition tf1_tree := @tf1 Tree TreeExpSYM.
(* Compute tf1_tree. *)

Definition calc := @id Z.

Definition view := @id string.

Fixpoint fromTree {repr} `{ExpSYM repr} (t : Tree) : option repr :=
  match t with
  | Node "Lit" [Leaf n] =>
    match int_of_string n with
    | Some n => Some (lit n)
    | None => None
    end
  | Node "Neg" [e] =>
    match fromTree e with
    | Some e => Some (neg e)
    | None => None
    end
  | Node "Add" [e1; e2] =>
    match fromTree e1, fromTree e2 with
    | Some e1, Some e2 => Some (add e1 e2)
    | _, _ => None
    end
  | _ => None
  end.

Compute (match fromTree tf1_tree with
  | Some e =>
    Some (string_of_int (calc e))
  | None => None
  end).

#[local] Instance PairExpSYM {repr repr'} `{ExpSYM repr} `{ExpSYM repr'} : ExpSYM (repr * repr') :=
  {
    lit n := (lit n, lit n);
    neg e := (neg (fst e), neg (snd e));
    add e1 e2 := (add (fst e1) (fst e2), add (snd e1) (snd e2));
  }.

Inductive tm :=
  | var (x : string)
  | lam (x : string) (e : tm)
  | app (e1 e2 : tm)
.

Inductive val :=
  | clos (x : string) (e : tm) (σ : string -> option val)
.

Inductive dom :=
  | Halt (v : option val)
  | Continue (e : tm) (σ : string -> option val) (k : val -> dom)
.

Fixpoint step (e : tm) (σ : string -> option val) (k : val -> dom) : dom :=
  match e with
  | var x => match σ x with None => Halt None | Some v => k v end
  | lam x e => k (clos x e σ)
  | app e1 e2 =>
    step e1 σ (fun v1 =>
      match v1 with
      | clos x e σ1 =>
        step e2 σ (fun v2 =>
        Continue e (fun x' => if String.eqb x x' then Some v2 else σ1 x') k)
      end)
  end.

Definition id_tm := lam "x" (var "x").

Fixpoint eval_cont e σ k (n : nat) :=
  match step e σ k with
  | Halt v => Halt v
  | Continue e' σ' k' =>
    match n with
    | O => Continue e' σ' k'
    | S n' => eval_cont e' σ' k' n'
    end
  end.

Definition eval e n := eval_cont e (fun _ => None) (fun v => Halt (Some v)) n.

Compute eval (app (app id_tm id_tm) id_tm) 2.

