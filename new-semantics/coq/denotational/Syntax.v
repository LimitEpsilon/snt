From Coq Require Import PArith Arith Lia String List.
From Denotational Require Import Vec.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition var := string.

Variant cstr_name : nat -> Type :=
  | Zero : cstr_name 0
  | Succ : cstr_name 1
  | Cons : cstr_name 2
.

Definition eqb_cstr {m n} (c1 : cstr_name m) (c2 : cstr_name n) :=
  match c1, c2 with
  | Zero, Zero | Succ, Succ | Cons, Cons => true
  | Zero, _ | Succ, _ | Cons, _ => false
  end.

Record cstr_type :=
  {
    cs_arity : nat;
    cs_name : cstr_name cs_arity;
  }.

Lemma eqb_cstr_eq (c1 c2 : cstr_type) :
  eqb_cstr c1.(cs_name) c2.(cs_name) = true <-> c1 = c2.
Proof.
  destruct c1, c2; simpl;
  match goal with
  | |- context [eqb_cstr ?x ?y] => destruct x, y
  end; simpl;
  split; intro EQ; inversion EQ; auto.
Qed.

Record cstr {V : Type} := mkCstr
  {
    cs_type : cstr_type;
    cs_args : vec V cs_type.(cs_arity);
  }.

Record dstr := mkDstr
  {
    ds_type : cstr_type;
    ds_idx : nat;
    ds_valid : S ds_idx <= ds_type.(cs_arity);
  }.

Record branch {B : Type} := mkBranch
  {
    br_cstr : cstr_type;
    br_vars : vec var br_cstr.(cs_arity);
    br_body : B;
  }.

Inductive tm :=
  | Var (x : var)
  | Fn (x : var) (e : tm) (* λ x . e *)
  | App (f a : tm)
  | Link (m e : tm) (* m ⋊ e *)
  | Mt (* ε *)
  | Bind (x : var) (v m : tm) (* let rec x = v ; m *)
  | Cstr (args : @cstr tm) (* C e1 e2 ... en *)
  | Case (e : tm) (b : list (@branch tm))
  (* match e with | C1 \vec{x1} => e1 | ... | Cn \vec{xn} => en end *)
.

