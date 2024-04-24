From Basics Require Import Basics.
From With_events Require Import Syntax.
From With_events Require Import EnvSemantics.
From CFA Require Import Syntax.

Fixpoint is_repr {var lbl} (t : @tm var lbl) (g : lbl -> ltm) :=
  match t with
  | tm_var p x =>
    g p = ltm_var x
  | tm_lam p x t =>
    g p = ltm_lam x (get_lbl t) /\ is_repr t g
  | tm_app p t1 t2 =>
    g p = ltm_app (get_lbl t1) (get_lbl t2) /\ is_repr t1 g /\ is_repr t2 g
  | tm_link p t1 t2 =>
    g p = ltm_link (get_lbl t1) (get_lbl t2) /\ is_repr t1 g /\ is_repr t2 g
  | tm_mt p =>
    g p = ltm_mt
  | tm_bind p x t1 t2 =>
    g p = ltm_bind x (get_lbl t1) (get_lbl t2) /\ is_repr t1 g /\ is_repr t2 g
  end
.

Definition geq {var lbl} (v1 v2 : @abs_val var lbl) :=
  match v1, v2 with
  | ((σ1, E1), λ1), ((σ2, E2), λ2) =>
    (forall x p, In p (σ2 x) -> In p (σ1 x)) /\
    (forall E, In E E2 -> In E E1) /\
    (forall λ, In λ λ2 -> In λ λ1)
  end.

Notation "v1 '⊒' v2" := (geq v1 v2)
  (at level 100, v2 at next level, right associativity).

