From Basics Require Import Basics.
(* term *)
Inductive tm {var lbl} :=
| tm_var (p : lbl) (x : var)
| tm_lam (p : lbl) (x : var) (t : tm)
| tm_app (p : lbl) (t1 t2 : tm)
| tm_link (p : lbl) (t1 t2 : tm)
| tm_mt (p : lbl)
| tm_bind (p : lbl) (x : var) (t1 t2 : tm)
.

(* labelled term *)
Variant ltm {var lbl} :=
| ltm_var (x : var)
| ltm_lam (x : var) (p' : lbl)
| ltm_app (p1 p2 : lbl)
| ltm_link (p1 p2 : lbl)
| ltm_mt
| ltm_bind (x : var) (p1 p2 : lbl)
.

Variant val {var lbl} :=
| v_fn (x : var) (t : @tm var lbl)
.

Variant lval {var lbl} :=
| lv_fn (x : var) (p : lbl)
.

Definition get_lbl {var lbl} (t : @tm var lbl) :=
  match t with
    tm_var p _ | tm_lam p _ _ | tm_app p _ _ | tm_link p _ _ | tm_mt p | tm_bind p _ _ _ => p
  end.

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

Notation "t '∈' g" := (is_repr t g)
  (at level 100, g at next level, right associativity).

Variant avnt {var lbl} :=
| AInit
| ARead (p : lbl) (x : var)
| ACall (p1 p2 : lbl)
.

Definition abs_env {var lbl} : Type := (var -> list lbl) * list (@avnt var lbl).

Definition abs_val {var lbl} : Type := @abs_env var lbl * list (@lval var lbl * lbl).

Definition abs_sem {var lbl} := lbl -> (@abs_env var lbl * @abs_val var lbl).

Definition geq {var lbl} (v1 v2 : @abs_val var lbl) :=
  match v1, v2 with
  | ((σ1, E1), λ1), ((σ2, E2), λ2) =>
    (forall x p, In p (σ2 x) -> In p (σ1 x)) /\
    (forall E, In E E2 -> In E E1) /\
    (forall λ, In λ λ2 -> In λ λ1)
  end.

Notation "v1 '⊒' v2" := (geq v1 v2)
  (at level 100, v2 at next level, right associativity).

