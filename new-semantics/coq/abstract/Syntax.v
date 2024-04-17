Inductive tm {var lbl} :=
| tm_var (p : lbl) (x : var)
| tm_lam (p : lbl) (x : var) (t : tm)
| tm_app (p : lbl) (t1 t2 : tm)
| tm_link (p : lbl) (t1 t2 : tm)
| tm_mt (p : lbl)
| tm_bind (p : lbl) (x : var) (t1 t2 : tm)
.

Variant val {var lbl} :=
| v_fn (x : var) (t : @tm var lbl)
.

Definition get_lbl {var lbl} (t : @tm var lbl) :=
match t with
  tm_var p _ | tm_lam p _ _ | tm_app p _ _ | tm_link p _ _ | tm_mt p | tm_bind p _ _ _ => p
end.

Fixpoint subexpr {var lbl} (s t : @tm var lbl) :=
s = t \/
match t with
| tm_app _ t1 t2 | tm_link _ t1 t2 | tm_bind _ _ t1 t2 => subexpr s t1 \/ subexpr s t2
| tm_lam _ _ t' => subexpr s t'
| _ => False
end.

Notation "s '∈' t" := (subexpr s t)
  (at level 100, t at next level, right associativity).

