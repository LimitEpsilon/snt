Inductive tm {var lbl} :=
| tm_var (p : lbl) (x : var)
| tm_lam (p : lbl)(x : var) (t : tm)
| tm_app (p : lbl) (t1 t2 : tm)
| tm_link (p : lbl) (t1 t2 : tm)
| tm_mt (p : lbl)
| tm_bind (p : lbl) (x : var) (t1 t2 : tm)
.

Variant val {var lbl} :=
| v_fn (x : var) (t : @tm var lbl)
.
