Inductive tm {var} :=
| tm_var (x : var)
| tm_lam (x : var) (t : tm)
| tm_app (t1 t2 : tm)
| tm_link (t1 t2 : tm)
| tm_mt
| tm_bind (x : var) (t1 t2 : tm)
.

Variant val {var} :=
| v_fn (x : var) (t : @tm var)
.
