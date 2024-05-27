Inductive tm {var lbl} :=
| tm_var (x : var)
| tm_lam (x : var) (t : ltm)
| tm_app (t1 t2 : ltm)
| tm_link (t1 t2 : ltm)
| tm_mt
| tm_bind (x : var) (t1 t2 : ltm)

with ltm {var lbl} :=
| lblled (p : lbl) (t : tm)
.

Scheme tm_ind_mut := Induction for tm Sort Prop
  with ltm_ind_mut := Induction for ltm Sort Prop.

Combined Scheme term_ind from tm_ind_mut, ltm_ind_mut.

Variant val {var lbl} :=
| v_fn (x : var) (t : @ltm var lbl)
.
