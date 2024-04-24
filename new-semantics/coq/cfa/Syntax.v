Section syntax.
  Context {var lbl : Type}.

  (* labelled term *)
  Variant ltm :=
  | ltm_var (x : var)
  | ltm_lam (x : var) (p' : lbl)
  | ltm_app (p1 p2 : lbl)
  | ltm_link (p1 p2 : lbl)
  | ltm_mt
  | ltm_bind (x : var) (p1 p2 : lbl)
  .
  
  Variant lval :=
  | lv_fn (x : var) (p : lbl)
  .
  
  Variant avnt :=
  | AInit
  | ARead (p : lbl) (x : var)
  | ACall (p1 p2 : lbl)
  .
 
  Definition abs_env : Type := (var -> list lbl) * list avnt.
 
  Definition abs_val : Type := abs_env * list (lval * lbl).
 
  Definition abs_sem : Type := lbl -> (abs_env * abs_val).
End syntax.

