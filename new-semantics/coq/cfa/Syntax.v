Set Primitive Projections.

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

  Record abs_env := mkEnv {
    _β : var -> list lbl;
    _E : list avnt;
  }.

  Definition aenv_bot := {| _β := fun _ => nil; _E := nil |}.

  Record abs_val := mkVal {
    _σ : abs_env;
    _λ : list (lval * lbl);
  }.

  Definition aval_bot := {| _σ := aenv_bot; _λ := nil |}.

  Record io := mkIO {
    _i : abs_env;
    _o : abs_val;
  }.

  Definition abs_sem : Type := lbl -> io.

  Definition asem_bot : abs_sem := fun _ => {| _i := aenv_bot; _o := aval_bot |}.
End syntax.

