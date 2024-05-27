From Basics Require Import Basics.
From With_events Require Import Syntax.
Set Primitive Projections.

Section syntax.
  Context {var lbl : Type} `{EqVar : Eq var} `{EqLbl : Eq lbl}.

  Variant avnt :=
  | AInit
  | ARead (p : @ltm var lbl) (x : var)
  | ACall (p1 p2 : @ltm var lbl)
  .

  Record abs_env := mkEnv {
    _β : var -> list (@ltm var lbl);
    _E : list avnt;
  }.

  Definition aenv_bot := {| _β := fun _ => nil; _E := nil |}.

  Record abs_val := mkVal {
    _σ : abs_env;
    _λ : list (@val var lbl * lbl);
  }.

  Definition aval_bot := {| _σ := aenv_bot; _λ := nil |}.

  Record io := mkIO {
    _i : option abs_env;
    _o : option abs_val;
  }.

  Definition abs_sem : Type := @ltm var lbl -> io.

  Definition asem_bot : abs_sem := fun _ => {| _i := None; _o := None |}.
End syntax.

