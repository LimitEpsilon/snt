From Coq Require Import String List.
From Denotational Require Import Vec Syntax Domain Linking Interpreter.
Import DomNotations.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

(* Helper functions *)
Fixpoint get_wal t :=
  match t with
  | Bot => []
  | Wal w => [w]
  | Match _ b =>
    let fold acc (b : cstr_type * trace) :=
      let (c, t) := b in get_wal t ++ acc
    in List.fold_left fold b nil
  | Guard _ t => get_wal t
  end%list.

Definition zero_tm c :=
  Cstr {|
    cs_type := {| cs_name := c; cs_arity := 0 |};
    cs_args := []%vec;
  |}.

Definition succ_tm t :=
  Cstr {|
    cs_type := {| cs_name := Succ; cs_arity := 1 |};
    cs_args := [t]%vec;
  |}.

Definition one_tm := succ_tm (zero_tm Zero).
Definition two_tm := succ_tm one_tm.
Definition three_tm := succ_tm two_tm.

Definition zero_branch (t : tm) :=
  {|
    br_cstr := {| cs_name := Zero; cs_arity := _ |};
    br_vars := []%vec;
    br_body := t
  |}.

Definition succ_branch x (t : tm) :=
  {|
    br_cstr := {| cs_name := Succ; cs_arity := _ |};
    br_vars := [x]%vec;
    br_body := t
  |}.

Module SimpleExamples.

Definition pred_tm :=
  Fn "n" (Case (Var "n") [zero_branch (zero_tm Zero); succ_branch "m" (Var "m")])
.

(* Fixpoint add m n := match m with 0 => n | S m => S (add m n) end *)
Definition add_tm :=
Link (Bind "+"
  (Fn "m"
    (Fn "n"
      (Case (Var "m")
        [zero_branch (Var "n");
        succ_branch "m" (succ_tm (App (App (Var "+") (Var "m")) (Var "n")))]
      )))
  Mt) (Var "+")
.

Definition mult_tm :=
Link (Bind "×"
  (Fn "m"
    (Fn "n"
      (Case (Var "m")
        [zero_branch (Var "m");
        succ_branch "m"
        (App
          (App add_tm (Var "n"))
          (App
            (App (Var "×") (Var "m"))
            (Var "n")))])))
  Mt) (Var "×")
.

Definition infinity :=
Link (Bind "n" (succ_tm (Var "n")) Mt)
  (Var "n").

Definition three_plus_three := App (App add_tm three_tm) three_tm.
Definition three_times_three := App (App mult_tm three_tm) three_tm.

Definition x_plus_three := App (App add_tm three_tm) (Var "x").

Definition double_x := App (App add_tm (Var "x")) (Var "x").

Compute get_wal (interp 5 three_plus_three).
Compute get_wal (interp 10 three_times_three).
Compute get_wal (interp 6 x_plus_three).
Compute get_wal (interp 6 double_x).
Compute get_wal (interp 6 (App pred_tm infinity)).

Compute get_wal (interp 100
  (App
    (App add_tm
      (App
        (App add_tm one_tm)
        two_tm))
    (Var "x"))).

Definition sum_tm :=
Link (Bind "Σ"
  (Fn "f"
    (Fn "n"
      (Case (Var "n")
        [zero_branch (App (Var "f") (zero_tm Zero));
        succ_branch "n"
        (App
          (App (Var "+") (App (Var "f") (succ_tm (Var "n"))))
          (App
            (App (Var "Σ") (Var "f"))
            (Var "n")))])))
  Mt) (Var "Σ").

Definition unknown_function :=
  App (App sum_tm (Var "f")) three_tm.

Compute interp 5 unknown_function.

Definition unknown_function_and_number :=
  App (App sum_tm (Var "f")) (Var "n").

Definition export_function_number :=
  Bind "f" (Fn "n" (App (App add_tm (Var "n")) one_tm))
    (Bind "n" three_tm
      (Bind "+" add_tm Mt)).

Definition export_function_number_sem :=
  Eval vm_compute in
  interp 4 export_function_number.

Definition unknown_function_and_number_sem :=
  Eval vm_compute in
  interp 10 unknown_function_and_number.

Compute get_wal (sem_link (link 10)
  export_function_number_sem
  unknown_function_and_number_sem).

Compute
  let l := get_wal (interp 10
    (Fn "n" (App (App add_tm (Var "n")) one_tm)))
  in
  let for_each w :=
    match w with
    | wvl_v (vl_clos _ k _) => get_wal k
    | _ => []
    end
  in List.map for_each l.

Definition ω := Fn "x" (App (Var "x") (Var "x")).
Definition bomb := Bind "w" ω Mt.
Definition bomber := Bind "div" (App (Var "w") (Var "w")) Mt.
Compute interp 10 (Link bomb (Link bomber Mt)).
Compute interp 10 (Link (Link bomb bomber) Mt).
End SimpleExamples.

Module MutExample.
(* even? n = 1 if n is even 0 if n is odd *)
Definition top_module :=
Bind "Top"
  (Bind "Even"
    (Bind "even?"
      (Fn "x"
        (Case (Var "x")
          [zero_branch one_tm;
          succ_branch "n" (App (Link (Var "Top") (Link (Var "Odd") (Var "odd?"))) (Var "n"))]
        ))
      Mt)
    (Bind "Odd"
      (Bind "odd?"
        (Fn "y"
          (Case (Var "y")
            [zero_branch (zero_tm Zero);
            succ_branch "n" (App (Link (Var "Top") (Link (Var "Even") (Var "even?"))) (Var "n"))]
          ))
        Mt)
      Mt))
  Mt.

Definition test_even :=
  Link top_module
    (Link (Var "Top") (Link (Var "Even") (Var "even?"))).
Definition test_odd :=
  Link top_module
    (Link (Var "Top") (Link (Var "Odd") (Var "odd?"))).

Definition test_num := succ_tm (three_tm).

Compute get_wal (interp 10 (App test_even test_num)).
Compute get_wal (interp 10 (App test_odd test_num)).
Eval vm_compute in
  let σ := interp 10 (Bind "n" test_num Mt) in
  let w := interp 10 (App test_odd (Var "n")) in
  get_wal (sem_link (link 10) σ w).
End MutExample.

