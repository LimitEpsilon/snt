From Coq Require Import ZArith String List.
Import ListNotations.

Local Open Scope string_scope.

Inductive tm :=
  | Var (x : string)
  | Fn (x : string) (e : tm)
  | App (f a : tm)
  | Link (m e : tm)
  | Mt
  | Bind (x : string) (v m : tm)
.

Inductive env :=
  | No_shadow (β : list (string * val))
    (* no shadow at the bottom *)
  | Shadow_env (β : list (string * val)) (s : shadow)
    (* shadow at the bottom *)

with val :=
  | Clos (x : string) (k : option val) (σ : env)
  | Mod (σ : env)
  | Shadow_val (s : shadow)

with shadow :=
  | Init
  | Read (s : shadow) (x : string)
  | Call (s : shadow) (v : val)
.

Local Coercion Var : string >-> tm.
Local Notation "'⟪' 'λ' x e '⟫'" := (Fn x e) (at level 60, right associativity).
Local Notation "'⟪' '@' M N '⟫'" := (App M N) (at level 60, right associativity).
Local Notation "'⟪' M '⋊' N '⟫'" := (Link M N) (at level 60, right associativity).
Local Notation "'⟪' ε '⟫'" := (Mt) (at level 60, right associativity).
Local Notation "'⟪' x '=' M ';' N '⟫'" := (Bind x M N) (at level 60, right associativity).

Definition ω := Fn "x" (App (Var "x") (Var "x")).
Definition ι := Fn "x" (Var "x").

Definition upd_env (σ : env) (x : string) (v : val) :=
  match σ with
  | No_shadow β => No_shadow ((x, v) :: β)
  | Shadow_env β s => Shadow_env ((x, v) :: β) s
  end.

Definition app_env β σ :=
  match σ with
  | No_shadow β' => No_shadow (β ++ β')
  | Shadow_env β' s => Shadow_env (β ++ β') s
  end.

Fixpoint read_list (β : list (string * val)) (x : string) :=
  match β with
  | [] => None
  | (x', v) :: β' =>
    if x =? x' then Some v else read_list β' x
  end.

Definition read_env (σ : env) (x : string) :=
  match σ with
  | No_shadow β => read_list β x
  | Shadow_env β s =>
    match read_list β x with
    | Some v => Some v
    | None => Some (Shadow_val (Read s x))
    end
  end.

Definition eval (link : env -> val -> option val) :=
  fix eval (e : tm) : option val :=
  match e with
  | Var x => Some (Shadow_val (Read Init x))
  | Fn x M => Some (Clos x (eval M) (Shadow_env [] Init))
  | App M N =>
    match eval M, eval N with
    | Some (Clos x B σ), Some v =>
      match B with
      | Some k => link (upd_env σ x v) k
      | None => None
      end
    | Some (Shadow_val s), Some v => Some (Shadow_val (Call s v))
    | Some (Mod _), Some _
    | Some _, None | None, Some _ | None, None => None
    end
  | Link M N =>
    match eval M, eval N with
    | Some (Mod σ), Some v => link σ v
    | Some (Shadow_val s), Some v => link (Shadow_env [] s) v
    | Some (Clos _ _ _), Some _
    | Some _, None | None, Some _ | None, None => None
    end
  | Mt => Some (Mod (No_shadow []))
  | Bind x M N =>
    match eval M, eval N with
    | Some v, Some (Mod σ) => Some (Mod (upd_env σ x v))
    | Some v, Some (Shadow_val s) => Some (Mod (Shadow_env [(x, v)] s))
    | Some _, Some (Clos _ _ _)
    | Some _, None | None, Some _ | None, None => None
    end
  end.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : env) : val -> option val :=
  match n with 0 => (fun _ => None) | S n =>
  fix link_val v : option val :=
    match v with
    | Clos x k σ' =>
      match link_env σ' with
      | None => None
      | Some σ' => Some (Clos x k σ')
      end
    | Mod σ' =>
      match link_env σ' with
      | None => None
      | Some σ' => Some (Mod σ')
      end
    | Shadow_val s => link_shadow s
    end
  with link_env σ' : option env :=
    let fix link_list β :=
      match β with
      | [] => Some []
      | (x, v) :: β =>
        match link_val v, link_list β with
        | None, _ | _, None => None
        | Some v, Some β => Some ((x, v) :: β)
        end
      end
    in match σ' with
    | No_shadow β =>
      match link_list β with None => None | Some β => Some (No_shadow β) end
    | Shadow_env β s =>
      match link_list β, link_shadow s with
      | None, _ | _, None => None
      | Some _, Some (Clos _ _ _) => None
      | Some β, Some (Mod σ) => Some (app_env β σ)
      | Some β, Some (Shadow_val s) => Some (Shadow_env β s)
      end
    end
  with link_shadow s : option val :=
    match s with
    | Init => Some (Mod σ)
    | Read s x =>
      match link_shadow s with
      | None | Some (Clos _ _ _) => None
      | Some (Mod σ) => read_env σ x
      | Some (Shadow_val s) => Some (Shadow_val (Read s x))
      end
    | Call s v =>
      match link_shadow s, link_val v with
      | None, _ | _, None | Some (Mod _), _ => None
      | Some (Clos x k σ), Some v =>
        match k with
        | None => None
        | Some k => link n (upd_env σ x v) k
        end
      | Some (Shadow_val s), Some v => Some (Shadow_val (Call s v))
      end
    end
  for link_val
  end.

Definition interp n := eval (link n).

Local Coercion Shadow_val : shadow >-> val.
Local Coercion Mod : env >-> val.
Compute interp 1 ω.
Compute interp 100 (App ω ω).
Compute interp 1 (App ι ι).
Definition test_module := Bind "id" ι Mt.
Definition open_program := App (Var "id") (Var "id").
Compute interp 2 (Link test_module open_program).

