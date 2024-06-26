From Coq Require Import PArith List.
From Denotational Require Import Vec Syntax Domain Linking.

Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition sem_link (link : env -> walue -> trace) (σ w : trace) :=
  let check_module m :=
    match unroll m with
    | Some (vl_sh s) => link_trace (link (nv_sh s)) Wal w
    | Some (vl_exp σ) => link_trace (link σ) Wal w
    | _ => Bot
    end
  in bind check_module σ.

(* precondition : bd, exp has no free locations *)
Definition sem_bind (link : env -> walue -> trace) x (bd exp : trace) :=
  let check_bd w :=
    match unroll w with
    | Some v =>
      let w := wvl_recv (close_value 0 xH v) in
      let check_exp σ :=
        match unroll σ with
        | Some (vl_sh s) => Wal (wvl_v (vl_exp (nv_bd x w (nv_sh s))))
        | Some (vl_exp σ) => Wal (wvl_v (vl_exp (nv_bd x w σ)))
        | _ => Bot
        end
      in link_trace (link (nv_bd x w (nv_sh Init))) check_exp exp
    | None => Bot
    end
  in link_trace (link (nv_bd x (wvl_floc xH) (nv_sh Init))) check_bd bd.

Definition sem_case (link : env -> walue -> trace) (matched : trace) (branches : list (@branch trace)) :=
  let check_match m :=
    match unroll m with
    | Some (vl_sh s) =>
      let map_each b :=
        let body := link_trace (link (dstr_shadow s b)) Wal b.(br_body)
        in (b.(br_cstr), body)
      in Match s (List.map map_each branches)
    | Some (vl_cstr c) =>
      let fold_each acc b :=
        match acc with
        | None =>
          match dstr_cstr c b with
          | None => None
          | Some σ => Some (link_trace (link σ) Wal b.(br_body))
          end
        | Some t => Some t
        end
      in match List.fold_left fold_each branches None with
      | None => Bot
      | Some t => t
      end
    | _ => Bot
    end
  in bind check_match matched.

Definition eval (link : env -> walue -> trace) :=
  fix eval (e : tm) : trace :=
  let guard := Guard (nv_sh Init) in
  match e with
  | Var x => Wal (wvl_v (vl_sh (Read Init x)))
  | Fn x M => Wal (wvl_v (vl_clos x (eval M) (nv_sh Init)))
  | App M N => call_trace link (eval M) (eval N)
  | Link M N => sem_link link (eval M) (eval N)
  | Mt => guard (Wal (wvl_v (vl_exp nv_mt)))
  | Bind x M N => sem_bind link x (eval M) (eval N)
  | Cstr c =>
    cstr_trace
      {|
        cs_type := c.(cs_type);
        cs_args := map_vec eval c.(cs_args)
      |}
  | Case E B =>
    let matched := eval E in
    let branches :=
      let for_each b :=
        {|
          br_cstr := b.(br_cstr);
          br_vars := b.(br_vars);
          br_body := eval b.(br_body);
        |}
      in List.map for_each B
    in sem_case link matched branches
  end.

Definition interp n := eval (link n).

