From Coq Require Import PArith Arith Lia String List.
From Denotational Require Import Vec Syntax Domain.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition read_env (σ : env) (x : var) :=
  let fix read σ (acc : env -> env) :=
    match σ with
    | nv_mt => None
    | nv_sh s => Some (wvl_v (vl_sh (Read s x)), acc nv_mt)
    | nv_bd x' w' σ' =>
      if x =? x' then Some (w', acc σ') else
      let acc' σ' := acc (nv_bd x' w' σ')
      in read σ' acc'
    end
  in read σ id.

Definition unroll (w : walue) : option value :=
  match w with
  | wvl_v v => Some v
  | wvl_recv v => Some (open_wvl_value 0 w v)
  | wvl_bloc _ | wvl_floc _ => None
  end.

Local Definition dstr_helper1 m n k :
  n <= m -> S k <= m -> k <= m.
Proof. lia. Qed.

Local Definition dstr_helper2 m n k :
  n <= m -> S k <= m -> S (m - S k) <= m.
Proof. lia. Qed.

Definition dstr_shadow {B} (s : shadow) (b : @branch B) : env.
Proof.
  refine (
  let arity := b.(br_cstr).(cs_arity) in
  let fix for_each {n} (l : vec var n) (LE : n <= arity) acc {struct l} :=
    match l as l' in vec _ m return m <= arity -> _ with
    | [] => fun _ => acc
    | hd :: tl => _
    end%vec LE
  in for_each b.(br_vars) _ (nv_sh Init)); constructor.
  Unshelve. intro LE'.
  eapply for_each; [exact tl | eapply dstr_helper1; eauto | eapply nv_bd].
  - exact hd.
  - apply wvl_v. apply vl_sh.
    match goal with
    | _ : context [S ?m] |- _ =>
    refine (Dstr s
      {|
        ds_type := b.(br_cstr);
        ds_idx := b.(br_cstr).(cs_arity) - (S m);
        ds_valid := _
      |})
    end; eapply dstr_helper2; eauto.
  - exact acc.
Defined.

Definition dstr_cstr {B} (c : @cstr walue) (b : @branch B) : option env.
Proof.
  refine(
  let b_name := b.(br_cstr).(cs_name) in
  let c_name := c.(cs_type).(cs_name) in
  match eqb_cstr c_name b_name as b return eqb_cstr c_name b_name = b -> _ with
  | true => fun EQ =>
    let fix add_binding {m n} acc (xs : vec _ m) (ws : vec _ n) (EQ : m = n) :=
      match xs in vec _ m' return m' = n -> _ with
      | [] => fun _ => acc
      | x :: xs => fun EQ =>
        match ws in vec _ n' return m = n' -> _ with
        | [] => fun CONTRA => _
        | w :: ws => fun RR =>
          add_binding (nv_bd x w acc) xs ws _
        end _
      end EQ
    in Some (add_binding (nv_sh Init) b.(br_vars) c.(cs_args) _)
  | false => fun _ => None
  end%vec eq_refl).
  - subst b_name. subst c_name.
    rewrite eqb_cstr_eq in *.
    rewrite EQ. reflexivity.
    Unshelve.
    all:congruence.
Defined.

Definition map_branches (k : trace -> trace) b :=
  let for_branch (b : cstr_type * trace) :=
    let (c, t) := b in (c, k t)
  in List.map for_branch b
.

Definition bind (k : walue -> trace) : trace -> trace :=
  fix bind t :=
    match t with
    | Bot => Bot
    | Wal w => k w
    | Match s b => Match s (map_branches bind b)
    | Guard σ t => Guard σ (bind t)
    end.

Definition dstr_trace (d : dstr) : trace -> trace.
Proof.
  refine (
  let k w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_sh (Dstr s d)))
    | Some (vl_cstr c) =>
      let c_name := c.(cs_type).(cs_name) in
      let d_name := d.(ds_type).(cs_name) in
      match eqb_cstr c_name d_name as b return eqb_cstr c_name d_name = b -> _ with
      | true => fun EQ => Wal (get_idx c.(cs_args) d.(ds_idx) _)
      | false => fun _ => Bot
      end eq_refl
    | _ => Bot
    end
  in bind k);
  subst c_name; subst d_name;
  rewrite eqb_cstr_eq in *;
  rewrite EQ; exact d.(ds_valid).
Defined.

Definition test_dstr_shadow := dstr_shadow Init
  {|
    br_cstr := {| cs_name := Cons; cs_arity := 2 |};
    br_vars := ["x"; "y"]%vec;
    br_body := tt;
  |}.

Definition test_dstr_cstr := dstr_cstr
  {|
    cs_type := {| cs_name := Cons; cs_arity := 2 |};
    cs_args := [wvl_bloc 0; wvl_bloc 1]%vec;
  |}
  {|
    br_cstr := {| cs_name := Cons; cs_arity := 2 |};
    br_vars := ["x"; "y"]%vec;
    br_body := tt;
  |}.

(*
Eval vm_compute in test_dstr_shadow.
Eval vm_compute in test_dstr_cstr.
 *)

Compute dstr_trace
  {|
    ds_type := {| cs_name := Cons; cs_arity := 2 |};
    ds_idx := 1;
    ds_valid := ltac:(repeat constructor);
  |}
  (Wal (wvl_v (vl_cstr
  {|
    cs_type := {| cs_name := Cons; cs_arity := 2 |};
    cs_args := [wvl_bloc 0; wvl_bloc 1]%vec;
  |}))).

(* type of fold_left *)
(* forall A B, (A -> B -> A) -> list B -> A -> A *)

Definition cstr_trace (c : @cstr trace) : trace :=
  let arity := c.(cs_type).(cs_arity) in
  let fix fold_arg {n} (v : vec trace n) (k : vec walue n -> vec walue arity) {struct v} :=
    match v in vec _ m return (vec walue m -> vec walue arity) -> _ with
    | [] => fun k =>
      Wal (wvl_v (vl_cstr {| cs_type := c.(cs_type) ; cs_args := k vnil |}))
    | hd :: tl => fun k =>
      let check_trace w := fold_arg tl (fun v => k (w :: v))
      in bind check_trace hd
    end%vec k
  in fold_arg c.(cs_args) (fun v => v).

Definition link_trace (link : walue -> trace) (k : walue -> trace) : trace -> trace :=
  fix link_trace t :=
    match t with
    | Bot => Bot
    | Wal w => bind k (link w)
    | Match s b =>
      let check_match w :=
        match unroll w with
        | Some (vl_sh s) => Match s (map_branches link_trace b)
        | Some (vl_cstr c) =>
          let fold_branch acc (b : cstr_type * trace) :=
            let (c', t) := b in
            match acc with
            | None =>
              if eqb_cstr c.(cs_type).(cs_name) c'.(cs_name)
              then Some (link_trace t) else None
            | Some t => Some t
            end
          in match List.fold_left fold_branch b None with
          | None => Bot
          | Some t => t
          end
        | _ => Bot
        end
      in bind check_match (link (wvl_v (vl_sh s)))
    | Guard σ t =>
      let check_guard w :=
        match unroll w with
        | Some (vl_sh s) => Guard (nv_sh s) (link_trace t)
        | Some (vl_exp σ) => Guard σ (link_trace t)
        | _ => Bot
        end
      in bind check_guard (link (wvl_v (vl_exp σ)))
    end.

Definition read_trace x :=
  let read w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_sh (Read s x)))
    | Some (vl_exp σ) =>
      match read_env σ x with
      | Some (w, σ) => Guard σ (Wal w)
      | None => Bot
      end
    | _ => Bot
    end
  in bind read.

Definition call_trace
  (link : env -> walue -> trace)
  (fn arg : trace) : trace :=
  let check_fn fn :=
    match unroll fn with
    | Some (vl_sh s) =>
      let check_arg arg := Wal (wvl_v (vl_sh (Call s arg)))
      in bind check_arg arg
    | Some (vl_clos x t σ) =>
      let check_arg arg :=
        let σ' := nv_bd x arg σ
        in link_trace (link σ') Wal t
      in bind check_arg arg
    | _ => Bot
    end
  in bind check_fn fn.

Definition close_rec ℓ :=
  let close w :=
    match unroll w with
    | Some v => Wal (wvl_recv (close_value 0 ℓ v))
    | None => Bot
    end
  in bind close.

Definition bd_trace x (w : trace) (σ : trace) :=
  let check_bd w :=
    let check_mod σ :=
      match unroll σ with
      | Some (vl_sh s) => Wal (wvl_v (vl_exp (nv_bd x w (nv_sh s))))
      | Some (vl_exp σ) => Wal (wvl_v (vl_exp (nv_bd x w σ)))
      | _ => Bot
      end
    in bind check_mod σ
  in bind check_bd w.

Definition clos_trace x k :=
  let clos w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_clos x k (nv_sh s)))
    | Some (vl_exp σ) => Wal (wvl_v (vl_clos x k σ))
    | _ => Bot
    end
  in bind clos.

Definition filter_env :=
  let filter w :=
    match unroll w with
    | Some (vl_sh s) => Wal (wvl_v (vl_exp (nv_sh s)))
    | Some (vl_exp σ) => Wal (wvl_v (vl_exp σ))
    | _ => Bot
    end
  in bind filter.

Lemma fold_fact {n} (v : vec walue n) :
  let fold acc w' := Nat.max acc (size_walue w') in
  forall x y, x <= y -> x < S (fold_vec fold v y).
Proof.
  induction v; intros; simpl in *; [lia | apply IHv; subst fold; simpl; lia].
Qed.

Lemma link_helper {n} (v : vec walue n) :
  let fold acc w' := Nat.max acc (size_walue w') in
  forall m w (IN : In_vec w v),
    size_walue w < S (fold_vec fold v m).
Proof.
  intro.
  induction v; intros; simpl in *; [contradiction | destruct IN as [IN | IN]].
  - subst. apply fold_fact. subst fold; simpl. lia.
  - auto.
Qed.

Ltac t :=
  repeat match goal with
  | _ => solve [auto | lia]
  | _ => progress simpl
  | RR : ?x = _ |- context [?x] => rewrite RR
  | |- context [size_value (open_loc_value ?n ?ℓ ?v)] =>
    replace (size_value (open_loc_value n ℓ v)) with (size_value v);
    [|eapply open_loc_size_eq]
  | _ => apply link_helper
  end.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : env) : walue -> trace.
Proof.
  refine (
  match n with 0 => (fun _ => Bot) | S n =>
  let go :=
  fix link_wvl w (ACC : Acc lt (size_walue w)) {struct ACC} : trace :=
    match w as w' return w = w' -> _ with
    | wvl_v v => fun _ => link_vl v (Acc_inv ACC _)
    | wvl_recv v => fun _ =>
      let ℓ := Pos.max (alloc_value v) (alloc_env σ) in
      close_rec ℓ (link_vl (open_loc_value 0 ℓ v) (Acc_inv ACC _))
    | wvl_bloc n => fun _ => (* unreachable *) Bot
    | wvl_floc ℓ => fun _ => Wal (wvl_floc ℓ)
    end eq_refl
  with link_vl v (ACC : Acc lt (size_value v)) {struct ACC} : trace :=
    match v as v' return v = v' -> _ with
    | vl_clos x k σ' => fun _ =>
      clos_trace x k (link_nv σ' (Acc_inv ACC _))
    | vl_exp σ' => fun _ => link_nv σ' (Acc_inv ACC _)
    | vl_sh s => fun _ => link_shdw s (Acc_inv ACC _)
    | vl_cstr c => fun _ =>
      cstr_trace
      {|
        cs_type := c.(cs_type);
        cs_args :=
          map_vec_In c.(cs_args)
            (fun w IN => link_wvl w (Acc_inv ACC _));
      |}
    end eq_refl
  with link_nv σ' (ACC : Acc lt (size_env σ')) {struct ACC} : trace :=
    match σ' as σ'' return σ' = σ'' -> _ with
    | nv_mt => fun _ => Wal (wvl_v (vl_exp nv_mt))
    | nv_sh s => fun _ =>
      filter_env (link_shdw s (Acc_inv ACC _))
    | nv_bd x w σ' => fun _ =>
      let bound := link_wvl w (Acc_inv ACC _) in
      let exp := link_nv σ' (Acc_inv ACC _) in
      bd_trace x bound exp
    end eq_refl
  with link_shdw s (ACC : Acc lt (size_shadow s)) {struct ACC} : trace :=
    match s as s' return s = s' -> _ with
    | Init => fun _ => Wal (wvl_v (vl_exp σ))
    | Read s x => fun _ =>
      read_trace x (link_shdw s (Acc_inv ACC _))
    | Call s w => fun _ =>
      let fn := link_shdw s (Acc_inv ACC _) in
      let arg := link_wvl w (Acc_inv ACC _) in
      call_trace (link n) fn arg
    | Dstr s d => fun _ =>
      dstr_trace d (link_shdw s (Acc_inv ACC _))
    end eq_refl
  for link_wvl
  in fun w => go w (lt_wf (size_walue w))
  end).
  Unshelve.
  all: try abstract t.
  all: abstract t.
Defined.

