From Coq Require Import PArith Arith Lia String List.
From Denotational Require Import Vec Syntax.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition loc := positive.

Inductive shdw {wvl} :=
  | Init
  | Read (s : shdw) (x : var)
  | Call (s : shdw) (w : wvl)
  | Dstr (s : shdw) (d : dstr)
.

Arguments shdw : clear implicits.

Inductive nv {wvl} :=
  | nv_mt (* • *)
  | nv_sh (s : shdw wvl) (* [s] *)
  | nv_bd (x : var) (w : wvl) (σ : nv) (* bound value *)
.

Arguments nv : clear implicits.

Inductive vl {wvl K} :=
  | vl_exp (σ : nv wvl)
  | vl_sh (s : shdw wvl) (* s *)
  | vl_clos (x : var) (k : K) (σ : nv wvl)
  | vl_cstr (c : @cstr wvl)
.

Arguments vl : clear implicits.

Inductive wvl {K} :=
  | wvl_v (v : vl wvl K) (* v *)
  | wvl_recv (v : vl wvl K) (* μ.v *)
  | wvl_bloc (n : nat) (* bound location *)
  | wvl_floc (ℓ : loc) (* free location *)
.

Arguments wvl : clear implicits.

(* finite approximations *)
Inductive trace :=
  | Bot
  | Wal (w : wvl trace)
  | Match (s : shdw (wvl trace)) (b : list (cstr_type * trace))
  | Guard (σ : nv (wvl trace)) (t : trace)
.

(*
Variant traceF trace :=
  | Bot
  | Wal (w : wvl trace)
  | Match (s : shdw (wvl trace)) (b : list (cstr_type * trace))
  | Guard (σ : nv (wvl trace)) (t : trace)
.

CoInductive trace := mkTrace { _obs_tr : traceF trace }.
*)

Definition walue := wvl trace.
Definition value := vl walue trace.
Definition shadow := shdw walue.
Definition env := nv walue.

Section PRE_VAL_IND.
  Context {K : Type}.
  Context (Pwvl : wvl K -> Prop) (Pnv : nv (wvl K) -> Prop) (Pvl : vl (wvl K) K -> Prop) (Pshdw : shdw (wvl K) -> Prop).
  Context (Pwvl_v : forall v, Pvl v -> Pwvl (wvl_v v))
          (Pwvl_recv : forall v, Pvl v -> Pwvl (wvl_recv v))
          (Pwvl_bloc : forall n, Pwvl (wvl_bloc n))
          (Pwvl_floc : forall ℓ, Pwvl (wvl_floc ℓ)).
  Context (Pnv_mt : Pnv nv_mt)
          (Pnv_sh : forall s, Pshdw s -> Pnv (nv_sh s))
          (Pnv_bd : forall x w σ, Pwvl w -> Pnv σ -> Pnv (nv_bd x w σ)).
  Context (Pvl_exp : forall σ, Pnv σ -> Pvl (vl_exp σ))
          (Pvl_sh : forall s, Pshdw s -> Pvl (vl_sh s))
          (Pvl_clos : forall x k σ, Pnv σ -> Pvl (vl_clos x k σ))
          (Pvl_cstr : forall c (Pl : forall w, In_vec w c.(cs_args) -> Pwvl w),
            Pvl (vl_cstr c)).
  Context (PInit : Pshdw Init)
          (PRead : forall s x, Pshdw s -> Pshdw (Read s x))
          (PCall : forall s w, Pshdw s -> Pwvl w -> Pshdw (Call s w))
          (PDstr : forall s d, Pshdw s -> Pshdw (Dstr s d)).

  Definition shdw_ind wvl_ind :=
    fix shdw_ind s : Pshdw s :=
    match s with
    | Init => PInit
    | Read s x => PRead s x (shdw_ind s)
    | Call s w => PCall s w (shdw_ind s) (wvl_ind w)
    | Dstr s d => PDstr s d (shdw_ind s)
    end.

  Definition nv_ind wvl_ind :=
    fix nv_ind σ : Pnv σ :=
    match σ with
    | nv_mt => Pnv_mt
    | nv_sh s => Pnv_sh s (shdw_ind wvl_ind s)
    | nv_bd x w σ => Pnv_bd x w σ (wvl_ind w) (nv_ind σ)
    end.

  Definition vl_ind (wvl_ind : forall w, Pwvl w) : forall v, Pvl v.
  Proof.
    refine (
    let shdw_ind := shdw_ind wvl_ind in
    let nv_ind := nv_ind wvl_ind in
    fix vl_ind v :=
    match v with
    | vl_exp σ => Pvl_exp σ (nv_ind σ)
    | vl_sh s => Pvl_sh s (shdw_ind s)
    | vl_clos x k σ => Pvl_clos x k σ (nv_ind σ)
    | vl_cstr c =>
      let fix in_vec {n} (l : vec _ n) w (IN : In_vec w l) {struct l} : Pwvl w :=
        match l as l' return In_vec w l' -> Pwvl w with
        | [] => _
        | hd :: tl => _
        end%vec IN
      in
      Pvl_cstr c (in_vec c.(cs_args))
    end); intro IN'; simpl in IN'.
    - exfalso. assumption.
    - destruct IN' as [IN' | IN'].
      + rewrite IN'. apply wvl_ind.
      + eapply in_vec. exact IN'.
  Defined.

  Fixpoint wvl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind wvl_ind v)
    | wvl_recv v => Pwvl_recv v (vl_ind wvl_ind v)
    | wvl_bloc n => Pwvl_bloc n
    | wvl_floc ℓ => Pwvl_floc ℓ
    end.

  Lemma pre_val_ind :
    (forall w, Pwvl w) /\
    (forall σ, Pnv σ) /\
    (forall v, Pvl v) /\
    (forall s, Pshdw s).
  Proof.
    eauto using wvl_ind, (nv_ind wvl_ind), (vl_ind wvl_ind), (shdw_ind wvl_ind).
  Qed.
End PRE_VAL_IND.

Module DomNotations.
  Notation " 'μ' v " := (wvl_recv v) (at level 60, right associativity, only printing).
  Notation " v " := (wvl_v v) (at level 60, right associativity, only printing).
  Notation " n " := (wvl_bloc n) (at level 60, right associativity, only printing).
  Notation " ℓ " := (wvl_floc ℓ) (at level 60, right associativity, only printing).

  Notation " s " := (vl_sh s) (at level 60, right associativity, only printing).
  Notation " σ " := (vl_exp σ) (at level 60, right associativity, only printing).
  Notation " name args " := (vl_cstr {| cs_type := {| cs_name := name; cs_arity := _ |}; cs_args := args |})
    (at level 60, right associativity, only printing).
  Notation " name ',' idx " := {| ds_type := {| cs_name := name; cs_arity := _ |}; ds_idx := idx; ds_valid := _ |}
    (at level 60, right associativity, only printing).
  Notation "'⟨' 'λ' x k σ '⟩'" := (vl_clos x k σ) (at level 60, right associativity, only printing).

  Notation "•" := (nv_mt) (at level 60, right associativity, only printing).
  Notation "'⟪' s '⟫'" := (nv_sh s) (at level 60, right associativity, only printing).
  Notation "'⟪' x ',' w '⟫' ';;' σ " := (nv_bd x w σ) (at level 60, right associativity, only printing).

  Notation "⊥" := (Bot) (at level 60, right associativity, only printing).
  Notation "w" := (Wal w) (at level 60, right associativity, only printing).
  Notation "s '→' b" := (Match s b) (at level 60, right associativity, only printing).
  Notation "σ '→' t" := (Guard σ t) (at level 60, right associativity, only printing).
End DomNotations.

(** Operations for substitution *)
(* open the bound location i with ℓ *)
Definition open_loc_shdw f (i : nat) (ℓ : loc) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s w => Call (open s) (f i ℓ w)
  | Dstr s d => Dstr (open s) d
  end.

Definition open_loc_nv f (i : nat) (ℓ : loc) :=
  fix open (σ : env) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_loc_shdw f i ℓ s)
  | nv_bd x w σ' =>
    nv_bd x (f i ℓ w) (open σ')
  end.

Definition open_loc_vl f (i : nat) (ℓ : loc) :=
  fix open (v : value) :=
  match v with
  | vl_exp σ => vl_exp (open_loc_nv f i ℓ σ)
  | vl_sh s => vl_sh (open_loc_shdw f i ℓ s)
  | vl_clos x k σ => vl_clos x k (open_loc_nv f i ℓ σ)
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (f i ℓ) c.(cs_args)
    |}
  end.

Fixpoint open_loc_walue (i : nat) (ℓ : loc) (w : walue) : walue :=
  let open_loc_vl := open_loc_vl open_loc_walue in
  let open_loc_shdw := open_loc_shdw open_loc_walue in
  match w with
  | wvl_v v => wvl_v (open_loc_vl i ℓ v)
  | wvl_recv v => wvl_recv (open_loc_vl (S i) ℓ v)
  | wvl_bloc n => if Nat.eqb i n then wvl_floc ℓ else wvl_bloc n
  | wvl_floc ℓ => wvl_floc ℓ
  end.

Definition open_loc_value := open_loc_vl open_loc_walue.
Definition open_loc_env := open_loc_nv open_loc_walue.
Definition open_loc_shadow := open_loc_shdw open_loc_walue.

(* close the free location ℓ with the binding depth i *)
Definition close_shdw f (i : nat) (ℓ : loc) :=
  fix close (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (close s) x
  | Call s w => Call (close s) (f i ℓ w)
  | Dstr s d => Dstr (close s) d
  end.

Definition close_nv f (i : nat) (ℓ : loc) :=
  fix close (σ : env) : env :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (close_shdw f i ℓ s)
  | nv_bd x w σ' =>
    nv_bd x (f i ℓ w) (close σ')
  end.

Definition close_vl f (i : nat) (ℓ : loc) :=
  fix close (v : value) : value :=
  match v with
  | vl_exp σ => vl_exp (close_nv f i ℓ σ)
  | vl_sh s => vl_sh (close_shdw f i ℓ s)
  | vl_clos x k σ => vl_clos x k (close_nv f i ℓ σ)
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (f i ℓ) c.(cs_args);
    |}
  end.

Fixpoint close_walue (i : nat) (ℓ : loc) (w : walue) : walue :=
  let close_vl := close_vl close_walue in
  let close_shdw := close_shdw close_walue in
  match w with
  | wvl_v v => wvl_v (close_vl i ℓ v)
  | wvl_recv v => wvl_recv (close_vl (S i) ℓ v)
  | wvl_bloc n => wvl_bloc n
  | wvl_floc ℓ' => if Pos.eqb ℓ ℓ' then wvl_bloc i else wvl_floc ℓ'
  end.

Definition close_value := close_vl close_walue.
Definition close_env := close_nv close_walue.
Definition close_shadow := close_shdw close_walue.

(* open the bound location i with u *)
Definition open_wvl_shdw f (i : nat) (u : walue) :=
  fix open (s : shadow) : shadow :=
  match s with
  | Init => Init
  | Read s x => Read (open s) x
  | Call s w => Call (open s) (f i u w)
  | Dstr s d => Dstr (open s) d
  end.

Definition open_wvl_nv f (i : nat) (u : walue) :=
  fix open (σ : env) :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (open_wvl_shdw f i u s)
  | nv_bd x w σ' =>
    nv_bd x (f i u w) (open σ')
  end.

Definition open_wvl_vl f (i : nat) (u : walue) :=
  fix open (v : value) :=
  match v with
  | vl_exp σ => vl_exp (open_wvl_nv f i u σ)
  | vl_sh s => vl_sh (open_wvl_shdw f i u s)
  | vl_clos x k σ => vl_clos x k (open_wvl_nv f i u σ)
  | vl_cstr c =>
    vl_cstr
    {|
      cs_type := c.(cs_type);
      cs_args := map_vec (f i u) c.(cs_args)
    |}
  end.

Fixpoint open_wvl_walue (i : nat) (u : walue) (w : walue) : walue :=
  let open_wvl_vl := open_wvl_vl open_wvl_walue in
  let open_wvl_shdw := open_wvl_shdw open_wvl_walue in
  match w with
  | wvl_v v => wvl_v (open_wvl_vl i u v)
  | wvl_recv v => wvl_recv (open_wvl_vl (S i) u v)
  | wvl_bloc n => if Nat.eqb i n then u else wvl_bloc n
  | wvl_floc ℓ => wvl_floc ℓ
  end.

Definition open_wvl_value := open_wvl_vl open_wvl_walue.
Definition open_wvl_env := open_wvl_nv open_wvl_walue.
Definition open_wvl_shadow := open_wvl_shdw open_wvl_walue.

(* allocate fresh locations *)
Definition alloc_shdw f :=
  fix alloc (s : shadow) : positive :=
  match s with
  | Init => xH
  | Read s x => alloc s
  | Call s w => Pos.max (alloc s) (f w)
  | Dstr s d => alloc s
  end.

Definition alloc_nv f :=
  fix alloc (σ : env) : positive :=
  match σ with
  | nv_mt => xH
  | nv_sh s => alloc_shdw f s
  | nv_bd _ w σ' => Pos.max (f w) (alloc σ')
  end.

Definition alloc_vl f :=
  fix alloc (v : value) : positive :=
  match v with
  | vl_exp σ | vl_clos _ _ σ => alloc_nv f σ
  | vl_sh s => alloc_shdw f s
  | vl_cstr c =>
    let for_each acc w := Pos.max acc (f w) in
    fold_vec for_each c.(cs_args) xH
  end.

Fixpoint alloc_walue (w : walue) : positive :=
  let alloc_vl := alloc_vl alloc_walue in
  let alloc_shdw := alloc_shdw alloc_walue in
  match w with
  | wvl_v v | wvl_recv v => alloc_vl v
  | wvl_bloc _ => 1
  | wvl_floc ℓ => Pos.succ ℓ
  end%positive.

Definition alloc_value := alloc_vl alloc_walue.
Definition alloc_env := alloc_nv alloc_walue.
Definition alloc_shadow := alloc_shdw alloc_walue.

(* term size *)
Definition size_shdw f :=
  fix size (s : shadow) :=
  match s with
  | Init => O
  | Read s x => S (size s)
  | Call s w => S (Nat.max (size s) (f w))
  | Dstr s d => S (size s)
  end.

Definition size_nv f :=
  fix size (σ : env) :=
  match σ with
  | nv_mt => O
  | nv_sh s => S (size_shdw f s)
  | nv_bd _ w σ' => S (Nat.max (f w) (size σ'))
  end.

Definition size_vl f :=
  fix size (v : value) :=
  match v with
  | vl_exp σ | vl_clos _ _ σ => S (size_nv f σ)
  | vl_sh s => S (size_shdw f s)
  | vl_cstr c =>
    let for_each acc w := Nat.max acc (f w) in
    S (fold_vec for_each c.(cs_args) O)
  end.

Fixpoint size_walue (w : walue) :=
  let size_vl := size_vl size_walue in
  let size_shdw := size_shdw size_walue in
  match w with
  | wvl_v v | wvl_recv v => S (size_vl v)
  | wvl_bloc _ | wvl_floc _ => O
  end.

Definition size_value := size_vl size_walue.
Definition size_env := size_nv size_walue.
Definition size_shadow := size_shdw size_walue.

Definition open_loc_size_eq_wvl w :=
  forall n ℓ, size_walue w = size_walue (open_loc_walue n ℓ w).
Definition open_loc_size_eq_nv σ :=
  forall n ℓ, size_env σ = size_env (open_loc_env n ℓ σ).
Definition open_loc_size_eq_vl v :=
  forall n ℓ, size_value v = size_value (open_loc_value n ℓ v).
Definition open_loc_size_eq_shdw s :=
  forall n ℓ, size_shadow s = size_shadow (open_loc_shadow n ℓ s).

Lemma open_loc_size_eq_vec m n ℓ (l : vec _ m) :
  forall acc
    (IH : forall w, In_vec w l -> open_loc_size_eq_wvl w),
    fold_vec (fun acc w => Nat.max acc (size_walue w)) l acc =
    fold_vec (fun acc w => Nat.max acc (size_walue w))
      (map_vec (open_loc_walue n ℓ) l) acc.
Proof.
  induction l; intros; simpl; auto.
  rewrite <- IH; simpl; auto.
  eapply IHl. intros. apply IH. simpl. auto.
Qed.

Lemma open_loc_size_eq :
  (forall w, open_loc_size_eq_wvl w) /\
  (forall σ, open_loc_size_eq_nv σ) /\
  (forall v, open_loc_size_eq_vl v) /\
  (forall s, open_loc_size_eq_shdw s).
Proof.
  apply pre_val_ind; repeat intro; simpl; auto.
  match goal with
  | |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb x y)
  end; simpl; auto.
  f_equal. auto using open_loc_size_eq_vec.
Qed.

