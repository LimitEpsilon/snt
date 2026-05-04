From Stdlib Require Import
  Utf8
.
From Koika Require Import
  Common.CtxNotations
  Lang.Types
  Lang.Syntax
.

Local Generalizable Variable mod_t.

Definition linearize_pure `{M : Modules.t mod_t} {E' V}
  : ∀ E {ty} (e : t V E ty),
    match E with
    | Effectful => unit
    | Pure => ∀ ret, (V ty → linear V E' ret) → linear V E' ret
    end :=
  fix lin_pure E ty e :=
  match e with
  | Var x => fun _ k => k x
  | Cst c => fun _ k => LBind "" (LCst c) k
  | Rollback => fun _ _ => Lift LRollback
  | Undef => fun _ k => LBind "" LUndef k
  | UOp fn arg => fun ret k =>
    let k_arg arg' := LBind "" (LUOp fn arg') k in
    lin_pure Pure _ arg _ k_arg
  | BOp fn arg1 arg2 => fun ret k =>
    let k_arg1 arg1' :=
      let k_arg2 arg2' := LBind "" (LBOp fn arg1' arg2') k in
      lin_pure Pure _ arg2 _ k_arg2
    in
    lin_pure Pure _ arg1 _ k_arg1
  | VMet inst met args => fun ret k =>
    let args' := cmapv (lin_pure Pure) args in
    let k_args v := LBind "" (LVMet inst met v) k in
    let T v :=
      let retT := linear V E' ret in
      (context V v → retT) → retT
    in
    let argT v k := ∀ ret',
      let retT := linear V E' ret' in
      (V k → retT) → retT
    in cfoldr (T := T) (fun v k (arg' : argT v k) acc k_args' =>
      let acc' hd := acc (fun tl => k_args' (hd ::: tl)) in
      arg' ret acc'
    ) args' (fun k_init => k_init <[]>) k_args
  | @Bind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      t _ h τ1 → (V τ1 → t _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun a1 a2 ret k =>
      let k_a1 a1' := lin_pure Pure _ (a2 a1') _ k in
      lin_pure Pure _ a1 _ k_a1
    | Effectful => fun _ _ => tt
    end x y
  | @If _ _ _ eff τ cond x y =>
    match eff as h return
      t _ h τ → t _ h τ →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun con alt ret k =>
      let k_cond cond' :=
        LIf (LVar cond')
          (lin_pure Pure _ con _ (fun x => Lift (LVar x)))
          (lin_pure Pure _ alt _ (fun x => Lift (LVar x)))
        k
      in
      lin_pure Pure _ cond _ k_cond
    | Effectful => fun _ _ => tt
    end x y
  | _ => tt
  end%ctx.

Definition linearize `{M : Modules.t mod_t} {V}
  : ∀ {E ty} (e : t V E ty) ret,
    (V ty → linear V E ret) → linear V E ret :=
  fix linearize E ty e :=
  match e with
  | Var x => fun ret k =>
    linearize_pure Pure (Var x) _ k
  | Cst c => fun ret k =>
    linearize_pure Pure (Cst c) _ k
  | Rollback => fun ret k =>
    linearize_pure Pure (Rollback) _ k
  | Undef => fun ret k =>
    linearize_pure Pure Undef _ k
  | UOp fn arg => fun ret k =>
    linearize_pure Pure (UOp fn arg) _ k
  | BOp fn arg1 arg2 => fun ret k =>
    linearize_pure Pure (BOp fn arg1 arg2) _ k
  | VMet inst met args => fun ret k =>
    linearize_pure Pure (VMet inst met args) _ k
  | Ret x => fun ret k =>
    linearize_pure Pure x _ k
  | AMet inst met args => fun ret k =>
    let args' := cmapv (fun τ => linearize_pure (ty := τ) Pure) args in
    let k_args v := LBind "" (LAMet inst met v) k in
    let T v :=
      let retT := linear V Effectful ret in
      (context V v → retT) → retT
    in
    let argT v k := ∀ ret',
      let retT := linear V Effectful ret' in
      (V k → retT) → retT
    in cfoldr (T := T) (fun v k (arg' : argT v k) acc k_args' =>
      let acc' hd := acc (fun tl => k_args' (hd ::: tl)) in
      arg' ret acc'
    ) args' (fun k_init => k_init <[]>) k_args
  | @Bind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return t _ h τ1 → (V τ1 → t _ h τ2) → _ with
    | Pure => fun a1 a2 ret k =>
      linearize_pure Pure (Bind annot a1 a2) _ k
    | Effectful => fun a1 a2 ret k =>
      let k_a1 a1' := linearize _ _ (a2 a1') _ k in
      linearize _ _ a1 _ k_a1
    end x y
  | @If _ _ _ eff τ cond x y =>
    match eff as h return t _ h τ → t _ h τ → _ with
    | Pure => fun con alt ret k =>
      linearize_pure Pure (If cond con alt) _ k
    | Effectful => fun con alt ret k =>
      let k_cond cond' :=
        LIf (LVar cond')
          (linearize _ _ con _ (fun x => Lift (LVar x)))
          (linearize _ _ alt _ (fun x => Lift (LVar x)))
        k
      in
      linearize_pure Pure cond _ k_cond
    end x y
  end%ctx.

Lemma uncover_linearize_pure `{M : Modules.t mod_t}
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ ret k,
        linearize x ret k =
        linearize_pure Pure x ret k
    | Effectful => fun _ => True
    end e.
Proof. destruct e; auto; destruct eff; auto. Qed.

