From Stdlib Require Import
  Utf8
.
From Koika Require Import
  Common.CtxNotations
  Lang.Types
  Lang.Syntax
  Lang.BigStepSemantics
.

Local Generalizable All Variables.

(* log and interpret expression *)
Definition linterp_pure `{Modules.t mod_t} {Σ} (St : State Σ) (U : Update Σ)
  : ∀ {E ty} (e : t _ E ty), Log →
    match E with
    | Effectful => unit
    | Pure => ∀ P : bits ty → Log → Prop, Prop
    end :=
  fix linterp_pure E ty e log :=
  match e with
  | Var x => fun P => P x log
  | Cst c => fun P => P c log
  | Rollback => fun _ => False
  | Undef => fun P => ∀ bs, P bs log
  | UOp fn arg => fun P =>
    let P' arg' log' := P (sigma1 fn arg') log' in
    linterp_pure Pure _ arg log P'
  | BOp fn arg1 arg2 => fun P =>
    let P1' arg1' log1' :=
      let P2' arg2' log2' := P (sigma2 fn arg1' arg2') log2' in
      linterp_pure Pure _ arg2 log1' P2'
    in
    linterp_pure Pure _ arg1 log P1'
  | VMet inst met args => fun P =>
    let args' := cmapv (linterp_pure Pure) args in
    let k_args v log' :=
      let st := rd_st St U inst in
      let is_ret := Sem.vmet_sem (Σ inst) met v st in
      (∃ ret, is_ret ret) ∧
      ∀ ret (VSTEP : is_ret ret), P ret (upd_log log' inst (inl met))
    in
    let T v := (context Bits.bits v → Log → Prop) → Log → Prop in
    cfoldr (T := T) (fun v _ (arg' : _ → _ → Prop) acc k_args' log' =>
      let k_arg varg := acc (fun tl => k_args' (varg ::: tl)) in
      arg' log' k_arg
    ) args' (fun k_init => k_init <[]>) k_args log
  | @Bind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      t _ h τ1 → (bits τ1 → t _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun a1 a2 P =>
      let P1' a1' log1' := linterp_pure Pure _ (a2 a1') log1' P in
      linterp_pure Pure _ a1 log P1'
    | Effectful => fun _ _ => tt
    end x y
  | @If _ _ _ eff τ cond x y =>
    match eff as h return
      t _ h τ → t _ h τ →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun con alt P =>
      let P' (cond' : bits 1) log' :=
        if Bits.single cond'
        then linterp_pure Pure _ con log' P
        else linterp_pure Pure _ alt log' P
      in
      linterp_pure Pure _ cond log P'
    | Effectful => fun _ _ => tt
    end x y
  | _ => tt
  end%ctx.

Definition interp_pure `{Modules.t mod_t} {Σ} (St : State Σ) (U : Update Σ)
  : ∀ {E ty} (e : t _ E ty),
    match E with
    | Effectful => unit
    | Pure => ∀ P : bits ty → Prop, Prop
    end :=
  fix interp_pure E ty e :=
  match e with
  | Var x => fun P => P x
  | Cst c => fun P => P c
  | Rollback => fun _ => False
  | Undef => fun P => ∀ bs, P bs
  | UOp fn arg => fun P =>
    let P' arg' := P (sigma1 fn arg') in
    interp_pure Pure _ arg P'
  | BOp fn arg1 arg2 => fun P =>
    let P1' arg1' :=
      let P2' arg2' := P (sigma2 fn arg1' arg2') in
      interp_pure Pure _ arg2 P2'
    in
    interp_pure Pure _ arg1 P1'
  | VMet inst met args => fun P =>
    let k_args v :=
      let st := rd_st St U inst in
      let is_ret := Sem.vmet_sem (Σ inst) met v st in
      (∃ ret, is_ret ret) ∧
      ∀ ret (VSTEP : is_ret ret), P ret
    in
    fold_pure args (interp_pure Pure) k_args
  | @Bind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      t _ h τ1 → (bits τ1 → t _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun a1 a2 P =>
      let P1' a1' := interp_pure Pure _ (a2 a1') P in
      interp_pure Pure _ a1 P1'
    | Effectful => fun _ _ => tt
    end x y
  | @If _ _ _ eff τ cond x y =>
    match eff as h return
      t _ h τ → t _ h τ →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun con alt P =>
      let P' (cond' : bits 1) :=
        if Bits.single cond'
        then interp_pure Pure _ con P
        else interp_pure Pure _ alt P
      in
      interp_pure Pure _ cond P'
    | Effectful => fun _ _ => tt
    end x y
  | _ => tt
  end%ctx.

(* σ, L ⊢ e ⇓ P means: starting from (σ, L), e will never abort and produces some (σ', L') ∈ P *)
Definition linterp `{Modules.t mod_t} {Σ} (St : State Σ)
  : ∀ {E ty} (e : t  _ E ty), Update Σ → Log → ∀ P, Prop :=
  fix linterp E ty (e : t _ E ty) U log :=
  match e with
  | Var x => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (Var x) log P'
  | Cst c => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (Cst c) log P'
  | Rollback => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (Rollback) log P'
  | Undef => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (Undef) log P'
  | UOp fn arg => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (UOp fn arg) log P'
  | BOp fn arg1 arg2 => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (BOp fn arg1 arg2) log P'
  | VMet inst met args => fun P =>
    let P' x' := P x' U in
    linterp_pure St U (VMet inst met args) log P'
  | Ret x => fun P =>
    let P' x' := P x' U in
    linterp_pure St U x log P'
  | AMet inst met args => fun P =>
    let args' := cmapv (fun τ => linterp_pure St U (ty := τ)) args in
    let k_args v log' :=
      let st := rd_st St U inst in
      let is_ret := Sem.amet_sem (Σ inst) met v st in
      (∃ ret st', is_ret ret st') ∧
      ∀ ret st' (ASTEP : is_ret ret st'),
        P ret (upd_st U inst st') (upd_log log' inst (inr met))
    in
    let T v := (context Bits.bits v → Log → Prop) → Log → Prop in
    cfoldr (T := T) (fun v _ (arg' : _ → _ → Prop) acc k_args' log' =>
      let k_arg aarg := acc (fun tl => k_args' (aarg ::: tl)) in
      arg' log' k_arg
    ) args' (fun k_init => k_init <[]>) k_args log
  | @Bind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return t _ h τ1 → (bits τ1 → t _ h τ2) → _ with
    | Pure => fun a1 a2 P =>
      let P' x' := P x' U in
      linterp_pure St U (Bind annot a1 a2) log P'
    | Effectful => fun a1 a2 P =>
      let P1' a1' U1' log1' := linterp _ _ (a2 a1') U1' log1' P
      in linterp _ _ a1 U log P1'
    end x y
  | @If _ _ _ eff τ cond x y =>
    match eff as h return t _ h τ → t _ h τ → _ with
    | Pure => fun con alt P =>
      let P' x' := P x' U in
      linterp_pure St U (If cond con alt) log P'
    | Effectful => fun con alt P =>
      let P' (cond' : bits 1) log' :=
        if Bits.single cond'
        then linterp _ _ con U log' P
        else linterp _ _ alt U log' P
      in
      linterp_pure St U cond log P'
    end x y
  end%ctx.

Definition interp `{Modules.t mod_t} {Σ} (St : State Σ)
  : ∀ {E ty} (e : t  _ E ty), Update Σ → ∀ P, Prop :=
  fix interp E ty (e : t _ E ty) U :=
  match e with
  | Var x => fun P =>
    let P' x' := P x' U in
    interp_pure St U (Var x) P'
  | Cst c => fun P =>
    let P' x' := P x' U in
    interp_pure St U (Cst c) P'
  | Rollback => fun P =>
    let P' x' := P x' U in
    interp_pure St U (Rollback) P'
  | Undef => fun P =>
    let P' x' := P x' U in
    interp_pure St U (Undef) P'
  | UOp fn arg => fun P =>
    let P' x' := P x' U in
    interp_pure St U (UOp fn arg) P'
  | BOp fn arg1 arg2 => fun P =>
    let P' x' := P x' U in
    interp_pure St U (BOp fn arg1 arg2) P'
  | VMet inst met args => fun P =>
    let P' x' := P x' U in
    interp_pure St U (VMet inst met args) P'
  | Ret x => fun P =>
    let P' x' := P x' U in
    interp_pure St U x P'
  | AMet inst met args => fun P =>
    let k_args v :=
      let st := rd_st St U inst in
      let is_ret := Sem.amet_sem (Σ inst) met v st in
      (∃ ret st', is_ret ret st') ∧
      ∀ ret st' (ASTEP : is_ret ret st'), P ret (upd_st U inst st')
    in
    fold_pure args (fun τ => interp_pure St U (ty := τ)) k_args
  | @Bind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return t _ h τ1 → (bits τ1 → t _ h τ2) → _ with
    | Pure => fun a1 a2 P =>
      let P' x' := P x' U in
      interp_pure St U (Bind annot a1 a2) P'
    | Effectful => fun a1 a2 P =>
      let P1' a1' U1' := interp _ _ (a2 a1') U1' P
      in interp _ _ a1 U P1'
    end x y
  | @If _ _ _ eff τ cond x y =>
    match eff as h return t _ h τ → t _ h τ → _ with
    | Pure => fun con alt P =>
      let P' x' := P x' U in
      interp_pure St U (If cond con alt) P'
    | Effectful => fun con alt P =>
      let P' (cond' : bits 1) :=
        if Bits.single cond'
        then interp _ _ con U P
        else interp _ _ alt U P
      in
      interp_pure St U cond P'
    end x y
  end%ctx.

Definition linterp_atom_pure `{Modules.t mod_t} {Σ} (St : State Σ) (U : Update Σ)
  : ∀ {E ty} (a : atom _ E ty), Log →
    match E with
    | Effectful => unit
    | Pure => ∀ P : bits ty → Log → Prop, Prop
    end :=
  fun E ty a log =>
  match a with
  | @LVar _ _ _ eff _ x =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P x log
      | Effectful => tt
      end
  | @LCst _ _ _ eff τ c =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P c log
      | Effectful => tt
      end
  | @LRollback _ _ _ eff _ =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => False
      | Effectful => tt
      end
  | @LUndef _ _ _ eff _ =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => ∀ bs, P bs log
      | Effectful => tt
      end
  | @LUOp _ _ _ eff fn arg =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P (sigma1 fn arg) log
      | Effectful => tt
      end
  | @LBOp _ _ _ eff fn arg1 arg2 =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P (sigma2 fn arg1 arg2) log
      | Effectful => tt
      end
  | @LVMet _ _ _ eff inst met args =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P =>
        let st := rd_st St U inst in
        let is_ret := Sem.vmet_sem (Σ inst) met args st in
        (∃ ret, is_ret ret) ∧
        ∀ ret (VSTEP : is_ret ret), P ret (upd_log log inst (inl met))
      | Effectful => tt
      end
  | LAMet _ _ _ => tt
  end.

Definition interp_atom_pure `{Modules.t mod_t} {Σ} (St : State Σ) (U : Update Σ)
  : ∀ {E ty} (a : atom _ E ty),
    match E with
    | Effectful => unit
    | Pure => ∀ P : bits ty → Prop, Prop
    end :=
  fun E ty a =>
  match a with
  | @LVar _ _ _ eff _ x =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P x
      | Effectful => tt
      end
  | @LCst _ _ _ eff τ c =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P c
      | Effectful => tt
      end
  | @LRollback _ _ _ eff _ =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => False
      | Effectful => tt
      end
  | @LUndef _ _ _ eff _ =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => ∀ bs, P bs
      | Effectful => tt
      end
  | @LUOp _ _ _ eff fn arg =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P (sigma1 fn arg)
      | Effectful => tt
      end
  | @LBOp _ _ _ eff fn arg1 arg2 =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P => P (sigma2 fn arg1 arg2)
      | Effectful => tt
      end
  | @LVMet _ _ _ eff inst met args =>
      match eff as h return
        match h return Type with Effectful => unit | Pure => _ end
      with
      | Pure => fun P =>
        let st := rd_st St U inst in
        let is_ret := Sem.vmet_sem (Σ inst) met args st in
        (∃ ret, is_ret ret) ∧
        ∀ ret (VSTEP : is_ret ret), P ret
      | Effectful => tt
      end
  | LAMet _ _ _ => tt
  end.

Definition linterp_atom `{Modules.t mod_t} {Σ} (St : State Σ)
  : ∀ {E ty} (a : atom  _ E ty), Update Σ → Log → ∀ P, Prop :=
  fun E ty a U log =>
  match a with
  | LVar x => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LVar x) log P'
  | LCst c => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LCst c) log P'
  | LRollback => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LRollback) log P'
  | LUndef => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LUndef) log P'
  | LUOp fn arg => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LUOp fn arg) log P'
  | LBOp fn arg1 arg2 => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LBOp fn arg1 arg2) log P'
  | LVMet inst met args => fun P =>
    let P' x' := P x' U in
    linterp_atom_pure St U (E := Pure) (LVMet inst met args) log P'
  | LAMet inst met args => fun P =>
    let st := rd_st St U inst in
    let is_ret := Sem.amet_sem (Σ inst) met args st in
    (∃ ret st', is_ret ret st') ∧
    ∀ ret st' (ASTEP : is_ret ret st'),
      P ret (upd_st U inst st') (upd_log log inst (inr met))
  end.

Definition interp_atom `{Modules.t mod_t} {Σ} (St : State Σ)
  : ∀ {E ty} (a : atom  _ E ty), Update Σ → ∀ P, Prop :=
  fun E ty a U =>
  match a with
  | LVar x => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LVar x) P'
  | LCst c => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LCst c) P'
  | LRollback => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LRollback) P'
  | LUndef => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LUndef) P'
  | LUOp fn arg => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LUOp fn arg) P'
  | LBOp fn arg1 arg2 => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LBOp fn arg1 arg2) P'
  | LVMet inst met args => fun P =>
    let P' x' := P x' U in
    interp_atom_pure St U (E := Pure) (LVMet inst met args) P'
  | LAMet inst met args => fun P =>
    let st := rd_st St U inst in
    let is_ret := Sem.amet_sem (Σ inst) met args st in
    (∃ ret st', is_ret ret st') ∧
    ∀ ret st' (ASTEP : is_ret ret st'), P ret (upd_st U inst st')
  end.

Definition linterp_linear_pure `{Modules.t mod_t} {Σ} (St : State Σ) (U : Update Σ)
  : ∀ {E ty} (l : linear _ E ty), Log →
    match E with
    | Effectful => unit
    | Pure => ∀ P : bits ty → Log → Prop, Prop
    end :=
  fix linterp_lin_pure E ty l log :=
  match l with
  | Lift x => linterp_atom_pure St U x log
  | @LBind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      atom _ h τ1 → (bits τ1 → linear _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun a1 a2 P =>
      let P1' a1' log1' := linterp_lin_pure Pure _ (a2 a1') log1' P in
      linterp_atom_pure St U a1 log P1'
    | Effectful => fun _ _ => tt
    end x y
  | @LIf _ _ _ eff τ1 τ2 cond x y z =>
    match eff as h return
      linear _ h τ1 → linear _ h τ1 → (bits τ1 → linear _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun con alt cont P =>
      let P' (cond' : bits 1) log' :=
        let P'' ret log'' := linterp_lin_pure Pure _ (cont ret) log'' P in
        if Bits.single cond'
        then linterp_lin_pure Pure _ con log' P''
        else linterp_lin_pure Pure _ alt log' P''
      in
      linterp_atom_pure St U cond log P'
    | Effectful => fun _ _ _ => tt
    end x y z
  end.

Definition interp_linear_pure `{Modules.t mod_t} {Σ} (St : State Σ) (U : Update Σ)
  : ∀ {E ty} (l : linear _ E ty),
    match E with
    | Effectful => unit
    | Pure => ∀ P : bits ty → Prop, Prop
    end :=
  fix interp_lin_pure E ty l :=
  match l with
  | Lift x => interp_atom_pure St U x
  | @LBind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      atom _ h τ1 → (bits τ1 → linear _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun a1 a2 P =>
      let P1' a1' := interp_lin_pure Pure _ (a2 a1') P in
      interp_atom_pure St U a1 P1'
    | Effectful => fun _ _ => tt
    end x y
  | @LIf _ _ _ eff τ1 τ2 cond x y z =>
    match eff as h return
      linear _ h τ1 → linear _ h τ1 → (bits τ1 → linear _ h τ2) →
      match h return Type with Effectful => unit | Pure => _ end
    with
    | Pure => fun con alt cont P =>
      let P' (cond' : bits 1) :=
        let P'' ret := interp_lin_pure Pure _ (cont ret) P in
        if Bits.single cond'
        then interp_lin_pure Pure _ con P''
        else interp_lin_pure Pure _ alt P''
      in
      interp_atom_pure St U cond P'
    | Effectful => fun _ _ _ => tt
    end x y z
  end.

Definition linterp_linear `{Modules.t mod_t} {Σ} (St : State Σ)
  : ∀ {E ty} (l : linear  _ E ty), Update Σ → Log → ∀ P, Prop :=
  fix linterp_lin E ty l U log :=
  match l with
  | Lift x => linterp_atom St x U log
  | @LBind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      atom _ h τ1 → (bits τ1 → linear _ h τ2) → _
    with
    | Pure => fun a1 a2 P =>
      let P' x' := P x' U in
      linterp_linear_pure St U (LBind annot a1 a2) log P'
    | Effectful => fun a1 a2 P =>
      let P1' a1' U1' log1' := linterp_lin _ _ (a2 a1') U1' log1' P
      in linterp_atom St a1 U log P1'
    end x y
  | @LIf _ _ _ eff τ1 τ2 cond x y z =>
    match eff as h return
      linear _ h τ1 → linear _ h τ1 → (bits τ1 → linear _ h τ2) → _
    with
    | Pure => fun con alt cont P =>
      let P' x' := P x' U in
      linterp_linear_pure St U (LIf cond con alt cont) log P'
    | Effectful => fun con alt cont P =>
      let P' (cond' : bits 1) log' :=
        let P1' a1' U1' log1' :=
          linterp_lin _ _ (cont a1') U1' log1' P
        in
        if Bits.single cond'
        then linterp_lin _ _ con U log' P1'
        else linterp_lin _ _ alt U log' P1'
      in
      linterp_atom_pure St U cond log P'
    end x y z
  end.

Definition interp_linear `{Modules.t mod_t} {Σ} (St : State Σ)
  : ∀ {E ty} (l : linear  _ E ty), Update Σ → ∀ P, Prop :=
  fix interp_lin E ty l U :=
  match l with
  | Lift x => interp_atom St x U
  | @LBind _ _ _ eff τ1 τ2 annot x y =>
    match eff as h return
      atom _ h τ1 → (bits τ1 → linear _ h τ2) → _
    with
    | Pure => fun a1 a2 P =>
      let P' x' := P x' U in
      interp_linear_pure St U (LBind annot a1 a2) P'
    | Effectful => fun a1 a2 P =>
      let P1' a1' U1' := interp_lin _ _ (a2 a1') U1'  P
      in interp_atom St a1 U P1'
    end x y
  | @LIf _ _ _ eff τ1 τ2 cond x y z =>
    match eff as h return
      linear _ h τ1 → linear _ h τ1 → (bits τ1 → linear _ h τ2) → _
    with
    | Pure => fun con alt cont P =>
      let P' x' := P x' U in
      interp_linear_pure St U (LIf cond con alt cont) P'
    | Effectful => fun con alt cont P =>
      let P' (cond' : bits 1) :=
        let P1' a1' U1' :=
          interp_lin _ _ (cont a1') U1' P
        in
        if Bits.single cond'
        then interp_lin _ _ con U P1'
        else interp_lin _ _ alt U P1'
      in
      interp_atom_pure St U cond P'
    end x y z
  end.

Definition interp_mod `{Modules.t mod_t} {Σ} (ifc : Modules.interface)
  (syn : mod_syn Bits.bits ifc) : Sem.t ifc :=
  {|
    Sem.state_t := ∀ m, Sem.state_t (Σ m);
    Sem.init m := Sem.init (Σ m);
    Sem.rules := merge_rules Σ (rules syn);
    Sem.vmet_sem vmet args St ret :=
      ∀ P (INTERP : interp_pure St (fun _ => None) (vmet_syn syn vmet args) P), P ret;
    Sem.amet_sem amet args St ret St' := ∃ U,
      (∀ P (INTERP : interp St (amet_syn syn amet args) (fun _ => None) P), P ret U) ∧
      St' = (rd_st St U);
    Sem.rule_sem rule St St' :=
      match rule with
      | inl rule => ∃ U,
        (∀ P (INTERP : interp St (rule_syn syn rule) (fun _ => None) P), P Ob U) ∧
        St' = (rd_st St U)
      | inr mrule =>
        let m := projT1 mrule in
        let rule := projT2 mrule in
        ∃ st',
          Sem.rule_sem (Σ m) rule (St m) st' ∧
          St' = rd_st St (upd_st (fun _ => None) m st')
      end;
  |}.

