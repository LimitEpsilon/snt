(*! Language | Types used by Kôika programs !*)
Require Export Stdlib.Strings.String.
Require Export Common IndexUtils.

(** * Anonymous function signatures **)

Record _Sig {argKind: Type} {nArgs: nat} :=
  { argSigs : vect argKind nArgs; retSig : argKind }.
Arguments _Sig : clear implicits.

Fixpoint _Sig_denote {nArgs argKind} (type_of_argKind: argKind -> Type)
         (args: vect argKind nArgs) (ret: argKind) :=
  match nArgs return vect argKind nArgs -> Type with
  | 0 => fun _ => type_of_argKind ret
  | S n => fun arg => type_of_argKind (vect_hd arg) ->
                  _Sig_denote type_of_argKind (vect_tl arg) ret
  end args.

Notation CSig n := (_Sig nat n).

Definition CSig_denote {n} (sg: CSig n) :=
  _Sig_denote (@Bits.bits) sg.(argSigs) sg.(retSig).

Notation arg1Sig := (fun fsig => (vect_hd fsig.(argSigs))).
Notation arg2Sig := (fun fsig => (vect_hd (vect_tl fsig.(argSigs)))).

Module SigNotations.
  Notation "{$  a1 ~> ret  $}" :=
    {| argSigs := vect_cons a1 vect_nil;
       retSig := ret |}.

  Notation "{$  a1 ~> a2 ~> ret  $}" :=
    {| argSigs := vect_cons a1 (vect_cons a2 vect_nil);
       retSig := ret |}.
End SigNotations.

