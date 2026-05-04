(*! Language | Combinational primitives available in all Kôika programs !*)
Require Export Common Environments IndexUtils Types.

Inductive bits_comparison :=
  cLt | cGt | cLe | cGe.

Inductive bits_display_style :=
  dBin | dDec | dHex | dFull.

Record display_options :=
  { display_strings : bool;
    display_newline : bool;
    display_style : bits_display_style }.

Module PrimTyped.
  Inductive fbits1 :=
  | Not (sz: nat)
  | SExt (sz: nat) (width: nat)
  | ZExtL (sz: nat) (width: nat)
  | ZExtR (sz: nat) (width: nat)
  | Repeat (sz: nat) (times: nat)
  | Slice (sz: nat) (offset: nat) (width: nat)
  .

  Inductive fbits2 :=
  | And (sz: nat)
  | Or (sz: nat)
  | Xor (sz: nat)
  | Lsl (bits_sz: nat) (shift_sz: nat)
  | Lsr (bits_sz: nat) (shift_sz: nat)
  | Asr (bits_sz: nat) (shift_sz: nat)
  | Concat (sz1 sz2 : nat)
  | Sel (sz: nat)
  | SliceSubst (sz: nat) (offset: nat) (width: nat)
  | IndexedSlice (sz: nat) (width: nat)
  | Plus (sz : nat)
  | Minus (sz : nat)
  | Mul (sz1 sz2: nat)
  | EqBits (sz: nat) (negate: bool)
  | Compare (signed: bool) (c: bits_comparison) (sz: nat).
End PrimTyped.

Open Scope nat.

Module CircuitSignatures.
  Import PrimTyped.
  Import SigNotations.

  Definition CSigma1 (fn: fbits1) : CSig 1 :=
    match fn with
    | Not sz => {$ sz ~> sz $}
    | SExt sz width => {$ sz ~> (Nat.max sz width) $}
    | ZExtL sz width => {$ sz ~> (Nat.max sz width) $}
    | ZExtR sz width => {$ sz ~> (Nat.max sz width) $}
    | Repeat sz times => {$ sz ~> times * sz $}
    | Slice sz offset width => {$ sz ~> width $}
    end.

  Definition CSigma2 (fn: PrimTyped.fbits2) : CSig 2 :=
    match fn with
    | Sel sz => {$ sz ~> (log2 sz) ~> 1 $}
    | SliceSubst sz offset width => {$ sz ~> width ~> sz $}
    | IndexedSlice sz width => {$ sz ~> (log2 sz) ~> width $}
    | And sz => {$ sz ~> sz ~> sz $}
    | Or sz => {$ sz ~> sz ~> sz $}
    | Xor sz => {$ sz ~> sz ~> sz $}
    | Lsl bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Lsr bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Asr bits_sz shift_sz => {$ bits_sz ~> shift_sz ~> bits_sz $}
    | Concat sz1 sz2 => {$ sz1 ~> sz2 ~> (sz2 + sz1) $}
    | EqBits sz _ => {$ sz ~> sz ~> 1 $}
    | Plus sz => {$ sz ~> sz ~> sz $}
    | Minus sz => {$ sz ~> sz ~> sz $}
    | Mul sz1 sz2 => {$ sz1 ~> sz2 ~> sz1 + sz2 $}
    | Compare _ _ sz => {$ sz ~> sz ~> 1 $}
    end.
End CircuitSignatures.

Module BitFuns.
  Definition bitfun_of_predicate {sz} (p: bits sz -> bits sz -> bool) (bs1 bs2: bits sz) :=
    Ob~(p bs1 bs2).

  Definition sel {sz} (bs: bits sz) (idx: bits (log2 sz)) :=
    Ob~match Bits.to_index sz idx with
       | Some idx => Bits.nth bs idx
       | _ => false (* TODO: x *)
       end.

  Definition lsl {bits_sz shift_sz} (bs: bits bits_sz) (places: bits shift_sz) :=
    Bits.lsl (Bits.to_nat places) bs.

  Definition lsr {bits_sz shift_sz} (bs: bits bits_sz) (places: bits shift_sz) :=
    Bits.lsr (Bits.to_nat places) bs.

  Definition asr {bits_sz shift_sz} (bs: bits bits_sz) (places: bits shift_sz) :=
    Bits.asr (Bits.to_nat places) bs.

  Definition _eq {tau} {EQ: EqDec tau} (v1 v2: tau) :=
    Ob~(beq_dec v1 v2).

  Definition _neq {tau} {EQ: EqDec tau} (v1 v2: tau) :=
    Ob~(negb (beq_dec v1 v2)).
End BitFuns.

Module CircuitPrimSpecs.
  Import PrimTyped BitFuns.

  Definition sigma1 (fn: PrimTyped.fbits1) : CSig_denote (CircuitSignatures.CSigma1 fn) :=
    match fn with
    | Not _ => fun bs => Bits.neg bs
    | SExt sz width => fun bs => Bits.extend_end bs width (Bits.msb bs)
    | ZExtL sz width => fun bs => Bits.extend_end bs width false
    | ZExtR sz width => fun bs => Bits.extend_beginning bs width false
    | Repeat sz times => fun bs => Bits.repeat times bs
    | Slice _ offset width => Bits.slice offset width
    end.

  Definition sigma2 (fn: PrimTyped.fbits2) : CSig_denote (CircuitSignatures.CSigma2 fn) :=
    match fn with
    | Sel _ => sel
    | SliceSubst _ offset width => Bits.slice_subst offset width
    | IndexedSlice _ width => fun bs offset => Bits.slice (Bits.to_nat offset) width bs
    | And _ => Bits.and
    | Or _ => Bits.or
    | Xor _ => Bits.xor
    | Lsl _ _ => lsl
    | Lsr _ _ => lsr
    | Asr _ _ => asr
    | Concat _ _ => Bits.app
    | Plus _ => Bits.plus
    | Minus _ => Bits.minus
    | Mul _ _ => Bits.mul
    | EqBits _ false => _eq
    | EqBits _ true => _neq
    | Compare true cLt _ => bitfun_of_predicate Bits.signed_lt
    | Compare true cGt _ => bitfun_of_predicate Bits.signed_gt
    | Compare true cLe _ => bitfun_of_predicate Bits.signed_le
    | Compare true cGe _ => bitfun_of_predicate Bits.signed_ge
    | Compare false cLt _ => bitfun_of_predicate Bits.unsigned_lt
    | Compare false cGt _ => bitfun_of_predicate Bits.unsigned_gt
    | Compare false cLe _ => bitfun_of_predicate Bits.unsigned_le
    | Compare false cGe _ => bitfun_of_predicate Bits.unsigned_ge
    end.
End CircuitPrimSpecs.

