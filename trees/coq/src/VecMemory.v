From Koika Require Import
  Lang.Prelude
.

(* a : bitwidth of address, d : bitwidth of data *)
Record VecMemoryRequest {n a d : nat} {V : nat → Type} := mkVecMemReq {
  memWrite : V 1;
  memAddr : Vector n a V;
  memDatas : Vector n (8 * d) V;
  memWrByteen : V d;
  memMask : V n;
}.

Arguments VecMemoryRequest : clear implicits.

#[export] Instance VecMemReqLayout n a d : Layout (VecMemoryRequest n a d) :=
  {|
    tag_sz := 0;
    default := (Ob, cstr! (mkVecMemReq n a d));
    others := []
  |}.

#[export] Instance VecMemReqOk n a d : LayoutOk (VecMemoryRequest n a d).
Proof. solve_layout_ok. Qed.

Definition VecMemoryResponse n d := Vector n (8 * d).

