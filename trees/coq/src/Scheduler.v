From Koika Require Import
  Prelude
  RVEncoding
  ProcTypes
.

Variant SchedOp {V : nat → Type} :=
| SchedInvalid
| TMC
| WSPAWN
| SPLIT
| JOIN
| BAR
| PRED
.

Arguments SchedOp : clear implicits.

#[export] Instance SchedOpLayout : Layout SchedOp :=
{|
  tag_sz := 3;
  default :=
    (Ob~1~1~1, cstr! @SchedInvalid);
  others := [
    (funct3_TMC, cstr! @TMC);
    (funct3_WSPAWN, cstr! @WSPAWN);
    (funct3_SPLIT, cstr! @SPLIT);
    (funct3_JOIN, cstr! @JOIN);
    (funct3_BAR, cstr! @BAR);
    (funct3_PRED, cstr! @PRED)
  ];
|}.

#[export] Instance SchedOpOk : LayoutOk SchedOp.
Proof. solve_layout_ok. Qed.

Record SchedReq {V : nat → Type} := mkSchedReq {
  schedWarp : Warp V;
  schedF : V ⌊ SchedOp ⌋;
  schedArg1 : V DataSz;
  schedArg2 : V DataSz;
}.

Arguments SchedReq : clear implicits.

#[export] Instance SchedReqLayout : Layout SchedReq :=
{|
  tag_sz := 0;
  default := (Ob, cstr! mkSchedReq);
  others := [];
|}.

#[export] Instance SchedReqOk : LayoutOk SchedReq.
Proof. solve_layout_ok. Qed.

Record SchedResp {V} := mkSchedResp {
  startWarp : Warp V;
  startWrite : V 1;
  startTop : V DataSz;
}.

Arguments SchedResp : clear implicits.

#[export] Instance SchedRespLayout : Layout SchedResp :=
{|
  tag_sz := 0;
  default := (Ob, cstr! mkSchedResp);
  others := [];
|}.

#[export] Instance SchedRespOk : LayoutOk SchedResp.
Proof. solve_layout_ok. Qed.

