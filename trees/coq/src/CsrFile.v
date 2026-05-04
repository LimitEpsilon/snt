From Koika Require Import
  Prelude
  ProcTypes
.

Record CsrReq {V : nat → Type} := mkCsrReq {
  csrCsr : V 12;
  csrWrite : V 1;
  csrData : V DataSz;
  csrWid : V (log2 WarpNum);
  csrMask : V ThreadNum;
}.

Arguments CsrReq : clear implicits.

#[export] Instance CsrReqLayout : Layout CsrReq :=
{|
  tag_sz := 0;
  default := (Ob, cstr! mkCsrReq);
  others := [];
|}.

#[export] Instance CsrReqOk : LayoutOk CsrReq.
Proof. solve_layout_ok. Qed.

Definition CsrResp := Vector ThreadNum DataSz.

