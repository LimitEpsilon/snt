From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import EnvSemantics.

Definition unroll {var loc lang} (w : wvl var loc lang) :=
  match w with
  | wvl_v v => v
  | wvl_recv v => open_wvl_vl 0 (wvl_recv v) v
  end.

Section LinkDefs.
  Variable var : Type.
  Variable loc : Type.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  (* local coercions were for this definition *)
  (* definition of linking *)
  Inductive link `{Eq loc} `{Eq var} (σ0 : nv var loc (@val var)) :
    wvl var loc (@val var) -> wvl var loc (@val var) -> Prop :=
  | link_Init
  : link σ0 Init σ0
  | link_Read E x (σ : nv _ _ _) w
    (LINKσ : link σ0 (nv_ev E) σ)
    (READ : read_env σ x = Env_wvl w)
  : link σ0 (Read E x) (unroll w)
  | link_CallEval (E : vnt _ _ _) x t σ (v v' v'' : vl _ _ _)
    (LINKE : link σ0 E (vl_clos (v_fn x t) σ))
    (LINKv : link σ0 v v')
    (EVAL : eval (nv_bval x v' σ) t v'')
  : link σ0 (Call E v) v''
  | link_CallEvent (E E' : vnt _ _ _) (v v' : vl _ _ _)
    (LINKE : link σ0 E E')
    (LINKv : link σ0 v v')
  : link σ0 (Call E v) (Call E' v')
  | link_mt
  : link σ0 nv_mt nv_mt
  | link_holeEnv (E : vnt _ _ _) (σ : nv _ _ _)
    (LINKE : link σ0 E σ)
  : link σ0 (nv_ev E) σ
  | link_holeEvent (E E' : vnt _ _ _)
    (LINKE : link σ0 E E')
  : link σ0 (nv_ev E) (nv_ev E')
  | link_floc x ℓ (σ σ' : nv _ _ _)
    (LINKσ : link σ0 σ σ')
  : link σ0 (nv_floc x ℓ σ) (nv_floc x ℓ σ')
  | link_bval x w w' (σ σ' : nv _ _ _)
    (LINKw : link σ0 w w')
    (LINKσ : link σ0 σ σ')
  : link σ0 (nv_bval x w σ) (nv_bval x w' σ')
  | link_clos e (σ σ' : nv _ _ _)
    (LINKσ : link σ0 σ σ')
  : link σ0 (vl_clos e σ) (vl_clos e σ')
  | link_rec (v v' : vl _ _ _) ℓ
    (nInv : ~ In ℓ (floc_vl v))
    (nInσ0 : ~ In ℓ (floc_nv σ0))
    (LINKv : link σ0 (open_loc_vl 0 ℓ v) v')
  : link σ0 (wvl_recv v) (wvl_recv (close_vl 0 ℓ v'))
  .
End LinkDefs.

Arguments link {var loc _ _}.
Arguments link_Init {var loc _ _}.
Arguments link_Read {var loc _ _}.
Arguments link_CallEval {var loc _ _}.
Arguments link_CallEvent {var loc _ _}.
Arguments link_mt {var loc _ _}.
Arguments link_holeEnv {var loc _ _}.
Arguments link_holeEvent {var loc _ _}.
Arguments link_floc {var loc _ _}.
Arguments link_bval {var loc _ _}.
Arguments link_clos {var loc _ _}.
Arguments link_rec {var loc _ _}.

