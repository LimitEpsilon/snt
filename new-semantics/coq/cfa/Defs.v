From Basics Require Import Basics.
From With_events Require Import Syntax.
From With_events Require Import Defs.
From With_events Require Import EnvSemantics.
From CFA Require Import Syntax.

Section defs.
  Context {var lbl : Type}.

  Fixpoint is_repr (t : @tm var lbl) (g : lbl -> ltm) :=
    match t with
    | tm_var p x =>
      g p = ltm_var x
    | tm_lam p x t =>
      g p = ltm_lam x (get_lbl t) /\ is_repr t g
    | tm_app p t1 t2 =>
      g p = ltm_app (get_lbl t1) (get_lbl t2) /\ is_repr t1 g /\ is_repr t2 g
    | tm_link p t1 t2 =>
      g p = ltm_link (get_lbl t1) (get_lbl t2) /\ is_repr t1 g /\ is_repr t2 g
    | tm_mt p =>
      g p = ltm_mt
    | tm_bind p x t1 t2 =>
      g p = ltm_bind x (get_lbl t1) (get_lbl t2) /\ is_repr t1 g /\ is_repr t2 g
    end
  .

  Definition geq (v1 v2 : @abs_val var lbl) :=
    (forall x p, In p (v2.(_σ).(_β) x) -> In p (v1.(_σ).(_β) x)) /\
    (forall E, In E v2.(_σ).(_E) -> In E v1.(_σ).(_E)) /\
    (forall λ, In λ v2.(_λ) -> In λ v1.(_λ))
  .

  Definition aval_of_aenv {var lbl} (σ : @abs_env var lbl) :=
    {| _σ := σ; _λ := [] |}.

  #[local] Coercion aval_of_aenv : abs_env >-> abs_val.
  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Inductive conc {loc} (t : @abs_sem var lbl) (v : abs_val) : wvl var lbl loc _ -> Prop :=
  | conc_nil
  : conc t v nv_mt
  | conc_enil (E : vnt _ _ _ _)
    (VNT : conc t v E)
  : conc t v (nv_ev E)
  | cons_floc x ℓ p (σ : nv _ _ _ _)
    (LOC : In p (v.(_σ).(_β) x))
    (ENV : conc t v σ)
  : conc t v (nv_floc x (ℓ, p) σ)
  | conc_wval x w p (σ : nv _ _ _ _)
    (LOC : In p (v.(_σ).(_β) x))
    (VAL : conc t (t p).(_o) w)
    (ENV : conc t v σ)
  : conc t v (nv_bval x w σ)
  | conc_clos x e p (σ : nv _ _ _ _)
    (LAM : In (lv_fn x (get_lbl e), p) v.(_λ))
    (ENV : conc t (t p).(_i) σ)
  : conc t v (vl_clos (v_fn x e) σ)
  | conc_rec L p v'
    (VAL : forall ℓ (nIN : ~ In ℓ L), conc t v (open_loc_vl 0 (ℓ, p) v'))
    (ROLL : forall ℓ (nIN : ~ In ℓ L), conc t (t p).(_o) (open_loc_vl 0 (ℓ, p) v'))
  : conc t v (wvl_recv p v')
  | conc_Init
    (VNT : In AInit v.(_σ).(_E))
  : conc t v Init
  | conc_Read p (E : vnt _ _ _ _) x
    (VNT : In (ARead p x) v.(_σ).(_E))
    (ENV : conc t (t p).(_i) E)
  : conc t v (Read E x)
  | conc_Call p1 p2 (E : vnt _ _ _ _) (v' : vl _ _ _ _)
    (VNT : In (ACall p1 p2) v.(_σ).(_E))
    (FN : conc t (t p1).(_o) E)
    (ARG : conc t (t p2).(_o) v')
  : conc t v (Call E v')
  .

  Ltac conc_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | L : list _ |- _ => instantiate (1 := L)
    end.

  Lemma conc_lc {loc} t v w (CONC : @conc loc t v w) : wvalue w.
  Proof.
    induction CONC;
    repeat econstructor; des;
    conc_lc_tac; ii.
    exploit H; eauto. ii. conc_lc_tac.
  Qed.

  (* monotonicity of concretization in v *)
  Lemma conc_mon_fst {loc} t v w (CONC : @conc loc t v w) v' (GEQ : geq v' v) :
    conc t v' w.
  Proof.
    induction CONC; ii; ss;
    repeat match goal with
    | H : ?P, IH : ?P -> _ |- _ => specialize (IH H)
    end; econstructor; eauto;
    match goal with
    | GE : geq _ _ |- _ =>
      destruct GE as (A & B & C); eauto
    end.
  Qed.

  (* monotonicity of concretization in t *)
  Lemma conc_mon_snd {loc} t v w (CONC : @conc loc t v w) t'
    (GEQ : forall p, geq (t' p).(_i) (t p).(_i) /\ geq (t' p).(_o) (t p).(_o)) :
      conc t' v w.
  Proof.
    induction CONC; ii; ss;
    econstructor; eauto;
    ii; eapply conc_mon_fst;
    try_all; eauto; eapply GEQ.
  Qed.
End defs.

Notation "v1 '⊒' v2" := (geq v1 v2)
  (at level 100, v2 at next level, right associativity).
Notation "t v '⪰' w" := (conc t v w)
  (at level 100, v at next level, w at next level, right associativity).

Ltac des_geq :=
  match goal with
  | H : geq _ _ |- _ =>
    let geσ := fresh "geσ" in
    let geE := fresh "geE" in
    let geλ := fresh "geλ" in
    destruct H as (geσ & geE & geλ)
  end.

