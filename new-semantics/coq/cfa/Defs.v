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

  Definition geq_env (σ1 σ2 : @abs_env var lbl) :=
    (forall x p, In p (σ2.(_β) x) -> In p (σ1.(_β) x)) /\
    (forall E, In E σ2.(_E) -> In E σ1.(_E))
  .

  Definition geq_val (v1 v2 : @abs_val var lbl) :=
    geq_env v1.(_σ) v2.(_σ) /\
    (forall λ, In λ v2.(_λ) -> In λ v1.(_λ))
  .

  Definition geq_env_opt (σ1 σ2 : option (@abs_env var lbl)) :=
    match σ1, σ2 with
    | Some σ1, Some σ2 => geq_env σ1 σ2
    | _, None => True
    | _, _ => False
    end
  .

  Definition geq_val_opt (v1 v2 : option (@abs_val var lbl)) :=
    match v1, v2 with
    | Some v1, Some v2 => geq_val v1 v2
    | _, None => True
    | _, _ => False
    end
  .

  Definition geq_sem (t' t : @abs_sem var lbl) :=
    forall p,
      geq_env_opt (t' p).(_i) (t p).(_i) /\
      geq_val_opt (t' p).(_o) (t p).(_o)
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
  | conc_wval x w p o (σ : nv _ _ _ _)
    (LOC : In p (v.(_σ).(_β) x))
    (SOME : (t p).(_o) = Some o)
    (VAL : conc t o w)
    (ENV : conc t v σ)
  : conc t v (nv_bval x w σ)
  | conc_clos x e p i (σ : nv _ _ _ _)
    (LAM : In (lv_fn x (get_lbl e), p) v.(_λ))
    (SOME : (t p).(_i) = Some i)
    (ENV : conc t i σ)
  : conc t v (vl_clos (v_fn x e) σ)
  | conc_rec L p o v'
    (SOME : (t p).(_o) = Some o)
    (VAL : forall ℓ (nIN : ~ In ℓ L), conc t v (open_loc_vl 0 (ℓ, p) v'))
    (ROLL : forall ℓ (nIN : ~ In ℓ L), conc t o (open_loc_vl 0 (ℓ, p) v'))
  : conc t v (wvl_recv p v')
  | conc_Init
    (VNT : In AInit v.(_σ).(_E))
  : conc t v Init
  | conc_Read p i (E : vnt _ _ _ _) x
    (VNT : In (ARead p x) v.(_σ).(_E))
    (SOME : (t p).(_i) = Some i)
    (ENV : conc t i E)
  : conc t v (Read E x)
  | conc_Call p1 p2 o1 o2 (E : vnt _ _ _ _) (v' : vl _ _ _ _)
    (VNT : In (ACall p1 p2) v.(_σ).(_E))
    (SOME1 : (t p1).(_o) = Some o1)
    (SOME2 : (t p2).(_o) = Some o2)
    (FN : conc t o1 E)
    (ARG : conc t o2 v')
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
  Lemma conc_mon_fst {loc} t v w (CONC : @conc loc t v w) v' (GEQ : geq_val v' v) :
    conc t v' w.
  Proof.
    induction CONC; ii; ss;
    repeat match goal with
    | H : ?P, IH : ?P -> _ |- _ => specialize (IH H)
    end; econstructor;
    match goal with
    | GE : geq_val _ _ |- _ =>
      try solve [eauto];
      destruct GE as ([A B] & C); eauto
    end.
  Qed.

  Ltac des_geq_sem :=
    repeat match goal with
    | GEQ : geq_sem ?t' ?t, RR : _o (?t ?p) = Some _ |- _ =>
      lazymatch goal with
      | _ : _o (t' p) = Some _ |- _ => fail
      | _ =>
        let GEQo := fresh "GEQo" in
        pose proof (GEQ p) as [_ GEQo];
        red in GEQo; rewrite RR in GEQo;
        des_hyp; clarify
      end
    | GEQ : geq_sem ?t' ?t, RR : _i (?t ?p) = Some _ |- _ =>
      lazymatch goal with
      | _ : _i (t' p) = Some _ |- _ => fail
      | _ =>
        let GEQi := fresh "GEQi" in
        pose proof (GEQ p) as [GEQi _];
        red in GEQi; rewrite RR in GEQi;
        des_hyp; clarify
      end
    | _ => solve [econstructor; eauto]
    end.

  (* monotonicity of concretization in t *)
  Lemma conc_mon_snd {loc} t v w (CONC : @conc loc t v w) t'
    (GEQ : geq_sem t' t) :
  conc t' v w.
  Proof.
    induction CONC; ii; ss;
    des_geq_sem;
    clear GEQ;
    econstructor; eauto;
    try eapply conc_mon_fst;
    try solve [eauto | split; eauto].
    ii; eapply conc_mon_fst;
    try_all; eauto.
  Qed.
End defs.

Notation "v1 '⊒σ' v2" := (geq_env v1 v2)
  (at level 100, v2 at next level, right associativity).
Notation "v1 '⊒v' v2" := (geq_val v1 v2)
  (at level 100, v2 at next level, right associativity).
Notation "t v '⪰' w" := (conc t v w)
  (at level 100, v at next level, w at next level, right associativity).

Ltac des_geq :=
  match goal with
  | H : geq_env _ _ |- _ =>
    let geβ := fresh "geβ" in
    let geE := fresh "geE" in
    destruct H as (geβ & geE)
  | H : geq_val _ _ |- _ =>
    let geσ := fresh "geσ" in
    let geλ := fresh "geλ" in
    destruct H as (geσ & geλ)
  end.

Ltac des_geq_sem :=
  match goal with
  | GEQ : geq_sem ?t' ?t, RR : _o (?t ?p) = Some _ |- _ =>
    lazymatch goal with
    | _ : _o (t' p) = Some _ |- _ => fail
    | _ =>
      let GEQo := fresh "GEQo" in
      pose proof (GEQ p) as [_ GEQo];
      red in GEQo; rewrite RR in GEQo;
      des_hyp; clarify
    end
  | GEQ : geq_sem ?t' ?t, RR : _i (?t ?p) = Some _ |- _ =>
    lazymatch goal with
    | _ : _i (t' p) = Some _ |- _ => fail
    | _ =>
      let GEQi := fresh "GEQi" in
      pose proof (GEQ p) as [GEQi _];
      red in GEQi; rewrite RR in GEQi;
      des_hyp; clarify
    end
  end.

