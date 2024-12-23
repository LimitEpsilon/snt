From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.

Variant read_env_res {var lbl loc lang} :=
  | Env_err
  | Env_loc (ℓ : loc * lbl)
  | Env_wvl (w : wvl var lbl loc lang)
.

Fixpoint read_env {var lbl loc lang} `{Eq var} (σ : nv var lbl loc lang) (x : var) :=
  match σ with
  | nv_mt | nv_bloc _ _ _ => Env_err
  | nv_ev E => Env_wvl (wvl_v (vl_ev (Read E x)))
  | nv_floc x' ℓ σ' =>
    if eqb x x' then Env_loc ℓ else read_env σ' x
  | nv_bval x' w σ' =>
    if eqb x x' then Env_wvl w else read_env σ' x
  end.

Inductive eval {var lbl loc} `{Eq var} `{Eq lbl} `{Eq loc}
  (σ : nv var (@ltm var lbl) loc (@val var lbl)): ltm -> (vl var (@ltm var lbl) loc val) -> Prop :=
| ev_id p x v (READ : read_env σ x = Env_wvl (wvl_v v))
: eval σ (lblled p (tm_var x)) v
| ev_rec p x p' v (READ : read_env σ x = Env_wvl (wvl_recv p' v))
: eval σ (lblled p (tm_var x)) (open_wvl_vl 0 (wvl_recv p' v) v)
| ev_fn p x t
: eval σ (lblled p (tm_lam x t)) (vl_clos (v_fn x t) σ)
| ev_app p t1 t2 x e σ1 v2 v
  (FN : eval σ t1 (vl_clos (v_fn x e) σ1))
  (ARG : eval σ t2 v2)
  (BODY : eval (nv_bval x (wvl_v v2) σ1) e v)
: eval σ (lblled p (tm_app t1 t2)) v
| ev_appevent p t1 t2 E1 v2
  (FN : eval σ t1 (vl_ev E1))
  (ARG : eval σ t2 v2)
: eval σ (lblled p (tm_app t1 t2)) (vl_ev (Call E1 v2))
| ev_link p t1 t2 σ1 v
  (MOD : eval σ t1 (vl_exp σ1))
  (IMP : eval σ1 t2 v)
: eval σ (lblled p (tm_link t1 t2)) v
| ev_linkevent p t1 t2 E1 v
  (MOD : eval σ t1 (vl_ev E1))
  (IMP : eval (nv_ev E1) t2 v)
: eval σ (lblled p (tm_link t1 t2)) v
| ev_mt p
: eval σ (lblled p tm_mt) (vl_exp nv_mt)
| ev_bind p x t1 t2 ℓ v1 σ2
  (FRESH : ~ In ℓ (floc_nv σ))
  (BIND : eval (nv_floc x (ℓ, t1) σ) t1 v1)
  (MOD : eval (nv_bval x (wvl_recv t1 (close_vl 0 (ℓ, t1) v1)) σ) t2 (vl_exp σ2))
: eval σ (lblled p (tm_bind x t1 t2)) (vl_exp (nv_bval x (wvl_recv t1 (close_vl 0 (ℓ, t1) v1)) σ2))
| ev_bindevent p x t1 t2 ℓ v1 E2
  (FRESH : ~ In ℓ (floc_nv σ))
  (BIND : eval (nv_floc x (ℓ, t1) σ) t1 v1)
  (MOD : eval (nv_bval x (wvl_recv t1 (close_vl 0 (ℓ, t1) v1)) σ) t2 (vl_ev E2))
: eval σ (lblled p (tm_bind x t1 t2)) (vl_exp (nv_bval x (wvl_recv t1 (close_vl 0 (ℓ, t1) v1)) (nv_ev E2)))
| ev_zero p
: eval σ (lblled p tm_zero) (vl_nat 0)
| ev_succ p t n
  (PRED : eval σ t (vl_nat n))
: eval σ (lblled p (tm_succ t)) (vl_nat (S n))
| ev_succevent p t E
  (PRED : eval σ t (vl_ev E))
: eval σ (lblled p (tm_succ t)) (vl_ev (Succ E))
| ev_casezero p t z n s v
  (MATCH : eval σ t (vl_nat 0))
  (ZERO : eval σ z v)
: eval σ (lblled p (tm_case t z n s)) v
| ev_casesucc p t z n s m v
  (MATCH : eval σ t (vl_nat (S m)))
  (SUCC : eval (nv_bval n (wvl_v (vl_nat m)) σ) s v)
: eval σ (lblled p (tm_case t z n s)) v
| ev_casezeroevent p t z n s E v
  (MATCH : eval σ t (vl_ev E))
  (ZERO : eval σ z v)
: eval σ (lblled p (tm_case t z n s)) v
| ev_casesuccevent p t z n s E v
  (MATCH : eval σ t (vl_ev E))
  (SUCC : eval (nv_bval n (wvl_v (vl_ev (predE E))) σ) s v)
: eval σ (lblled p (tm_case t z n s)) v
.

Lemma read_env_lc {var lbl loc lang} `{Eq var} (σ : nv var lbl loc lang) (Σ : env σ) :
  forall x w (READ : read_env σ x = Env_wvl w), wvalue w.
Proof.
  induction σ; ii; ss;
  des_ifs; inv Σ; repeat econstructor; auto;
  eqb2eq var; clarify; eauto.
Qed.

Lemma eval_lc {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc} t (σ : nv var _ loc (@val var lbl)) v (EVAL : eval σ t v) :
  forall (LC : env σ), value v.
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_lc in READ; eauto. inv READ. auto.
  - eapply read_env_lc in READ; eauto.
    inversion READ; clarify.
    gensym_tac (L ++ floc_vl v) ν.
    assert (subst_intro_vl v) by eapply subst_intro.
    rw; eauto.
    eapply subst_wvl_lc; eauto.
  - econstructor. auto.
  - apply IHEVAL3. econstructor.
    econstructor. apply IHEVAL2. auto.
    exploit IHEVAL1; eauto. intros LC'.
    inv LC'. auto.
  - specialize (IHEVAL1 LC). specialize (IHEVAL2 LC).
    inv IHEVAL1. repeat econstructor; eauto.
  - apply IHEVAL2. exploit IHEVAL1; eauto.
    intros LC'. inv LC'. auto.
  - apply IHEVAL2. exploit IHEVAL1; eauto.
    intros LC'. inv LC'. econstructor; eauto.
  - repeat constructor.
  - assert (wvalue (wvl_recv t1 (close_vl 0 (ℓ, t1) v1))).
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl v1) by eapply close_open_loc_eq; rw.
    exploit IHEVAL1; eauto. constructor; auto. intros VAL1.
    assert (open_loc_lc_vl v1 VAL1) by (eapply open_loc_lc; auto).
    rw.
    eapply subst_loc_lc. auto.
    repeat constructor; eauto.
    exploit IHEVAL2.
    constructor; auto.
    intros VAL. inv VAL. auto.
  - assert (wvalue (wvl_recv t1 (close_vl 0 (ℓ, t1) v1))).
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl v1) by eapply close_open_loc_eq; rw.
    exploit IHEVAL1; eauto. constructor; auto. intros VAL1.
    assert (open_loc_lc_vl v1 VAL1) by (eapply open_loc_lc; auto).
    rw.
    eapply subst_loc_lc. auto.
    repeat constructor; eauto.
    exploit IHEVAL2.
    constructor; auto.
    intros VAL. inv VAL. auto.
  - econstructor.
  - econstructor.
  - specialize (IHEVAL LC). inversion IHEVAL.
    repeat econstructor; auto.
  - apply IHEVAL2. repeat econstructor; auto.
  - apply IHEVAL2. repeat econstructor; auto.
    specialize (IHEVAL1 LC). inv IHEVAL1. auto.
Qed.

Lemma read_env_map {var lbl loc lang} `{Eq var} `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :
  forall φ w x (READ : read_env σ x = Env_wvl w),
    read_env (map_nv φ σ) x = Env_wvl (map_wvl φ w).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  des_ifs; eqb2eq var; clarify;
  try eqb2eq loc; clarify; eauto.
Qed.

Lemma read_env_subst_loc {var lbl loc lang} `{Eq var} `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) x :
  forall r ν ℓ (READ : read_env σ x = r),
    read_env (subst_loc_nv ν ℓ σ) x =
    match r with
    | Env_err => Env_err
    | Env_loc ℓ' =>
      if eqb ℓ ℓ' then Env_loc ν else Env_loc ℓ'
    | Env_wvl u =>
      Env_wvl (subst_loc_wvl ν ℓ u)
    end.
Proof.
  induction σ; ii; ss;
  repeat des_goal; repeat des_hyp;
  repeat first [eqb2eq var | eqb2eq loc | eqb2eq lbl]; clarify;
  erewrite IHσ; eauto; ss;
  repeat rewrite eqb_refl; ss;
  des_goal; repeat first [eqb2eq loc | eqb2eq lbl]; clarify.
Qed.

Lemma read_env_subst_wvl {var lbl loc lang} `{Eq var} `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) x :
  forall r w ℓ (READ : read_env σ x = r),
    read_env (subst_wvl_nv w ℓ σ) x =
    match r with
    | Env_err => Env_err
    | Env_loc ℓ' =>
      if eqb ℓ ℓ' then Env_wvl w else Env_loc ℓ'
    | Env_wvl u =>
      Env_wvl (subst_wvl_wvl w ℓ u)
    end.
Proof.
  induction σ; ii; ss;
  repeat des_goal; repeat des_hyp;
  repeat first [eqb2eq var | eqb2eq loc | eqb2eq lbl]; clarify;
  erewrite IHσ; eauto; ss;
  repeat rewrite eqb_refl; ss;
  des_goal; repeat first [eqb2eq loc | eqb2eq lbl]; clarify.
Qed.

Lemma read_env_flloc {var lbl loc lang} `{Eq var} `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :
  forall w ℓ x (READ : read_env σ x = Env_wvl w) (IN : In ℓ (flloc_wvl w)),
    In ℓ (flloc_nv σ).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  eqb2eq var; clarify; eauto;
  rewrite in_app_iff; eauto.
Qed.

Lemma read_env_floc {var lbl loc lang} `{Eq var} `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :
  forall w ℓ x (READ : read_env σ x = Env_wvl w) (IN : In ℓ (floc_wvl w)),
    In ℓ (floc_nv σ).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  eqb2eq var; clarify; eauto;
  rewrite in_app_iff; eauto.
Qed.

Lemma eval_flloc_dec {var lbl loc} `{Eq var} `{Eq lbl} `{Eq loc} t (σ : nv var _ loc (@val var lbl)) v (EVAL : eval σ t v) :
  forall ℓ (IN : In ℓ (flloc_vl v)), In ℓ (flloc_nv σ).
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_flloc; eauto.
  - eapply open_wvl_flloc in IN.
    ss; des; eapply read_env_flloc; eauto.
  - apply IHEVAL3 in IN.
    rewrite in_app_iff in IN; des; auto.
  - rewrite in_app_iff in IN; des; auto.
  - rewrite in_app_iff in *.
    des; eauto.
    eapply close_flloc in IN. des; ss.
    exploit IHEVAL1; eauto.
    ii; des; clarify.
    exploit IHEVAL2; eauto. intros IN'.
    rewrite in_app_iff in *.
    des; eauto.
    eapply close_flloc in IN'. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
  - rewrite in_app_iff in *.
    des; eauto.
    eapply close_flloc in IN. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
    exploit IHEVAL2; eauto. intros IN'.
    rewrite in_app_iff in *.
    des; eauto.
    eapply close_flloc in IN'. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
  - apply IHEVAL2 in IN. rewrite in_app_iff in *.
    des; auto.
    rewrite predE_flloc in *. auto.
Qed.

Lemma eval_floc_dec {var lbl loc} `{Eq var} `{Eq lbl} `{Eq loc} t (σ : nv var _ loc (@val var lbl)) v (EVAL : eval σ t v) :
  forall ℓ (IN : In ℓ (floc_vl v)), In ℓ (floc_nv σ).
Proof.
  intros.
  assert (trans_floc_vl v) as RR by apply trans_floc.
  rewrite RR in IN. clear RR.
  assert (trans_floc_nv σ) as RR by apply trans_floc.
  rewrite RR. clear RR.
  rewrite in_map_iff in IN.
  destruct IN as [[ℓ' p'] [EQ IN]].
  ss; clarify.
  rewrite in_map_iff.
  exists (ℓ, p'). split; auto.
  eapply eval_flloc_dec; eauto.
Qed.

Lemma eval_map {var lbl loc} `{Eq var} `{Eq lbl} `{Name loc} t (σ : nv var _ loc (@val var lbl)) v (EVAL : eval σ t v) :
  forall φ (INJ : oto φ),
    eval (map_nv φ σ) t (map_vl φ v).
Proof.
  induction EVAL; ii; ss; try solve [econstructor; eauto].
  - econstructor. exploit (read_env_map σ); eauto.
  - assert (map_open_wvl_vl v) by (eapply map_open_wvl).
    rw. eapply ev_rec.
    exploit (read_env_map σ); eauto.
  - assert (map_close_vl v1) by (eapply map_close).
    rw; eauto.
    econstructor; eauto.
    red. intros IN. eapply map_floc in IN; eauto.
    rrw; eauto.
  - assert (map_close_vl v1) by (eapply map_close).
    rw; eauto.
    eapply ev_bindevent; eauto.
    red. intros IN. eapply map_floc in IN; eauto.
    rrw; eauto.
  - eapply ev_casesuccevent; eauto.
    exploit IHEVAL2; eauto.
    rewrite predE_map in *. auto.
Qed.

