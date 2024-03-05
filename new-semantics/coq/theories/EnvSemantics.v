From Basics Require Import Basics.
From LN Require Import Defs.
From LN Require Import Syntax.
From LN Require Import SubstFacts.

Variant read_env_res {var loc lang} :=
  | Env_err
  | Env_loc (ℓ : loc)
  | Env_wvl (w : wvl var loc lang)
.

Fixpoint read_env {var loc lang} `{Eq var} (σ : nv var loc lang) (x : var) :=
  match σ with
  | nv_mt | nv_bloc _ _ _ => Env_err
  | nv_floc x' ℓ σ' =>
    if eqb x x' then Env_loc ℓ else read_env σ' x
  | nv_bval x' w σ' =>
    if eqb x x' then Env_wvl w else read_env σ' x
  end.

Inductive eval {var loc} `{Eq var} `{Eq loc} (σ : nv var loc (@val var)): tm -> (vl var loc val) -> Prop :=
| ev_id x v (READ : read_env σ x = Env_wvl (wvl_v v))
: eval σ (tm_var x) v
| ev_rec x v (READ : read_env σ x = Env_wvl (wvl_recv v))
: eval σ (tm_var x) (open_wvl_vl 0 (wvl_recv v) v)
| ev_fn x t
: eval σ (tm_lam x t) (vl_clos (v_fn x t) σ)
| ev_app t1 t2 x e σ1 v2 v
  (FN : eval σ t1 (vl_clos (v_fn x e) σ1))
  (ARG : eval σ t2 v2)
  (BODY : eval (nv_bval x (wvl_v v2) σ1) e v)
: eval σ (tm_app t1 t2) v
| ev_link t1 t2 σ1 v
  (MOD : eval σ t1 (vl_exp σ1))
  (IMP : eval σ1 t2 v)
: eval σ (tm_link t1 t2) v
| ev_mt
: eval σ tm_mt (vl_exp nv_mt)
| ev_bind x t1 t2 ℓ v1 σ2
  (FRESH : ~ In ℓ (floc_nv σ))
  (BIND : eval (nv_floc x ℓ σ) t1 v1)
  (MOD : eval (nv_bval x (wvl_recv (close_vl 0 ℓ v1)) σ) t2 (vl_exp σ2))
: eval σ (tm_bind x t1 t2) (vl_exp (nv_bval x (wvl_recv (close_vl 0 ℓ v1)) σ2))
.

Lemma read_env_lc {var loc lang} `{Eq var} (σ : nv var loc lang) (Σ : env σ) :
  forall x w (READ : read_env σ x = Env_wvl w), wvalue w.
Proof.
  induction σ; ii; ss;
  des_ifs; eqb2eq var; clarify;
  inv Σ; eauto.
Qed.

Lemma eval_lc {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall (LC : env σ), value v.
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_lc in READ; eauto. inv READ. auto.
  - eapply read_env_lc in READ; eauto.
    inversion READ; clarify.
    gensym_tac (L ++ floc_vl v) ν.
    assert (subst_intro_vl _ _ _ v) by eapply subst_intro.
    rw; eauto.
    eapply subst_wvl_lc; eauto.
  - econstructor. auto.
  - apply IHEVAL3. econstructor.
    econstructor. apply IHEVAL2. auto.
    exploit IHEVAL1; eauto. intros LC'.
    inv LC'. auto.
  - apply IHEVAL2. exploit IHEVAL1; eauto.
    intros LC'. inv LC'. auto.
  - repeat constructor.
  - assert (wvalue (wvl_recv (close_vl 0 ℓ v1))).
    econstructor. instantiate (1 := []). ii.
    assert (close_open_loc_eq_vl _ _ _ v1) by eapply close_open_loc_eq; rw.
    exploit IHEVAL1; eauto. constructor; auto. intros VAL1.
    assert (open_loc_lc_vl _ _ _ v1 VAL1) by (eapply open_loc_lc; auto).
    rw.
    eapply subst_loc_lc. auto.
    repeat constructor; eauto.
    exploit IHEVAL2.
    constructor; auto.
    intros VAL. inv VAL. auto.
Qed.

Lemma read_env_map {var loc lang} `{Eq var} `{Eq loc} (σ : nv var loc lang) :
  forall φ w x (READ : read_env σ x = Env_wvl w),
    read_env (map_nv φ σ) x = Env_wvl (map_wvl φ w).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  des_ifs; eqb2eq var; clarify;
  try eqb2eq loc; clarify; eauto.
Qed.

Lemma read_env_floc {var loc lang} `{Eq var} `{Eq loc} (σ : nv var loc lang) :
  forall w ℓ x (READ : read_env σ x = Env_wvl w) (IN : In ℓ (floc_wvl w)),
    In ℓ (floc_nv σ).
Proof.
  induction σ; ii; ss;
  des_ifs; ss;
  eqb2eq var; clarify; eauto;
  rewrite in_app_iff; eauto.
Qed.

Lemma eval_floc_dec {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall ℓ (IN : In ℓ (floc_vl v)), In ℓ (floc_nv σ).
Proof.
  induction EVAL; ii; ss; eauto.
  - eapply read_env_floc; eauto.
  - gensym_tac (floc_vl v) ν.
    assert (subst_intro_vl _ _ _ v) as RR by eapply subst_intro.
    rewrite RR in IN; eauto.
    assert (floc_subst_wvl_vl _ _ _ (open_loc_vl 0 ν v)) as HINT by eapply floc_subst_wvl.
    apply HINT in IN.
    des; ss.
    apply open_floc in IN0. des; clarify.
    eapply read_env_floc; eauto.
    eapply read_env_floc; eauto.
  - apply IHEVAL3 in IN.
    rewrite in_app_iff in IN; des; eauto.
  - rewrite in_app_iff in *.
    des; eauto.
    eapply close_floc in IN. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
    exploit IHEVAL2; eauto. intros IN'.
    rewrite in_app_iff in *.
    des; eauto.
    eapply close_floc in IN'. des.
    exploit IHEVAL1; eauto. ii; des; clarify.
Qed.

Lemma eval_map {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall φ (INJ : forall ℓ ν (fEQ : φ ℓ = φ ν), ℓ = ν),
    eval (map_nv φ σ) t (map_vl φ v).
Proof.
  induction EVAL; ii; ss; try solve [econstructor; eauto].
  - econstructor. exploit (read_env_map σ); eauto.
  - assert (map_open_wvl_vl _ _ _ v) by (eapply map_open_wvl).
    rw. eapply ev_rec.
    exploit (read_env_map σ); eauto.
  - assert (map_close_vl _ _ _ v1) by (eapply map_close).
    rw; eauto.
    econstructor; eauto.
    red. intros IN. eapply map_floc in IN; eauto.
    rrw; eauto.
Qed.

Lemma eval_subst {var loc} `{Eq var} `{Name loc} t (σ : nv var loc (@val var)) v (EVAL : eval σ t v) :
  forall ℓ' ν (FRESH : ~ In ν (floc_nv σ)),
    eval (subst_loc_nv ν ℓ' σ) t (subst_loc_vl ν ℓ' v).
Proof.
  ii. pose proof (eval_map t σ v EVAL (swap id ν ℓ')) as HINT.
  assert (swap_is_subst_nv _ _ _ σ) as RR by eapply swap_is_subst.
  assert (swap_is_subst_vl _ _ _ v) as RR' by eapply swap_is_subst.
  replace ν with (id ν) by reflexivity.
  replace ℓ' with (id ℓ') by reflexivity.
  replace σ with (map_nv id σ) by (eapply map_id_is_id).
  replace v with (map_vl id v) by (eapply map_id_is_id).
  rewrite <- RR. rewrite <- RR'.
  apply HINT.
  ii; unfold swap, id in fEQ; des_ifs; repeat eqb2eq loc; clarify.
  all:try solve [ii; ss].
  red. intros IN. eapply eval_floc_dec in EVAL; eauto.
Qed.
