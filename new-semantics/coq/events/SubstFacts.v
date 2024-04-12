From Basics Require Import Basics.
From With_events Require Import Defs.

Section SubstFacts.
  Variable var : Type.
  Variable loc : Type.
  Variable lang : Type.

  Definition open_floc_wvl (w : wvl var loc lang) :=
    forall i ℓ x, In x (floc_wvl (open_loc_wvl i ℓ w)) -> x = ℓ \/ In x (floc_wvl w).

  Definition open_floc_nv (σ : nv var loc lang) :=
    forall i ℓ x, In x (floc_nv (open_loc_nv i ℓ σ)) -> x = ℓ \/ In x (floc_nv σ).

  Definition open_floc_vl (v : vl var loc lang) :=
    forall i ℓ x, In x (floc_vl (open_loc_vl i ℓ v)) -> x = ℓ \/ In x (floc_vl v).

  Definition open_floc_vnt (E : vnt var loc lang) :=
    forall i ℓ x, In x (floc_vnt (open_loc_vnt i ℓ E)) -> x = ℓ \/ In x (floc_vnt E).

  Lemma open_floc :
    (forall w, open_floc_wvl w) /\
    (forall σ, open_floc_nv σ) /\
    (forall v, open_floc_vl v) /\
    (forall E, open_floc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_floc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_floc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_floc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_floc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (des_ifs)
    | _ => progress (eqb2eq loc; clarify)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition open_wvl_floc_wvl (w : wvl var loc lang) :=
    forall i u x, In x (floc_wvl (open_wvl_wvl i u w)) ->
      In x (floc_wvl u) \/ In x (floc_wvl w).

  Definition open_wvl_floc_nv (σ : nv var loc lang) :=
    forall i u x, In x (floc_nv (open_wvl_nv i u σ)) ->
      In x (floc_wvl u) \/ In x (floc_nv σ).

  Definition open_wvl_floc_vl (v : vl var loc lang) :=
    forall i u x, In x (floc_vl (open_wvl_vl i u v)) ->
      In x (floc_wvl u) \/ In x (floc_vl v).

  Definition open_wvl_floc_vnt (E : vnt var loc lang) :=
    forall i u x, In x (floc_vnt (open_wvl_vnt i u E)) ->
      In x (floc_wvl u) \/ In x (floc_vnt E).
  
  Lemma open_wvl_floc :
    (forall w, open_wvl_floc_wvl w) /\
    (forall σ, open_wvl_floc_nv σ) /\
    (forall v, open_wvl_floc_vl v) /\
    (forall E, open_wvl_floc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_wvl_floc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_floc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_floc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_floc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (des_ifs)
    | _ => progress (eqb2eq loc; clarify)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition close_floc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ x, In x (floc_wvl (close_wvl i ℓ w)) ->
      (x <> ℓ /\ In x (floc_wvl w)).

  Definition close_floc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ x, In x (floc_nv (close_nv i ℓ σ)) ->
      (x <> ℓ /\ In x (floc_nv σ)).

  Definition close_floc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ x, In x (floc_vl (close_vl i ℓ v)) ->
      (x <> ℓ /\ In x (floc_vl v)).

  Definition close_floc_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ x, In x (floc_vnt (close_vnt i ℓ E)) ->
      (x <> ℓ /\ In x (floc_vnt E)).

  Lemma close_floc `{Eq loc} :
    (forall w, close_floc_wvl w) /\
    (forall σ, close_floc_nv σ) /\
    (forall v, close_floc_vl v) /\
    (forall E, close_floc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : close_floc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : close_floc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : close_floc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : close_floc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (des_ifs)
    | _ => progress (eqb2eq loc; clarify)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition open_inc_floc_wvl (w : wvl var loc lang) :=
    forall i ℓ x, In x (floc_wvl w) -> In x (floc_wvl (open_loc_wvl i ℓ w)).

  Definition open_inc_floc_nv (σ : nv var loc lang) :=
    forall i ℓ x, In x (floc_nv σ) -> In x (floc_nv (open_loc_nv i ℓ σ)).

  Definition open_inc_floc_vl (v : vl var loc lang) :=
    forall i ℓ x, In x (floc_vl v) -> In x (floc_vl (open_loc_vl i ℓ v)).

  Definition open_inc_floc_vnt (E : vnt var loc lang) :=
    forall i ℓ x, In x (floc_vnt E) -> In x (floc_vnt (open_loc_vnt i ℓ E)).

  Lemma open_inc_floc :
    (forall w, open_inc_floc_wvl w) /\
    (forall σ, open_inc_floc_nv σ) /\
    (forall v, open_inc_floc_vl v) /\
    (forall E, open_inc_floc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_inc_floc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_inc_floc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_inc_floc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_inc_floc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (des_ifs)
    | _ => progress (eqb2eq loc; clarify)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition subst_intro_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_wvl w)),
      open_wvl_wvl i u w =
      subst_wvl_wvl u ℓ (open_loc_wvl i ℓ w)
  .

  Definition subst_intro_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_nv σ)),
      open_wvl_nv i u σ =
      subst_wvl_nv u ℓ (open_loc_nv i ℓ σ)
  .

  Definition subst_intro_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_vl v)),
      open_wvl_vl i u v =
      subst_wvl_vl u ℓ (open_loc_vl i ℓ v)
  .

  Definition subst_intro_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_vnt E)),
      open_wvl_vnt i u E =
      subst_wvl_vnt u ℓ (open_loc_vnt i ℓ E)
  .

  Lemma subst_intro `{Eq loc} :
    (forall w, subst_intro_wvl w) /\
    (forall σ, subst_intro_nv σ) /\
    (forall v, subst_intro_vl v) /\
    (forall E, subst_intro_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all:try (cbn; f_equal; solve [auto]).
    - des_goal.
      + eqb2eq nat. subst.
        rewrite eqb_refl. f_equal. auto.
      + f_equal. auto.
    - des_goal.
      + eqb2eq loc. contradict.
      + f_equal. auto.
    - split_nIn; f_equal; auto.
    - split_nIn; f_equal; auto.
  Qed.

  Definition open_loc_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ, close_wvl i ℓ (open_loc_wvl i ℓ w) = close_wvl i ℓ w.

  Definition open_loc_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ, close_nv i ℓ (open_loc_nv i ℓ σ) = close_nv i ℓ σ.

  Definition open_loc_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ, close_vl i ℓ (open_loc_vl i ℓ v) = close_vl i ℓ v.

  Definition open_loc_close_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ, close_vnt i ℓ (open_loc_vnt i ℓ E) = close_vnt i ℓ E.

  Lemma open_loc_close `{Eq loc} :
    (forall w, open_loc_close_wvl w) /\
    (forall σ, open_loc_close_nv σ) /\
    (forall v, open_loc_close_vl v) /\
    (forall E, open_loc_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_goal; repeat rw; eauto.
    all:rewrite eqb_refl in *; eqb2eq nat; clarify.
  Qed.

  Definition close_fresh_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_wvl w)),
      close_wvl i ℓ w = w.

  Definition close_fresh_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_nv σ)),
      close_nv i ℓ σ = σ.

  Definition close_fresh_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_vl v)),
      close_vl i ℓ v = v.

  Definition close_fresh_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_vnt E)),
      close_vnt i ℓ E = E.

  Lemma close_fresh `{Eq loc} :
    (forall w, close_fresh_wvl w) /\
    (forall σ, close_fresh_nv σ) /\
    (forall v, close_fresh_vl v) /\
    (forall E, close_fresh_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; split_nIn;
    try (progress des_ifs; eqb2eq loc; clarify).
    all: repeat match goal with
    | RR : close_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : close_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : close_fresh_vl _ |- _ => erewrite RR; eauto
    | RR : close_fresh_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition subst_loc_fresh_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_wvl w)),
      subst_loc_wvl ν ℓ w = w.

  Definition subst_loc_fresh_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_nv σ)),
      subst_loc_nv ν ℓ σ = σ.

  Definition subst_loc_fresh_vl `{Eq loc} (v : vl var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_vl v)),
      subst_loc_vl ν ℓ v = v.

  Definition subst_loc_fresh_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_vnt E)),
      subst_loc_vnt ν ℓ E = E.

  Lemma subst_loc_fresh `{Eq loc} :
    (forall w, subst_loc_fresh_wvl w) /\
    (forall σ, subst_loc_fresh_nv σ) /\
    (forall v, subst_loc_fresh_vl v) /\
    (forall E, subst_loc_fresh_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; split_nIn;
    try (progress des_ifs; eqb2eq loc; clarify).
    all: repeat match goal with
    | RR : subst_loc_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : subst_loc_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : subst_loc_fresh_vl _ |- _ => erewrite RR; eauto
    | RR : subst_loc_fresh_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition subst_wvl_fresh_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_wvl w)),
      subst_wvl_wvl ν ℓ w = w.

  Definition subst_wvl_fresh_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_nv σ)),
      subst_wvl_nv ν ℓ σ = σ.

  Definition subst_wvl_fresh_vl `{Eq loc} (v : vl var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_vl v)),
      subst_wvl_vl ν ℓ v = v.

  Definition subst_wvl_fresh_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall ν ℓ (FRESH : ~ In ℓ (floc_vnt E)),
      subst_wvl_vnt ν ℓ E = E.

  Lemma subst_wvl_fresh `{Eq loc} :
    (forall w, subst_wvl_fresh_wvl w) /\
    (forall σ, subst_wvl_fresh_nv σ) /\
    (forall v, subst_wvl_fresh_vl v) /\
    (forall E, subst_wvl_fresh_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; split_nIn;
    try (progress des_ifs; eqb2eq loc; clarify).
    all: repeat match goal with
    | RR : subst_wvl_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : subst_wvl_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : subst_wvl_fresh_vl _ |- _ => erewrite RR; eauto
    | RR : subst_wvl_fresh_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition close_open_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_wvl i u (close_wvl j ℓ w) = close_wvl j ℓ (open_wvl_wvl i u w).

  Definition close_open_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_nv i u (close_nv j ℓ σ) = close_nv j ℓ (open_wvl_nv i u σ).

  Definition close_open_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_vl i u (close_vl j ℓ v) = close_vl j ℓ (open_wvl_vl i u v).

  Definition close_open_wvl_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_vnt i u (close_vnt j ℓ E) = close_vnt j ℓ (open_wvl_vnt i u E).

  Lemma close_open_wvl `{Eq loc} :
    (forall w, close_open_wvl_wvl w) /\
    (forall σ, close_open_wvl_nv σ) /\
    (forall v, close_open_wvl_vl v) /\
    (forall E, close_open_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: try match goal with
    | _ : ~ In ?ℓ (floc_wvl ?u) |- context [close_wvl _ ?ℓ ?u] =>
      assert (close_fresh_wvl u) as RR by apply close_fresh;
      rewrite RR; eauto
    end.
    all: repeat match goal with
    | RR : close_open_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : close_open_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : close_open_wvl_vl _ |- _ => erewrite RR; eauto
    | RR : close_open_wvl_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition close_open_loc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_wvl i ν (close_wvl j ℓ w) = close_wvl j ℓ (open_loc_wvl i ν w).

  Definition close_open_loc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_nv i ν (close_nv j ℓ σ) = close_nv j ℓ (open_loc_nv i ν σ).

  Definition close_open_loc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_vl i ν (close_vl j ℓ v) = close_vl j ℓ (open_loc_vl i ν v).

  Definition close_open_loc_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_vnt i ν (close_vnt j ℓ E) = close_vnt j ℓ (open_loc_vnt i ν E).

  Lemma close_open_loc `{Eq loc} :
    (forall w, close_open_loc_wvl w) /\
    (forall σ, close_open_loc_nv σ) /\
    (forall v, close_open_loc_vl v) /\
    (forall E, close_open_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : close_open_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_nv _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_vl _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition open_wvl_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall i u, open_wvl_wvl i u w = w.

  Definition open_wvl_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall i u, open_wvl_nv i u σ = σ.

  Definition open_wvl_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall i u, open_wvl_vl i u v = v.

  Definition open_wvl_lc_vnt `{Eq loc} (E : vnt var loc lang) (EE : event E) :=
    forall i u, open_wvl_vnt i u E = E.
  
  Lemma open_wvl_lc `{Name loc} :
    (forall w W, open_wvl_lc_wvl w W) /\
    (forall σ Σ, open_wvl_lc_nv σ Σ) /\
    (forall v V, open_wvl_lc_vl v V) /\
    (forall E EE, open_wvl_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss; repeat rw; eauto.
    gensym_tac (L ++ (floc_wvl u) ++ (floc_vl v)) ℓ.
    replace v with (close_vl 0 ℓ (open_loc_vl 0 ℓ v)) at 1.
    assert (close_open_wvl_vl (open_loc_vl 0 ℓ v)) as RR by apply close_open_wvl.
    erewrite RR; eauto.
    match goal with RR : forall _, ~ In _ _ -> _ |- _ => rewrite RR; f_equal end.
    all: try match goal with
    | |- _ = _ =>
      assert (open_loc_close_vl v) by apply open_loc_close; rw;
      assert (close_fresh_vl v) by apply close_fresh; rw; auto
    end.
    auto.
  Qed.

  Definition open_loc_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall i ℓ, open_loc_wvl i ℓ w = w.

  Definition open_loc_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall i ℓ, open_loc_nv i ℓ σ = σ.

  Definition open_loc_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall i ℓ, open_loc_vl i ℓ v = v.

  Definition open_loc_lc_vnt `{Eq loc} (E : vnt var loc lang) (EE : event E) :=
    forall i ℓ, open_loc_vnt i ℓ E = E.

  Lemma open_loc_lc `{Name loc} :
    (forall w W, open_loc_lc_wvl w W) /\
    (forall σ Σ, open_loc_lc_nv σ Σ) /\
    (forall v V, open_loc_lc_vl v V) /\
    (forall E EE, open_loc_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss; repeat rw; eauto.
    gensym_tac (ℓ :: L ++ (floc_vl v)) ν.
    replace v with (close_vl 0 ν (open_loc_vl 0 ν v)) at 1.
    assert (close_open_loc_vl (open_loc_vl 0 ν v)) as RR by apply close_open_loc.
    erewrite RR; eauto.
    match goal with RR : forall _, ~ In _ _ -> _ |- _ => rewrite RR; f_equal end.
    all: try match goal with
    | |- _ = _ =>
      assert (open_loc_close_vl v) by apply open_loc_close; rw;
      assert (close_fresh_vl v) by apply close_fresh; rw; auto
    end.
    auto.
  Qed.

  Definition open_wvl_subst_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_wvl u ℓ (open_wvl_wvl i u' w) =
      open_wvl_wvl i (subst_wvl_wvl u ℓ u') (subst_wvl_wvl u ℓ w)
  .

  Definition open_wvl_subst_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_nv u ℓ (open_wvl_nv i u' σ) =
      open_wvl_nv i (subst_wvl_wvl u ℓ u') (subst_wvl_nv u ℓ σ)
  .

  Definition open_wvl_subst_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_vl u ℓ (open_wvl_vl i u' v) =
      open_wvl_vl i (subst_wvl_wvl u ℓ u') (subst_wvl_vl u ℓ v)
  .

  Definition open_wvl_subst_wvl_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_vnt u ℓ (open_wvl_vnt i u' E) =
      open_wvl_vnt i (subst_wvl_wvl u ℓ u') (subst_wvl_vnt u ℓ E)
  .
 
  Lemma open_wvl_subst_wvl `{Name loc} :
    (forall w, open_wvl_subst_wvl_wvl w) /\
    (forall σ, open_wvl_subst_wvl_nv σ) /\
    (forall v, open_wvl_subst_wvl_vl v) /\
    (forall E, open_wvl_subst_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_wvl_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_vl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_vnt _ |- _ => erewrite RR; eauto
    end.
    assert (open_wvl_lc_wvl u U) by eapply open_wvl_lc.
    rw. eauto.
  Qed.

  Definition open_wvl_subst_loc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ u ν,
      subst_loc_wvl ν ℓ (open_wvl_wvl i u w) =
      open_wvl_wvl i (subst_loc_wvl ν ℓ u) (subst_loc_wvl ν ℓ w)
  .

  Definition open_wvl_subst_loc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ u ν,
      subst_loc_nv ν ℓ (open_wvl_nv i u σ) =
      open_wvl_nv i (subst_loc_wvl ν ℓ u) (subst_loc_nv ν ℓ σ)
  .

  Definition open_wvl_subst_loc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ u ν,
      subst_loc_vl ν ℓ (open_wvl_vl i u v) =
      open_wvl_vl i (subst_loc_wvl ν ℓ u) (subst_loc_vl ν ℓ v)
  .

  Definition open_wvl_subst_loc_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ u ν,
      subst_loc_vnt ν ℓ (open_wvl_vnt i u E) =
      open_wvl_vnt i (subst_loc_wvl ν ℓ u) (subst_loc_vnt ν ℓ E)
  .

  Lemma open_wvl_subst_loc `{Name loc} :
    (forall w, open_wvl_subst_loc_wvl w) /\
    (forall σ, open_wvl_subst_loc_nv σ) /\
    (forall v, open_wvl_subst_loc_vl v) /\
    (forall E, open_wvl_subst_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_wvl_subst_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_loc_nv _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_loc_vl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_loc_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition open_loc_subst_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_wvl u ℓ (open_loc_wvl i ν w) =
      open_loc_wvl i ν (subst_wvl_wvl u ℓ w)
  .

  Definition open_loc_subst_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_nv u ℓ (open_loc_nv i ν σ) =
      open_loc_nv i ν (subst_wvl_nv u ℓ σ)
  .

  Definition open_loc_subst_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_vl u ℓ (open_loc_vl i ν v) =
      open_loc_vl i ν (subst_wvl_vl u ℓ v)
  .
  
  Definition open_loc_subst_wvl_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_vnt u ℓ (open_loc_vnt i ν E) =
      open_loc_vnt i ν (subst_wvl_vnt u ℓ E)
  .

  Lemma open_loc_subst_wvl `{Name loc} :
    (forall w, open_loc_subst_wvl_wvl w) /\
    (forall σ, open_loc_subst_wvl_nv σ) /\
    (forall v, open_loc_subst_wvl_vl v) /\
    (forall E, open_loc_subst_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_loc_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_vl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_vnt _ |- _ => erewrite RR; eauto
    end.
    assert (open_loc_lc_wvl u U) by apply open_loc_lc.
    rw. eauto.
  Qed.

  Definition open_loc_subst_loc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_wvl ν ℓ (open_loc_wvl i ℓ' w) =
      open_loc_wvl i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_wvl ν ℓ w)
  .

  Definition open_loc_subst_loc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_nv ν ℓ (open_loc_nv i ℓ' σ) =
      open_loc_nv i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_nv ν ℓ σ)
  .

  Definition open_loc_subst_loc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_vl ν ℓ (open_loc_vl i ℓ' v) =
      open_loc_vl i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_vl ν ℓ v)
  .

  Definition open_loc_subst_loc_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_vnt ν ℓ (open_loc_vnt i ℓ' E) =
      open_loc_vnt i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_vnt ν ℓ E)
  .

  Lemma open_loc_subst_loc `{Eq loc} :
    (forall w, open_loc_subst_loc_wvl w) /\
    (forall σ, open_loc_subst_loc_nv σ) /\
    (forall v, open_loc_subst_loc_vl v) /\
    (forall E, open_loc_subst_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_loc_subst_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_vl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_vnt _ |- _ => erewrite RR; eauto
    end.
    all: repeat first [
      rewrite eqb_refl; auto |
      des_goal; eqb2eq loc; clarify].
  Qed.

  Definition subst_wvl_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_wvl i ℓ (subst_wvl_wvl u ν w) =
    subst_wvl_wvl u ν (close_wvl i ℓ w).

  Definition subst_wvl_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_nv i ℓ (subst_wvl_nv u ν σ) =
    subst_wvl_nv u ν (close_nv i ℓ σ).

  Definition subst_wvl_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_vl i ℓ (subst_wvl_vl u ν v) =
    subst_wvl_vl u ν (close_vl i ℓ v).

  Definition subst_wvl_close_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_vnt i ℓ (subst_wvl_vnt u ν E) =
    subst_wvl_vnt u ν (close_vnt i ℓ E).

  Ltac subst_wvl_close_tac :=
    repeat match goal with
    | H : subst_wvl_close_wvl _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_nv _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_vl _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_vnt _ |- _ => rewrite H; eauto
    end.

  Lemma subst_wvl_close `{Eq loc} :
    (forall w, subst_wvl_close_wvl w) /\
    (forall σ, subst_wvl_close_nv σ) /\
    (forall v, subst_wvl_close_vl v) /\
    (forall E, subst_wvl_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; subst_wvl_close_tac.
    repeat des_goal; repeat eqb2eq loc; clarify;
    subst_wvl_close_tac.
    assert (close_fresh_wvl u) by apply close_fresh.
    rw; eauto.
  Qed.

  Definition subst_loc_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_wvl i ℓ (subst_loc_wvl u ν w) =
    subst_loc_wvl u ν (close_wvl i ℓ w).

  Definition subst_loc_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_nv i ℓ (subst_loc_nv u ν σ) =
    subst_loc_nv u ν (close_nv i ℓ σ).

  Definition subst_loc_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_vl i ℓ (subst_loc_vl u ν v) =
    subst_loc_vl u ν (close_vl i ℓ v).

  Definition subst_loc_close_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_vnt i ℓ (subst_loc_vnt u ν E) =
    subst_loc_vnt u ν (close_vnt i ℓ E).

  Ltac subst_loc_close_tac :=
    repeat match goal with
    | H : subst_loc_close_wvl _ |- _ => rewrite H; eauto
    | H : subst_loc_close_nv _ |- _ => rewrite H; eauto
    | H : subst_loc_close_vl _ |- _ => rewrite H; eauto
    | H : subst_loc_close_vnt _ |- _ => rewrite H; eauto
    end.

  Lemma subst_loc_close `{Eq loc} :
    (forall w, subst_loc_close_wvl w) /\
    (forall σ, subst_loc_close_nv σ) /\
    (forall v, subst_loc_close_vl v) /\
    (forall E, subst_loc_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; subst_loc_close_tac.
    repeat des_goal; repeat eqb2eq loc; clarify;
    subst_loc_close_tac.
  Qed.

  Definition floc_subst_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_wvl (subst_wvl_wvl u ℓ w))),
    (x <> ℓ /\ In x (floc_wvl w)) \/ In x (floc_wvl u).

  Definition floc_subst_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_nv (subst_wvl_nv u ℓ σ))),
    (x <> ℓ /\ In x (floc_nv σ)) \/ In x (floc_wvl u).

  Definition floc_subst_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_vl (subst_wvl_vl u ℓ v))),
    (x <> ℓ /\ In x (floc_vl v)) \/ In x (floc_wvl u).

  Definition floc_subst_wvl_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_vnt (subst_wvl_vnt u ℓ E))),
    (x <> ℓ /\ In x (floc_vnt E)) \/ In x (floc_wvl u).

  Lemma floc_subst_wvl `{Eq loc} :
    (forall w, floc_subst_wvl_wvl w) /\
    (forall σ, floc_subst_wvl_nv σ) /\
    (forall v, floc_subst_wvl_vl v) /\
    (forall E, floc_subst_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss;
    try solve [exploit H0; eauto].
    all: repeat des_hyp; repeat rewrite in_app_iff in *; des;
    repeat eqb2eq loc; subst; try solve [auto];
    match goal with
    | H : floc_subst_wvl_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    end.
  Qed.

  Definition close_open_loc_eq_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν,
      open_loc_wvl i ν (close_wvl i ℓ w) =
      subst_loc_wvl ν ℓ (open_loc_wvl i ℓ w).

  Definition close_open_loc_eq_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν,
      open_loc_nv i ν (close_nv i ℓ σ) =
      subst_loc_nv ν ℓ (open_loc_nv i ℓ σ).

  Definition close_open_loc_eq_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν,
      open_loc_vl i ν (close_vl i ℓ v) =
      subst_loc_vl ν ℓ (open_loc_vl i ℓ v).

  Definition close_open_loc_eq_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ ν,
      open_loc_vnt i ν (close_vnt i ℓ E) =
      subst_loc_vnt ν ℓ (open_loc_vnt i ℓ E).

  Lemma close_open_loc_eq `{Eq loc} :
    (forall w, close_open_loc_eq_wvl w) /\
    (forall σ, close_open_loc_eq_nv σ) /\
    (forall v, close_open_loc_eq_vl v) /\
    (forall E, close_open_loc_eq_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; try solve [repeat rw; eauto];
    des_ifs; first [eqb2eq nat | eqb2eq loc]; clarify.
    - rw. s. rewrite eqb_refl. eauto.
    - rw. s. eauto.
    - s. rewrite Nat.eqb_refl. rw. eauto.
    - s. rw. eauto.
  Qed.

  Definition subst_loc_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall ℓ ν, wvalue (subst_loc_wvl ν ℓ w).

  Definition subst_loc_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall ℓ ν, env (subst_loc_nv ν ℓ σ).

  Definition subst_loc_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall ℓ ν, value (subst_loc_vl ν ℓ v).

  Definition subst_loc_lc_vnt `{Eq loc} (E : vnt var loc lang) (EE : event E) :=
    forall ℓ ν, event (subst_loc_vnt ν ℓ E).

  Lemma subst_loc_lc `{Eq loc} :
    (forall w W, subst_loc_lc_wvl w W) /\
    (forall σ Σ, subst_loc_lc_nv σ Σ) /\
    (forall v V, subst_loc_lc_vl v V) /\
    (forall E EE, subst_loc_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss;
    try (des_ifs; eqb2eq loc);
    try solve [econstructor; eauto].
    econstructor.
    instantiate (1 := ℓ :: L). ii. split_nIn.
    exploit VAL; eauto. ii.
    match goal with H : forall _, ~ In _ _ -> _ |- _ => exploit H; eauto end.
    instantiate (1 := ℓ). instantiate (1 := ν).
    assert (open_loc_subst_loc_vl v) by apply open_loc_subst_loc.
    rw. des_ifs; eqb2eq loc; clarify.
  Qed.

  Definition subst_wvl_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall ℓ u (U : wvalue u), wvalue (subst_wvl_wvl u ℓ w).

  Definition subst_wvl_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall ℓ u (U : wvalue u), env (subst_wvl_nv u ℓ σ).

  Definition subst_wvl_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall ℓ u (U : wvalue u), value (subst_wvl_vl u ℓ v).

  Definition subst_wvl_lc_vnt `{Eq loc} (E : vnt var loc lang) (EE : event E) :=
    forall ℓ u (U : wvalue u), event (subst_wvl_vnt u ℓ E).

  Lemma subst_wvl_lc `{Name loc} :
    (forall w W, subst_wvl_lc_wvl w W) /\
    (forall σ Σ, subst_wvl_lc_nv σ Σ) /\
    (forall v V, subst_wvl_lc_vl v V) /\
    (forall E EE, subst_wvl_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss;
    try (des_ifs; eqb2eq loc);
    try solve [econstructor; eauto].
    econstructor.
    instantiate (1 := ℓ :: L). ii. split_nIn.
    exploit VAL; eauto. ii.
    match goal with H : forall _, ~ In _ _ -> _ |- _ => exploit H; eauto end.
    instantiate (1 := ℓ).
    assert (open_loc_subst_wvl_vl v) by eapply open_loc_subst_wvl.
    rw; eauto.
  Qed.

  Definition map_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ φ (INJ : oto φ),
      map_wvl φ (close_wvl i ℓ w) = close_wvl i (φ ℓ) (map_wvl φ w).

  Definition map_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ φ (INJ : oto φ),
      map_nv φ (close_nv i ℓ σ) = close_nv i (φ ℓ) (map_nv φ σ).

  Definition map_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ φ (INJ : oto φ),
      map_vl φ (close_vl i ℓ v) = close_vl i (φ ℓ) (map_vl φ v).

  Definition map_close_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ φ (INJ : oto φ),
      map_vnt φ (close_vnt i ℓ E) = close_vnt i (φ ℓ) (map_vnt φ E).

  Lemma map_close `{Eq loc} :
    (forall w, map_close_wvl w) /\
    (forall σ, map_close_nv σ) /\
    (forall v, map_close_vl v) /\
    (forall E, map_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; unfold oto in INJ; repeat rw; eauto.
    des_ifs.
    all: repeat (eqb2eq loc; clarify; ss).
    all: repeat rw; eauto.
    apply INJ in Heq0; clarify.
  Qed.

  Definition map_open_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i u φ,
      map_wvl φ (open_wvl_wvl i u w) = open_wvl_wvl i (map_wvl φ u) (map_wvl φ w).

  Definition map_open_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i u φ,
      map_nv φ (open_wvl_nv i u σ) = open_wvl_nv i (map_wvl φ u) (map_nv φ σ).

  Definition map_open_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i u φ,
      map_vl φ (open_wvl_vl i u v) = open_wvl_vl i (map_wvl φ u) (map_vl φ v).

  Definition map_open_wvl_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i u φ,
      map_vnt φ (open_wvl_vnt i u E) = open_wvl_vnt i (map_wvl φ u) (map_vnt φ E).

  Lemma map_open_wvl `{Eq loc} :
    (forall w, map_open_wvl_wvl w) /\
    (forall σ, map_open_wvl_nv σ) /\
    (forall v, map_open_wvl_vl v) /\
    (forall E, map_open_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; eauto.
    des_ifs.
    all: repeat (eqb2eq nat; clarify; ss).
    all: repeat rw; eauto.
  Qed.

  Definition map_open_loc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i u φ,
      map_wvl φ (open_loc_wvl i u w) = open_loc_wvl i (φ u) (map_wvl φ w).

  Definition map_open_loc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i u φ,
      map_nv φ (open_loc_nv i u σ) = open_loc_nv i (φ u) (map_nv φ σ).

  Definition map_open_loc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i u φ,
      map_vl φ (open_loc_vl i u v) = open_loc_vl i (φ u) (map_vl φ v).

  Definition map_open_loc_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i u φ,
      map_vnt φ (open_loc_vnt i u E) = open_loc_vnt i (φ u) (map_vnt φ E).

  Lemma map_open_loc `{Eq loc} :
    (forall w, map_open_loc_wvl w) /\
    (forall σ, map_open_loc_nv σ) /\
    (forall v, map_open_loc_vl v) /\
    (forall E, map_open_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; eauto.
    des_ifs.
    all: repeat (eqb2eq nat; clarify; ss).
    all: repeat rw; eauto.
  Qed.

  Definition floc_map_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_wvl w)),
      In (φ ℓ) (floc_wvl (map_wvl φ w)).

  Definition floc_map_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_nv σ)),
      In (φ ℓ) (floc_nv (map_nv φ σ)).

  Definition floc_map_vl `{Eq loc} (v : vl var loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_vl v)),
      In (φ ℓ) (floc_vl (map_vl φ v)).

  Definition floc_map_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_vnt E)),
      In (φ ℓ) (floc_vnt (map_vnt φ E)).

  Lemma floc_map `{Eq loc} :
    (forall w, floc_map_wvl w) /\
    (forall σ, floc_map_nv σ) /\
    (forall v, floc_map_vl v) /\
    (forall E, floc_map_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; des; clarify; auto.
    all: rewrite in_app_iff in *; des; auto.
  Qed.

  Definition map_floc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_wvl (map_wvl φ w))),
    In ℓ (floc_wvl w).

  Definition map_floc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_nv (map_nv φ σ))),
    In ℓ (floc_nv σ).

  Definition map_floc_vl `{Eq loc} (v : vl var loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_vl (map_vl φ v))),
    In ℓ (floc_vl v).

  Definition map_floc_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_vnt (map_vnt φ E))),
    In ℓ (floc_vnt E).
 
  Lemma map_floc `{Eq loc} :
    (forall w, map_floc_wvl w) /\
    (forall σ, map_floc_nv σ) /\
    (forall v, map_floc_vl v) /\
    (forall E, map_floc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; eauto;
    des; eauto.
    all: rewrite in_app_iff in *; ss; des; eauto.
  Qed.

  Definition map_id_is_id_wvl (w : wvl var loc lang) :=
    map_wvl id w = w.

  Definition map_id_is_id_nv (σ : nv var loc lang) :=
    map_nv id σ = σ.

  Definition map_id_is_id_vl (v : vl var loc lang) :=
    map_vl id v = v.

  Definition map_id_is_id_vnt (E : vnt var loc lang) :=
    map_vnt id E = E.
  
  Lemma map_id_is_id :
    (forall w, map_id_is_id_wvl w) /\
    (forall σ, map_id_is_id_nv σ) /\
    (forall v, map_id_is_id_vl v) /\
    (forall E, map_id_is_id_vnt E).
  Proof.
    apply pre_val_ind; ii; red; s; repeat rw; eauto.
  Qed.

  Definition swap_is_subst_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall φ (INJ : oto φ)
      ℓ ν (FRESH : ~ In ℓ (floc_wvl w)),
      map_wvl (swap φ ℓ ν) w = subst_loc_wvl (φ ℓ) (φ ν) (map_wvl φ w).

  Definition swap_is_subst_nv `{Eq loc} (σ : nv var loc lang) :=
    forall φ (INJ : oto φ)
      ℓ ν (FRESH : ~ In ℓ (floc_nv σ)),
      map_nv (swap φ ℓ ν) σ = subst_loc_nv (φ ℓ) (φ ν) (map_nv φ σ).

  Definition swap_is_subst_vl `{Eq loc} (v : vl var loc lang) :=
    forall φ (INJ : oto φ)
      ℓ ν (FRESH : ~ In ℓ (floc_vl v)),
      map_vl (swap φ ℓ ν) v = subst_loc_vl (φ ℓ) (φ ν) (map_vl φ v).

  Definition swap_is_subst_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall φ (INJ : oto φ)
      ℓ ν (FRESH : ~ In ℓ (floc_vnt E)),
      map_vnt (swap φ ℓ ν) E = subst_loc_vnt (φ ℓ) (φ ν) (map_vnt φ E).

  Lemma swap_is_subst `{Eq loc} :
    (forall w, swap_is_subst_wvl w) /\
    (forall σ, swap_is_subst_nv σ) /\
    (forall v, swap_is_subst_vl v) /\
    (forall E, swap_is_subst_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; unfold oto in INJ; repeat rw; split_nIn; eauto.
    unfold swap; des_ifs; repeat eqb2eq loc; clarify.
    exploit INJ; eauto; ii; clarify.
  Qed.

  Definition subst_loc_close_eq_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (floc_wvl w)),
      close_wvl i ℓ (subst_loc_wvl ℓ ν w) = close_wvl i ν w.

  Definition subst_loc_close_eq_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (floc_nv σ)),
      close_nv i ℓ (subst_loc_nv ℓ ν σ) = close_nv i ν σ.

  Definition subst_loc_close_eq_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (floc_vl v)),
      close_vl i ℓ (subst_loc_vl ℓ ν v) = close_vl i ν v.

  Definition subst_loc_close_eq_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (floc_vnt E)),
      close_vnt i ℓ (subst_loc_vnt ℓ ν E) = close_vnt i ν E.

  Lemma subst_loc_close_eq `{Eq loc} :
    (forall w, subst_loc_close_eq_wvl w) /\
    (forall σ, subst_loc_close_eq_nv σ) /\
    (forall v, subst_loc_close_eq_vl v) /\
    (forall E, subst_loc_close_eq_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; split_nIn; eauto.
    do 2 (des_ifs; eqb2eq loc; clarify; s);
    rw; eauto.
  Qed.

  Definition map_ext_wvl (w : wvl var loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_wvl w)), φ ℓ = ϕ ℓ),
      map_wvl φ w = map_wvl ϕ w.

  Definition map_ext_nv (σ : nv var loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_nv σ)), φ ℓ = ϕ ℓ),
      map_nv φ σ = map_nv ϕ σ.

  Definition map_ext_vl (v : vl var loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_vl v)), φ ℓ = ϕ ℓ),
      map_vl φ v = map_vl ϕ v.

  Definition map_ext_vnt (E : vnt var loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_vnt E)), φ ℓ = ϕ ℓ),
      map_vnt φ E = map_vnt ϕ E.
  
  Lemma map_ext :
    (forall w, map_ext_wvl w) /\
    (forall σ, map_ext_nv σ) /\
    (forall v, map_ext_vl v) /\
    (forall E, map_ext_vnt E).
  Proof.
    apply pre_val_ind; ii; ss;
    repeat match goal with
    | RR : map_ext_wvl _ |- _ => erewrite (RR φ ϕ); eauto
    | RR : map_ext_nv _ |- _ => erewrite (RR φ ϕ); eauto
    | RR : map_ext_vl _ |- _ => erewrite (RR φ ϕ); eauto
    | RR : map_ext_vnt _ |- _ => erewrite (RR φ ϕ); eauto
    end.
    erewrite EXT; eauto.
    all:ii; apply EXT; rewrite in_app_iff; eauto.
  Qed.

  Definition compose (f g : loc -> loc) ℓ := f (g ℓ).

  Definition map_compose_wvl (w : wvl var loc lang) :=
    forall φ ϕ,
      map_wvl φ (map_wvl ϕ w) = map_wvl (compose φ ϕ) w.

  Definition map_compose_nv (σ : nv var loc lang) :=
    forall φ ϕ,
      map_nv φ (map_nv ϕ σ) = map_nv (compose φ ϕ) σ.

  Definition map_compose_vl (v : vl var loc lang) :=
    forall φ ϕ,
      map_vl φ (map_vl ϕ v) = map_vl (compose φ ϕ) v.

  Definition map_compose_vnt (E : vnt var loc lang) :=
    forall φ ϕ,
      map_vnt φ (map_vnt ϕ E) = map_vnt (compose φ ϕ) E.

  Lemma map_compose :
    (forall w, map_compose_wvl w) /\
    (forall σ, map_compose_nv σ) /\
    (forall v, map_compose_vl v) /\
    (forall E, map_compose_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; auto.
  Qed.

  Definition map_lc_wvl (w : wvl var loc lang) (W : wvalue w) :=
    forall φ, wvalue (map_wvl φ w).

  Definition map_lc_nv (σ : nv var loc lang) (Σ : env σ) :=
    forall φ, env (map_nv φ σ).

  Definition map_lc_vl (v : vl var loc lang) (V : value v) :=
    forall φ, value (map_vl φ v).

  Definition map_lc_vnt (E : vnt var loc lang) (EE : event E) :=
    forall φ, event (map_vnt φ E).

  Lemma map_lc `{Name loc} :
    (forall w W, map_lc_wvl w W) /\
    (forall σ Σ, map_lc_nv σ Σ) /\
    (forall v V, map_lc_vl v V) /\
    (forall E EE, map_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss; econstructor; eauto.
    instantiate (1 := []).
    ii. gensym_tac (L ++ floc_vl v) ν.
    exploit H1; eauto.
    instantiate (1 := fun x => if eqb x ν then ℓ else φ x).
    assert (map_open_loc_vl v) by apply map_open_loc.
    rw. rewrite eqb_refl.
    assert (map_ext_vl v) as RR by apply map_ext.
    erewrite RR; eauto.
    ii. des_ifs; eqb2eq loc; clarify.
  Qed.

  Definition subst_id_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ℓ, subst_loc_wvl ℓ ℓ w = w.

  Definition subst_id_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ℓ, subst_loc_nv ℓ ℓ σ = σ.

  Definition subst_id_vl `{Eq loc} (v : vl var loc lang) :=
    forall ℓ, subst_loc_vl ℓ ℓ v = v.

  Definition subst_id_vnt `{Eq loc} (E : vnt var loc lang) :=
    forall ℓ, subst_loc_vnt ℓ ℓ E = E.
  
  Lemma subst_id `{Eq loc} :
    (forall w, subst_id_wvl w) /\
    (forall σ, subst_id_nv σ) /\
    (forall v, subst_id_vl v) /\
    (forall E, subst_id_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; eauto;
    des_ifs; eqb2eq loc; clarify.
  Qed.
End SubstFacts.

(*
TODO : make tactics to automate rewriting the following
  open_floc
  open_inc_floc
  subst_intro
  open_loc_close
  close_fresh
  close_open_wvl
  close_open_loc
  open_wvl_lc
  open_loc_lc
  open_wvl_subst_wvl
  open_loc_subst_loc
  subst_wvl_close
  floc_subst_wvl
*)
