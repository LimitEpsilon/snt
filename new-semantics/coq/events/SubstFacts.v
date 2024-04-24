From Basics Require Import Basics.
From Coq.Program Require Export Basics.
From With_events Require Import Defs.

Section SubstFacts.
  Context {var lbl loc lang : Type}.

  Definition open_floc_wvl (w : wvl var lbl loc lang) :=
    forall i ℓ x, In x (floc_wvl (open_loc_wvl i ℓ w)) -> x = fst ℓ \/ In x (floc_wvl w).

  Definition open_floc_nv (σ : nv var lbl loc lang) :=
    forall i ℓ x, In x (floc_nv (open_loc_nv i ℓ σ)) -> x = fst ℓ \/ In x (floc_nv σ).

  Definition open_floc_vl (v : vl var lbl loc lang) :=
    forall i ℓ x, In x (floc_vl (open_loc_vl i ℓ v)) -> x = fst ℓ \/ In x (floc_vl v).

  Definition open_floc_vnt (E : vnt var lbl loc lang) :=
    forall i ℓ x, In x (floc_vnt (open_loc_vnt i ℓ E)) -> x = fst ℓ \/ In x (floc_vnt E).

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

  Definition close_flloc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ x, In x (flloc_wvl (close_wvl i ℓ w)) ->
      (x <> ℓ /\ In x (flloc_wvl w)).

  Definition close_flloc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ x, In x (flloc_nv (close_nv i ℓ σ)) ->
      (x <> ℓ /\ In x (flloc_nv σ)).

  Definition close_flloc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ x, In x (flloc_vl (close_vl i ℓ v)) ->
      (x <> ℓ /\ In x (flloc_vl v)).

  Definition close_flloc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ x, In x (flloc_vnt (close_vnt i ℓ E)) ->
      (x <> ℓ /\ In x (flloc_vnt E)).

  Lemma close_flloc `{Eq lbl} `{Eq loc} :
    (forall w, close_flloc_wvl w) /\
    (forall σ, close_flloc_nv σ) /\
    (forall v, close_flloc_vl v) /\
    (forall E, close_flloc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : close_flloc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : close_flloc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : close_flloc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : close_flloc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (repeat des_hyp)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (eqb2eq lbl; clarify)
    | _ => progress (eqb2eq loc; clarify)
    | _ => progress (ss)
    end.
    all: split; auto; ii; des_ifs.
  Qed.

  Definition trans_floc_wvl (w : wvl var lbl loc lang) :=
    floc_wvl w = List.map fst (flloc_wvl w).

  Definition trans_floc_nv (σ : nv var lbl loc lang) :=
    floc_nv σ = List.map fst (flloc_nv σ).

  Definition trans_floc_vl (v : vl var lbl loc lang) :=
    floc_vl v = List.map fst (flloc_vl v).

  Definition trans_floc_vnt (E : vnt var lbl loc lang) :=
    floc_vnt E = List.map fst (flloc_vnt E).

  Lemma trans_floc :
    (forall w, trans_floc_wvl w) /\
    (forall σ, trans_floc_nv σ) /\
    (forall v, trans_floc_vl v) /\
    (forall E, trans_floc_vnt E).
  Proof.
    apply pre_val_ind; red; ii; repeat rw; ss;
    try des_goal; ss; repeat rw; auto;
    rewrite map_app; auto.
  Qed.

  Definition open_loc_flloc_wvl (w : wvl var lbl loc lang) :=
    forall i u x, In x (flloc_wvl (open_loc_wvl i u w)) ->
      x = u \/ In x (flloc_wvl w).

  Definition open_loc_flloc_nv (σ : nv var lbl loc lang) :=
    forall i u x, In x (flloc_nv (open_loc_nv i u σ)) ->
      x = u \/ In x (flloc_nv σ).

  Definition open_loc_flloc_vl (v : vl var lbl loc lang) :=
    forall i u x, In x (flloc_vl (open_loc_vl i u v)) ->
      x = u \/ In x (flloc_vl v).

  Definition open_loc_flloc_vnt (E : vnt var lbl loc lang) :=
    forall i u x, In x (flloc_vnt (open_loc_vnt i u E)) ->
      x = u \/ In x (flloc_vnt E).
 
  Lemma open_loc_flloc :
    (forall w, open_loc_flloc_wvl w) /\
    (forall σ, open_loc_flloc_nv σ) /\
    (forall v, open_loc_flloc_vl v) /\
    (forall E, open_loc_flloc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_loc_flloc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_loc_flloc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_loc_flloc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_loc_flloc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (des_ifs)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition open_wvl_flloc_wvl (w : wvl var lbl loc lang) :=
    forall i u x, In x (flloc_wvl (open_wvl_wvl i u w)) ->
      In x (flloc_wvl u) \/ In x (flloc_wvl w).

  Definition open_wvl_flloc_nv (σ : nv var lbl loc lang) :=
    forall i u x, In x (flloc_nv (open_wvl_nv i u σ)) ->
      In x (flloc_wvl u) \/ In x (flloc_nv σ).

  Definition open_wvl_flloc_vl (v : vl var lbl loc lang) :=
    forall i u x, In x (flloc_vl (open_wvl_vl i u v)) ->
      In x (flloc_wvl u) \/ In x (flloc_vl v).

  Definition open_wvl_flloc_vnt (E : vnt var lbl loc lang) :=
    forall i u x, In x (flloc_vnt (open_wvl_vnt i u E)) ->
      In x (flloc_wvl u) \/ In x (flloc_vnt E).
 
  Lemma open_wvl_flloc :
    (forall w, open_wvl_flloc_wvl w) /\
    (forall σ, open_wvl_flloc_nv σ) /\
    (forall v, open_wvl_flloc_vl v) /\
    (forall E, open_wvl_flloc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_wvl_flloc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_flloc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_flloc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_flloc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (rewrite in_app_iff in *)
    | _ => progress (des; clarify)
    | _ => progress (des_ifs)
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition open_wvl_inc_flloc_wvl (w : wvl var lbl loc lang) :=
    forall i u x, In x (flloc_wvl w) ->
      In x (flloc_wvl (open_wvl_wvl i u w)).

  Definition open_wvl_inc_flloc_nv (σ : nv var lbl loc lang) :=
    forall i u x, In x (flloc_nv σ) ->
      In x (flloc_nv (open_wvl_nv i u σ)).

  Definition open_wvl_inc_flloc_vl (v : vl var lbl loc lang) :=
    forall i u x, In x (flloc_vl v) ->
      In x (flloc_vl (open_wvl_vl i u v)).

  Definition open_wvl_inc_flloc_vnt (E : vnt var lbl loc lang) :=
    forall i u x, In x (flloc_vnt E) ->
      In x (flloc_vnt (open_wvl_vnt i u E)).
  
  Lemma open_wvl_inc_flloc :
    (forall w, open_wvl_inc_flloc_wvl w) /\
    (forall σ, open_wvl_inc_flloc_nv σ) /\
    (forall v, open_wvl_inc_flloc_vl v) /\
    (forall E, open_wvl_inc_flloc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq nat; clarify|
      des_goal; clarify|
      rewrite in_app_iff in *; auto].
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_wvl_inc_flloc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_inc_flloc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_inc_flloc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_wvl_inc_flloc_vnt _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | _ => progress (des; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition open_inc_floc_wvl (w : wvl var lbl loc lang) :=
    forall i ℓ x, In x (floc_wvl w) -> In x (floc_wvl (open_loc_wvl i ℓ w)).

  Definition open_inc_floc_nv (σ : nv var lbl loc lang) :=
    forall i ℓ x, In x (floc_nv σ) -> In x (floc_nv (open_loc_nv i ℓ σ)).

  Definition open_inc_floc_vl (v : vl var lbl loc lang) :=
    forall i ℓ x, In x (floc_vl v) -> In x (floc_vl (open_loc_vl i ℓ v)).

  Definition open_inc_floc_vnt (E : vnt var lbl loc lang) :=
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
    | _ => progress (eqb2eq nat; clarify)
    | _ => progress (ss)
    end.
  Qed.

  Definition subst_intro_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ p u (FRESH : ~ In ℓ (floc_wvl w)),
      open_wvl_wvl i u w =
      subst_wvl_wvl u (ℓ, p) (open_loc_wvl i (ℓ, p) w)
  .

  Definition subst_intro_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ p u (FRESH : ~ In ℓ (floc_nv σ)),
      open_wvl_nv i u σ =
      subst_wvl_nv u (ℓ, p) (open_loc_nv i (ℓ, p) σ)
  .

  Definition subst_intro_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ p u (FRESH : ~ In ℓ (floc_vl v)),
      open_wvl_vl i u v =
      subst_wvl_vl u (ℓ, p) (open_loc_vl i (ℓ, p) v)
  .

  Definition subst_intro_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ p u (FRESH : ~ In ℓ (floc_vnt E)),
      open_wvl_vnt i u E =
      subst_wvl_vnt u (ℓ, p) (open_loc_vnt i (ℓ, p) E)
  .

  Lemma subst_intro `{Eq lbl} `{Eq loc} :
    (forall w, subst_intro_wvl w) /\
    (forall σ, subst_intro_nv σ) /\
    (forall v, subst_intro_vl v) /\
    (forall E, subst_intro_vnt E).
  Proof.
    apply pre_val_ind; ii; ss.
    all:try (cbn; f_equal; solve [auto]).
    - des_goal.
      + eqb2eq nat. subst.
        repeat rewrite eqb_refl. s. f_equal. auto.
      + f_equal. auto.
    - des_hyp; split_nIn; des_goal.
      + eqb2eq loc. contradict.
      + f_equal. auto.
    - split_nIn; f_equal; auto.
    - split_nIn; f_equal; auto.
  Qed.

  Definition open_loc_close_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ, close_wvl i ℓ (open_loc_wvl i ℓ w) = close_wvl i ℓ w.

  Definition open_loc_close_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ, close_nv i ℓ (open_loc_nv i ℓ σ) = close_nv i ℓ σ.

  Definition open_loc_close_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ, close_vl i ℓ (open_loc_vl i ℓ v) = close_vl i ℓ v.

  Definition open_loc_close_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ, close_vnt i ℓ (open_loc_vnt i ℓ E) = close_vnt i ℓ E.

  Lemma open_loc_close `{Eq lbl} `{Eq loc} :
    (forall w, open_loc_close_wvl w) /\
    (forall σ, open_loc_close_nv σ) /\
    (forall v, open_loc_close_vl v) /\
    (forall E, open_loc_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_goal; repeat rw; eauto.
    all:repeat des_hyp; rewrite eqb_refl in *; eqb2eq nat; clarify.
  Qed.

  Definition close_fresh_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ p (FRESH : ~ In ℓ (floc_wvl w)),
      close_wvl i (ℓ, p) w = w.

  Definition close_fresh_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ p (FRESH : ~ In ℓ (floc_nv σ)),
      close_nv i (ℓ, p) σ = σ.

  Definition close_fresh_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ p (FRESH : ~ In ℓ (floc_vl v)),
      close_vl i (ℓ, p) v = v.

  Definition close_fresh_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ p (FRESH : ~ In ℓ (floc_vnt E)),
      close_vnt i (ℓ, p) E = E.

  Lemma close_fresh `{Eq lbl} `{Eq loc} :
    (forall w, close_fresh_wvl w) /\
    (forall σ, close_fresh_nv σ) /\
    (forall v, close_fresh_vl v) /\
    (forall E, close_fresh_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : close_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : close_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : close_fresh_vl _ |- _ => erewrite RR; eauto
    | RR : close_fresh_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition subst_loc_fresh_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_wvl w)),
      subst_loc_wvl ν (ℓ, p) w = w.

  Definition subst_loc_fresh_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_nv σ)),
      subst_loc_nv ν (ℓ, p) σ = σ.

  Definition subst_loc_fresh_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_vl v)),
      subst_loc_vl ν (ℓ, p) v = v.

  Definition subst_loc_fresh_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_vnt E)),
      subst_loc_vnt ν (ℓ, p) E = E.

  Lemma subst_loc_fresh `{Eq lbl} `{Eq loc} :
    (forall w, subst_loc_fresh_wvl w) /\
    (forall σ, subst_loc_fresh_nv σ) /\
    (forall v, subst_loc_fresh_vl v) /\
    (forall E, subst_loc_fresh_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : subst_loc_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : subst_loc_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : subst_loc_fresh_vl _ |- _ => erewrite RR; eauto
    | RR : subst_loc_fresh_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition subst_wvl_fresh_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_wvl w)),
      subst_wvl_wvl ν (ℓ, p) w = w.

  Definition subst_wvl_fresh_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_nv σ)),
      subst_wvl_nv ν (ℓ, p) σ = σ.

  Definition subst_wvl_fresh_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_vl v)),
      subst_wvl_vl ν (ℓ, p) v = v.

  Definition subst_wvl_fresh_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall ν ℓ p (FRESH : ~ In ℓ (floc_vnt E)),
      subst_wvl_vnt ν (ℓ, p) E = E.

  Lemma subst_wvl_fresh `{Eq lbl} `{Eq loc} :
    (forall w, subst_wvl_fresh_wvl w) /\
    (forall σ, subst_wvl_fresh_nv σ) /\
    (forall v, subst_wvl_fresh_vl v) /\
    (forall E, subst_wvl_fresh_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : subst_wvl_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : subst_wvl_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : subst_wvl_fresh_vl _ |- _ => erewrite RR; eauto
    | RR : subst_wvl_fresh_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition close_open_wvl_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i j ℓ p u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_wvl i u (close_wvl j (ℓ, p) w) = close_wvl j (ℓ, p) (open_wvl_wvl i u w).

  Definition close_open_wvl_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i j ℓ p u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_nv i u (close_nv j (ℓ, p) σ) = close_nv j (ℓ, p) (open_wvl_nv i u σ).

  Definition close_open_wvl_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i j ℓ p u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_vl i u (close_vl j (ℓ, p) v) = close_vl j (ℓ, p) (open_wvl_vl i u v).

  Definition close_open_wvl_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i j ℓ p u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_vnt i u (close_vnt j (ℓ, p) E) = close_vnt j (ℓ, p) (open_wvl_vnt i u E).

  Lemma close_open_wvl `{Eq lbl} `{Eq loc} :
    (forall w, close_open_wvl_wvl w) /\
    (forall σ, close_open_wvl_nv σ) /\
    (forall v, close_open_wvl_vl v) /\
    (forall E, close_open_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq nat; try eqb2eq loc; try eqb2eq lbl; clarify.
    all: try match goal with
    | _ : ~ In ?ℓ (floc_wvl ?u) |- context [close_wvl _ (?ℓ, _) ?u] =>
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

  Definition close_open_loc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_wvl i ν (close_wvl j ℓ w) = close_wvl j ℓ (open_loc_wvl i ν w).

  Definition close_open_loc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_nv i ν (close_nv j ℓ σ) = close_nv j ℓ (open_loc_nv i ν σ).

  Definition close_open_loc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_vl i ν (close_vl j ℓ v) = close_vl j ℓ (open_loc_vl i ν v).

  Definition close_open_loc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_vnt i ν (close_vnt j ℓ E) = close_vnt j ℓ (open_loc_vnt i ν E).

  Lemma close_open_loc `{Eq lbl} `{Eq loc} :
    (forall w, close_open_loc_wvl w) /\
    (forall σ, close_open_loc_nv σ) /\
    (forall v, close_open_loc_vl v) /\
    (forall E, close_open_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq nat; try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : close_open_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_nv _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_vl _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition open_wvl_lc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) (W : wvalue w) :=
    forall i u, open_wvl_wvl i u w = w.

  Definition open_wvl_lc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) (Σ : env σ) :=
    forall i u, open_wvl_nv i u σ = σ.

  Definition open_wvl_lc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) (V : value v) :=
    forall i u, open_wvl_vl i u v = v.

  Definition open_wvl_lc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) (EE : event E) :=
    forall i u, open_wvl_vnt i u E = E.
 
  Lemma open_wvl_lc `{Eq lbl} `{Name loc} :
    (forall w W, open_wvl_lc_wvl w W) /\
    (forall σ Σ, open_wvl_lc_nv σ Σ) /\
    (forall v V, open_wvl_lc_vl v V) /\
    (forall E EE, open_wvl_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss; repeat rw; eauto.
    gensym_tac (L ++ (floc_wvl u) ++ (floc_vl v)) ℓ.
    replace v with (close_vl 0 (ℓ, p) (open_loc_vl 0 (ℓ, p) v)) at 1.
    assert (close_open_wvl_vl (open_loc_vl 0 (ℓ, p) v)) as RR by apply close_open_wvl.
    erewrite RR; eauto.
    match goal with RR : forall _, ~ In _ _ -> _ |- _ => rewrite RR; f_equal end.
    all: try match goal with
    | |- _ = _ =>
      assert (open_loc_close_vl v) by apply open_loc_close; rw;
      assert (close_fresh_vl v) by apply close_fresh; rw; auto
    end.
    auto.
  Qed.

  Definition open_loc_lc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) (W : wvalue w) :=
    forall i ℓ, open_loc_wvl i ℓ w = w.

  Definition open_loc_lc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) (Σ : env σ) :=
    forall i ℓ, open_loc_nv i ℓ σ = σ.

  Definition open_loc_lc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) (V : value v) :=
    forall i ℓ, open_loc_vl i ℓ v = v.

  Definition open_loc_lc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) (EE : event E) :=
    forall i ℓ, open_loc_vnt i ℓ E = E.

  Lemma open_loc_lc `{Eq lbl} `{Name loc} :
    (forall w W, open_loc_lc_wvl w W) /\
    (forall σ Σ, open_loc_lc_nv σ Σ) /\
    (forall v V, open_loc_lc_vl v V) /\
    (forall E EE, open_loc_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss; repeat rw; eauto.
    destruct ℓ as [ℓ p'].
    gensym_tac (ℓ :: L ++ (floc_vl v)) ν.
    replace v with (close_vl 0 (ν, p) (open_loc_vl 0 (ν, p) v)) at 1.
    assert (close_open_loc_vl (open_loc_vl 0 (ν, p) v)) as RR by apply close_open_loc.
    erewrite RR; eauto.
    match goal with RR : forall _, ~ In _ _ -> _ |- _ => rewrite RR; f_equal end.
    all: try match goal with
    | |- _ = _ =>
      assert (open_loc_close_vl v) by apply open_loc_close; rw;
      assert (close_fresh_vl v) by apply close_fresh; rw; auto
    end.
    all: ii; clarify; auto.
  Qed.

  Definition open_wvl_subst_wvl_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_wvl u ℓ (open_wvl_wvl i u' w) =
      open_wvl_wvl i (subst_wvl_wvl u ℓ u') (subst_wvl_wvl u ℓ w)
  .

  Definition open_wvl_subst_wvl_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_nv u ℓ (open_wvl_nv i u' σ) =
      open_wvl_nv i (subst_wvl_wvl u ℓ u') (subst_wvl_nv u ℓ σ)
  .

  Definition open_wvl_subst_wvl_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_vl u ℓ (open_wvl_vl i u' v) =
      open_wvl_vl i (subst_wvl_wvl u ℓ u') (subst_wvl_vl u ℓ v)
  .

  Definition open_wvl_subst_wvl_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_vnt u ℓ (open_wvl_vnt i u' E) =
      open_wvl_vnt i (subst_wvl_wvl u ℓ u') (subst_wvl_vnt u ℓ E)
  .
 
  Lemma open_wvl_subst_wvl `{Eq lbl} `{Name loc} :
    (forall w, open_wvl_subst_wvl_wvl w) /\
    (forall σ, open_wvl_subst_wvl_nv σ) /\
    (forall v, open_wvl_subst_wvl_vl v) /\
    (forall E, open_wvl_subst_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq nat; try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : open_wvl_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_vl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_vnt _ |- _ => erewrite RR; eauto
    end.
    assert (open_wvl_lc_wvl u U) by eapply open_wvl_lc.
    rw. eauto.
  Qed.

  Definition open_wvl_subst_loc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ u ν,
      subst_loc_wvl ν ℓ (open_wvl_wvl i u w) =
      open_wvl_wvl i (subst_loc_wvl ν ℓ u) (subst_loc_wvl ν ℓ w)
  .

  Definition open_wvl_subst_loc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ u ν,
      subst_loc_nv ν ℓ (open_wvl_nv i u σ) =
      open_wvl_nv i (subst_loc_wvl ν ℓ u) (subst_loc_nv ν ℓ σ)
  .

  Definition open_wvl_subst_loc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ u ν,
      subst_loc_vl ν ℓ (open_wvl_vl i u v) =
      open_wvl_vl i (subst_loc_wvl ν ℓ u) (subst_loc_vl ν ℓ v)
  .

  Definition open_wvl_subst_loc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ u ν,
      subst_loc_vnt ν ℓ (open_wvl_vnt i u E) =
      open_wvl_vnt i (subst_loc_wvl ν ℓ u) (subst_loc_vnt ν ℓ E)
  .

  Lemma open_wvl_subst_loc `{Eq lbl} `{Eq loc} :
    (forall w, open_wvl_subst_loc_wvl w) /\
    (forall σ, open_wvl_subst_loc_nv σ) /\
    (forall v, open_wvl_subst_loc_vl v) /\
    (forall E, open_wvl_subst_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq nat; try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : open_wvl_subst_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_loc_nv _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_loc_vl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_loc_vnt _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition open_loc_subst_wvl_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_wvl u ℓ (open_loc_wvl i ν w) =
      open_loc_wvl i ν (subst_wvl_wvl u ℓ w)
  .

  Definition open_loc_subst_wvl_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_nv u ℓ (open_loc_nv i ν σ) =
      open_loc_nv i ν (subst_wvl_nv u ℓ σ)
  .

  Definition open_loc_subst_wvl_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_vl u ℓ (open_loc_vl i ν v) =
      open_loc_vl i ν (subst_wvl_vl u ℓ v)
  .
  
  Definition open_loc_subst_wvl_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_vnt u ℓ (open_loc_vnt i ν E) =
      open_loc_vnt i ν (subst_wvl_vnt u ℓ E)
  .

  Lemma open_loc_subst_wvl `{Eq lbl} `{Name loc} :
    (forall w, open_loc_subst_wvl_wvl w) /\
    (forall σ, open_loc_subst_wvl_nv σ) /\
    (forall v, open_loc_subst_wvl_vl v) /\
    (forall E, open_loc_subst_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq nat; try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : open_loc_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_vl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_vnt _ |- _ => erewrite RR; eauto
    end.
    assert (open_loc_lc_wvl u U) by apply open_loc_lc.
    rw. eauto.
  Qed.

  Definition open_loc_subst_loc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_wvl ν ℓ (open_loc_wvl i ℓ' w) =
      open_loc_wvl i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_wvl ν ℓ w)
  .

  Definition open_loc_subst_loc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_nv ν ℓ (open_loc_nv i ℓ' σ) =
      open_loc_nv i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_nv ν ℓ σ)
  .

  Definition open_loc_subst_loc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_vl ν ℓ (open_loc_vl i ℓ' v) =
      open_loc_vl i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_vl ν ℓ v)
  .

  Definition open_loc_subst_loc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_vnt ν ℓ (open_loc_vnt i ℓ' E) =
      open_loc_vnt i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_vnt ν ℓ E)
  .

  Lemma open_loc_subst_loc `{Eq lbl} `{Eq loc} :
    (forall w, open_loc_subst_loc_wvl w) /\
    (forall σ, open_loc_subst_loc_nv σ) /\
    (forall v, open_loc_subst_loc_vl v) /\
    (forall E, open_loc_subst_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; split_nIn;
    repeat des_goal; repeat des_hyp;
    try eqb2eq nat; try eqb2eq loc; try eqb2eq lbl; clarify.
    all: repeat match goal with
    | RR : open_loc_subst_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_vl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_vnt _ |- _ => erewrite RR; eauto
    end.
    all: repeat first [
      rewrite eqb_refl; auto |
      des_goal | des_hyp | eqb2eq loc; clarify | eqb2eq lbl; clarify | ss].
  Qed.

  Definition subst_wvl_close_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ p ν u
      (NEQ : (ℓ, p) <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_wvl i (ℓ, p) (subst_wvl_wvl u ν w) =
    subst_wvl_wvl u ν (close_wvl i (ℓ, p) w).

  Definition subst_wvl_close_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ p ν u
      (NEQ : (ℓ, p) <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_nv i (ℓ, p) (subst_wvl_nv u ν σ) =
    subst_wvl_nv u ν (close_nv i (ℓ, p) σ).

  Definition subst_wvl_close_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ p ν u
      (NEQ : (ℓ, p) <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_vl i (ℓ, p) (subst_wvl_vl u ν v) =
    subst_wvl_vl u ν (close_vl i (ℓ, p) v).

  Definition subst_wvl_close_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ p ν u
      (NEQ : (ℓ, p) <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_vnt i (ℓ, p) (subst_wvl_vnt u ν E) =
    subst_wvl_vnt u ν (close_vnt i (ℓ, p) E).

  Ltac subst_wvl_close_tac :=
    repeat match goal with
    | H : subst_wvl_close_wvl _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_nv _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_vl _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_vnt _ |- _ => rewrite H; eauto
    end.

  Lemma subst_wvl_close `{Eq lbl} `{Eq loc} :
    (forall w, subst_wvl_close_wvl w) /\
    (forall σ, subst_wvl_close_nv σ) /\
    (forall v, subst_wvl_close_vl v) /\
    (forall E, subst_wvl_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; subst_wvl_close_tac.
    repeat des_goal; repeat des_hyp;
    repeat eqb2eq loc; repeat eqb2eq lbl; clarify;
    subst_wvl_close_tac.
    all: assert (close_fresh_wvl u) by apply close_fresh.
    all: rw; eauto.
  Qed.

  Definition subst_loc_close_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_wvl i ℓ (subst_loc_wvl u ν w) =
    subst_loc_wvl u ν (close_wvl i ℓ w).

  Definition subst_loc_close_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_nv i ℓ (subst_loc_nv u ν σ) =
    subst_loc_nv u ν (close_nv i ℓ σ).

  Definition subst_loc_close_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ℓ <> u),
    close_vl i ℓ (subst_loc_vl u ν v) =
    subst_loc_vl u ν (close_vl i ℓ v).

  Definition subst_loc_close_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
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

  Lemma subst_loc_close `{Eq lbl} `{Eq loc} :
    (forall w, subst_loc_close_wvl w) /\
    (forall σ, subst_loc_close_nv σ) /\
    (forall v, subst_loc_close_vl v) /\
    (forall E, subst_loc_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; subst_loc_close_tac.
    repeat des_goal; repeat des_hyp;
    repeat eqb2eq loc; repeat eqb2eq lbl; clarify;
    subst_loc_close_tac.
  Qed.

  Definition close_open_loc_eq_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ ν,
      open_loc_wvl i ν (close_wvl i ℓ w) =
      subst_loc_wvl ν ℓ (open_loc_wvl i ℓ w).

  Definition close_open_loc_eq_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ ν,
      open_loc_nv i ν (close_nv i ℓ σ) =
      subst_loc_nv ν ℓ (open_loc_nv i ℓ σ).

  Definition close_open_loc_eq_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ ν,
      open_loc_vl i ν (close_vl i ℓ v) =
      subst_loc_vl ν ℓ (open_loc_vl i ℓ v).

  Definition close_open_loc_eq_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ ν,
      open_loc_vnt i ν (close_vnt i ℓ E) =
      subst_loc_vnt ν ℓ (open_loc_vnt i ℓ E).

  Lemma close_open_loc_eq `{Eq lbl} `{Eq loc} :
    (forall w, close_open_loc_eq_wvl w) /\
    (forall σ, close_open_loc_eq_nv σ) /\
    (forall v, close_open_loc_eq_vl v) /\
    (forall E, close_open_loc_eq_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; try solve [repeat rw; eauto];
    repeat des_goal; repeat des_hyp;
    repeat first [eqb2eq nat | eqb2eq loc | eqb2eq lbl]; clarify;
    try solve [rw; eauto].
  Qed.

  Definition subst_loc_lc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) (W : wvalue w) :=
    forall ℓ ν, wvalue (subst_loc_wvl ν ℓ w).

  Definition subst_loc_lc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) (Σ : env σ) :=
    forall ℓ ν, env (subst_loc_nv ν ℓ σ).

  Definition subst_loc_lc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) (V : value v) :=
    forall ℓ ν, value (subst_loc_vl ν ℓ v).

  Definition subst_loc_lc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) (EE : event E) :=
    forall ℓ ν, event (subst_loc_vnt ν ℓ E).

  Lemma subst_loc_lc `{Eq lbl} `{Eq loc} :
    (forall w W, subst_loc_lc_wvl w W) /\
    (forall σ Σ, subst_loc_lc_nv σ Σ) /\
    (forall v V, subst_loc_lc_vl v V) /\
    (forall E EE, subst_loc_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss;
    try (repeat des_goal; repeat des_hyp;
      repeat first [eqb2eq loc | eqb2eq lbl]; clarify);
    try solve [econstructor; eauto].
    econstructor.
    instantiate (1 := fst ℓ :: L). ii. split_nIn.
    exploit VAL; eauto. ii.
    match goal with H : forall _, ~ In _ _ -> _ |- _ => exploit H; eauto end.
    instantiate (1 := ℓ). instantiate (1 := ν).
    assert (open_loc_subst_loc_vl v) by apply open_loc_subst_loc.
    rw. des_ifs. destruct ℓ; ss; des_hyp; eqb2eq loc; clarify.
  Qed.

  Definition subst_wvl_lc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) (W : wvalue w) :=
    forall ℓ u (U : wvalue u), wvalue (subst_wvl_wvl u ℓ w).

  Definition subst_wvl_lc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) (Σ : env σ) :=
    forall ℓ u (U : wvalue u), env (subst_wvl_nv u ℓ σ).

  Definition subst_wvl_lc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) (V : value v) :=
    forall ℓ u (U : wvalue u), value (subst_wvl_vl u ℓ v).

  Definition subst_wvl_lc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) (EE : event E) :=
    forall ℓ u (U : wvalue u), event (subst_wvl_vnt u ℓ E).

  Lemma subst_wvl_lc `{Eq lbl} `{Name loc} :
    (forall w W, subst_wvl_lc_wvl w W) /\
    (forall σ Σ, subst_wvl_lc_nv σ Σ) /\
    (forall v V, subst_wvl_lc_vl v V) /\
    (forall E EE, subst_wvl_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss;
    try (repeat des_goal; repeat des_hyp;
      repeat first [eqb2eq loc | eqb2eq lbl]; clarify);
    try solve [econstructor; eauto].
    econstructor.
    instantiate (1 := fst ℓ :: L). ii. split_nIn.
    exploit VAL; eauto. ii.
    match goal with H : forall _, ~ In _ _ -> _ |- _ => exploit H; eauto end.
    instantiate (1 := ℓ).
    assert (open_loc_subst_wvl_vl v) by eapply open_loc_subst_wvl.
    rw; eauto. destruct ℓ; ss; ii; clarify.
  Qed.

  Definition map_close_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ p φ (INJ : oto φ),
      map_wvl φ (close_wvl i (ℓ, p) w) = close_wvl i (φ ℓ, p) (map_wvl φ w).

  Definition map_close_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ p φ (INJ : oto φ),
      map_nv φ (close_nv i (ℓ, p) σ) = close_nv i (φ ℓ, p) (map_nv φ σ).

  Definition map_close_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ p φ (INJ : oto φ),
      map_vl φ (close_vl i (ℓ, p) v) = close_vl i (φ ℓ, p) (map_vl φ v).

  Definition map_close_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ p φ (INJ : oto φ),
      map_vnt φ (close_vnt i (ℓ, p) E) = close_vnt i (φ ℓ, p) (map_vnt φ E).

  Lemma map_close `{Eq lbl} `{Eq loc} :
    (forall w, map_close_wvl w) /\
    (forall σ, map_close_nv σ) /\
    (forall v, map_close_vl v) /\
    (forall E, map_close_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; unfold oto in INJ; repeat rw; eauto.
    repeat des_goal; repeat des_hyp.
    all: repeat first [eqb2eq loc | eqb2eq lbl]; clarify; ss.
    all: repeat rw; eauto.
    all: match goal with
    | H : ?φ _ = ?φ _ |- _ => apply INJ in H; clarify
    end.
  Qed.

  Definition map_open_wvl_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i u φ,
      map_wvl φ (open_wvl_wvl i u w) = open_wvl_wvl i (map_wvl φ u) (map_wvl φ w).

  Definition map_open_wvl_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i u φ,
      map_nv φ (open_wvl_nv i u σ) = open_wvl_nv i (map_wvl φ u) (map_nv φ σ).

  Definition map_open_wvl_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i u φ,
      map_vl φ (open_wvl_vl i u v) = open_wvl_vl i (map_wvl φ u) (map_vl φ v).

  Definition map_open_wvl_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i u φ,
      map_vnt φ (open_wvl_vnt i u E) = open_wvl_vnt i (map_wvl φ u) (map_vnt φ E).

  Lemma map_open_wvl `{Eq lbl} `{Eq loc} :
    (forall w, map_open_wvl_wvl w) /\
    (forall σ, map_open_wvl_nv σ) /\
    (forall v, map_open_wvl_vl v) /\
    (forall E, map_open_wvl_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; eauto.
    repeat des_goal; repeat des_hyp.
    all: repeat first [eqb2eq loc | eqb2eq lbl]; clarify; ss.
    all: repeat rw; repeat des_goal; eauto.
  Qed.

  Definition map_open_loc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i u p φ,
      map_wvl φ (open_loc_wvl i (u, p) w) = open_loc_wvl i (φ u, p) (map_wvl φ w).

  Definition map_open_loc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i u p φ,
      map_nv φ (open_loc_nv i (u, p) σ) = open_loc_nv i (φ u, p) (map_nv φ σ).

  Definition map_open_loc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i u p φ,
      map_vl φ (open_loc_vl i (u, p) v) = open_loc_vl i (φ u, p) (map_vl φ v).

  Definition map_open_loc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i u p φ,
      map_vnt φ (open_loc_vnt i (u, p) E) = open_loc_vnt i (φ u, p) (map_vnt φ E).

  Lemma map_open_loc `{Eq lbl} `{Eq loc} :
    (forall w, map_open_loc_wvl w) /\
    (forall σ, map_open_loc_nv σ) /\
    (forall v, map_open_loc_vl v) /\
    (forall E, map_open_loc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; eauto.
    repeat des_goal; repeat des_hyp.
    all: repeat first [eqb2eq loc | eqb2eq lbl]; clarify; ss.
    all: repeat rw; repeat des_goal; eauto.
  Qed.

  Definition floc_map_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_wvl w)),
      In (φ ℓ) (floc_wvl (map_wvl φ w)).

  Definition floc_map_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_nv σ)),
      In (φ ℓ) (floc_nv (map_nv φ σ)).

  Definition floc_map_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_vl v)),
      In (φ ℓ) (floc_vl (map_vl φ v)).

  Definition floc_map_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall ℓ φ (IN : In ℓ (floc_vnt E)),
      In (φ ℓ) (floc_vnt (map_vnt φ E)).

  Lemma floc_map `{Eq lbl} `{Eq loc} :
    (forall w, floc_map_wvl w) /\
    (forall σ, floc_map_nv σ) /\
    (forall v, floc_map_vl v) /\
    (forall E, floc_map_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_hyp; des; clarify; ss; auto.
    all: rewrite in_app_iff in *; des; clarify; auto.
  Qed.

  Definition map_floc_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_wvl (map_wvl φ w))),
    In ℓ (floc_wvl w).

  Definition map_floc_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_nv (map_nv φ σ))),
    In ℓ (floc_nv σ).

  Definition map_floc_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_vl (map_vl φ v))),
    In ℓ (floc_vl v).

  Definition map_floc_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall ℓ φ (INJ : oto φ)
      (IN : In (φ ℓ) (floc_vnt (map_vnt φ E))),
    In ℓ (floc_vnt E).
 
  Lemma map_floc `{Eq lbl} `{Eq loc} :
    (forall w, map_floc_wvl w) /\
    (forall σ, map_floc_nv σ) /\
    (forall v, map_floc_vl v) /\
    (forall E, map_floc_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; eauto;
    repeat des_hyp; ss; des; eauto.
    all: rewrite in_app_iff in *; ss; des; eauto.
  Qed.

  Definition map_id_is_id_wvl (w : wvl var lbl loc lang) :=
    map_wvl id w = w.

  Definition map_id_is_id_nv (σ : nv var lbl loc lang) :=
    map_nv id σ = σ.

  Definition map_id_is_id_vl (v : vl var lbl loc lang) :=
    map_vl id v = v.

  Definition map_id_is_id_vnt (E : vnt var lbl loc lang) :=
    map_vnt id E = E.
  
  Lemma map_id_is_id :
    (forall w, map_id_is_id_wvl w) /\
    (forall σ, map_id_is_id_nv σ) /\
    (forall v, map_id_is_id_vl v) /\
    (forall E, map_id_is_id_vnt E).
  Proof.
    apply pre_val_ind; ii; red; s; repeat rw; des_ifs; eauto.
  Qed.

  Definition swap_is_subst_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall φ (INJ : oto φ) ℓ ν p
      (FRESH : ~ In ℓ (floc_wvl w)) (UNIQUE : forall p', In (ν, p') (flloc_wvl w) -> p' = p),
      map_wvl (swap φ ℓ ν) w = subst_loc_wvl (φ ℓ, p) (φ ν, p) (map_wvl φ w).

  Definition swap_is_subst_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall φ (INJ : oto φ) ℓ ν p
      (FRESH : ~ In ℓ (floc_nv σ)) (UNIQUE : forall p', In (ν, p') (flloc_nv σ) -> p' = p),
      map_nv (swap φ ℓ ν) σ = subst_loc_nv (φ ℓ, p) (φ ν, p) (map_nv φ σ).

  Definition swap_is_subst_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall φ (INJ : oto φ) ℓ ν p
      (FRESH : ~ In ℓ (floc_vl v)) (UNIQUE : forall p', In (ν, p') (flloc_vl v) -> p' = p),
      map_vl (swap φ ℓ ν) v = subst_loc_vl (φ ℓ, p) (φ ν, p) (map_vl φ v).

  Definition swap_is_subst_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall φ (INJ : oto φ) ℓ ν p
      (FRESH : ~ In ℓ (floc_vnt E)) (UNIQUE : forall p', In (ν, p') (flloc_vnt E) -> p' = p),
      map_vnt (swap φ ℓ ν) E = subst_loc_vnt (φ ℓ, p) (φ ν, p) (map_vnt φ E).

  Lemma swap_is_subst `{Eq lbl} `{Eq loc} :
    (forall w, swap_is_subst_wvl w) /\
    (forall σ, swap_is_subst_nv σ) /\
    (forall v, swap_is_subst_vl v) /\
    (forall E, swap_is_subst_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; des_ifs;
    repeat match goal with
    | RR : swap_is_subst_wvl _ |- _ => rewrite RR
    | RR : swap_is_subst_nv _ |- _ => rewrite RR
    | RR : swap_is_subst_vl _ |- _ => rewrite RR
    | RR : swap_is_subst_vnt _ |- _ => rewrite RR
    end; split_nIn; eauto.
    all: try solve [ii; apply UNIQUE; rewrite in_app_iff; eauto].
    unfold swap; repeat des_goal; repeat des_hyp;
    repeat first [rewrite eqb_eq in * | rewrite eqb_neq in *]; clarify.
    all: match goal with
    | _ => solve [exfalso; try_all; symmetry; apply UNIQUE; auto]
    | H : ?φ _ = ?φ _ |- _ => apply INJ in H; split_nIn; clarify
    end.
  Qed.

  Definition subst_loc_close_eq_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (flloc_wvl w)),
      close_wvl i ℓ (subst_loc_wvl ℓ ν w) = close_wvl i ν w.

  Definition subst_loc_close_eq_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (flloc_nv σ)),
      close_nv i ℓ (subst_loc_nv ℓ ν σ) = close_nv i ν σ.

  Definition subst_loc_close_eq_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (flloc_vl v)),
      close_vl i ℓ (subst_loc_vl ℓ ν v) = close_vl i ν v.

  Definition subst_loc_close_eq_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall i ℓ ν (FRESH : ~ In ℓ (flloc_vnt E)),
      close_vnt i ℓ (subst_loc_vnt ℓ ν E) = close_vnt i ν E.

  Lemma subst_loc_close_eq `{Eq lbl} `{Eq loc} :
    (forall w, subst_loc_close_eq_wvl w) /\
    (forall σ, subst_loc_close_eq_nv σ) /\
    (forall v, subst_loc_close_eq_vl v) /\
    (forall E, subst_loc_close_eq_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; split_nIn; eauto.
    repeat des_goal; repeat des_hyp;
    repeat first [rewrite eqb_eq in * | rewrite eqb_neq in *]; clarify.
    all: rw; eauto.
  Qed.

  Definition map_ext_wvl (w : wvl var lbl loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_wvl w)), φ ℓ = ϕ ℓ),
      map_wvl φ w = map_wvl ϕ w.

  Definition map_ext_nv (σ : nv var lbl loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_nv σ)), φ ℓ = ϕ ℓ),
      map_nv φ σ = map_nv ϕ σ.

  Definition map_ext_vl (v : vl var lbl loc lang) :=
    forall φ ϕ (EXT : forall ℓ (DOM : In ℓ (floc_vl v)), φ ℓ = ϕ ℓ),
      map_vl φ v = map_vl ϕ v.

  Definition map_ext_vnt (E : vnt var lbl loc lang) :=
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
    des_goal; erewrite EXT; ss; clarify; auto.
    all:ii; apply EXT; first [des_goal | rewrite in_app_iff]; eauto.
  Qed.

  Definition map_compose_wvl (w : wvl var lbl loc lang) :=
    forall φ ϕ,
      map_wvl φ (map_wvl ϕ w) = map_wvl (φ <*> ϕ) w.

  Definition map_compose_nv (σ : nv var lbl loc lang) :=
    forall φ ϕ,
      map_nv φ (map_nv ϕ σ) = map_nv (φ <*> ϕ) σ.

  Definition map_compose_vl (v : vl var lbl loc lang) :=
    forall φ ϕ,
      map_vl φ (map_vl ϕ v) = map_vl (φ <*> ϕ) v.

  Definition map_compose_vnt (E : vnt var lbl loc lang) :=
    forall φ ϕ,
      map_vnt φ (map_vnt ϕ E) = map_vnt (φ <*> ϕ) E.

  Lemma map_compose :
    (forall w, map_compose_wvl w) /\
    (forall σ, map_compose_nv σ) /\
    (forall v, map_compose_vl v) /\
    (forall E, map_compose_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; des_ifs; ss; repeat rw; auto.
  Qed.

  Definition map_lc_wvl (w : wvl var lbl loc lang) (W : wvalue w) :=
    forall φ, wvalue (map_wvl φ w).

  Definition map_lc_nv (σ : nv var lbl loc lang) (Σ : env σ) :=
    forall φ, env (map_nv φ σ).

  Definition map_lc_vl (v : vl var lbl loc lang) (V : value v) :=
    forall φ, value (map_vl φ v).

  Definition map_lc_vnt (E : vnt var lbl loc lang) (EE : event E) :=
    forall φ, event (map_vnt φ E).

  Lemma map_lc `{Eq lbl} `{Name loc} :
    (forall w W, map_lc_wvl w W) /\
    (forall σ Σ, map_lc_nv σ Σ) /\
    (forall v V, map_lc_vl v V) /\
    (forall E EE, map_lc_vnt E EE).
  Proof.
    apply val_ind; ii; ss; des_ifs; econstructor; eauto.
    instantiate (1 := []).
    ii. gensym_tac (L ++ floc_vl v) ν.
    match goal with H : forall _, ~ In _ _ -> map_lc_vl _ _ |- _ => exploit H; eauto end.
    instantiate (1 := fun x => if eqb x ν then ℓ else φ x).
    assert (map_open_loc_vl v) by eapply map_open_loc.
    rw. rewrite eqb_refl.
    assert (map_ext_vl v) as RR by apply map_ext.
    erewrite RR; eauto. clear RR.
    ii. des_goal; first [rewrite eqb_eq in * | rewrite eqb_neq in *]; clarify.
  Qed.

  Definition subst_id_wvl `{Eq lbl} `{Eq loc} (w : wvl var lbl loc lang) :=
    forall ℓ, subst_loc_wvl ℓ ℓ w = w.

  Definition subst_id_nv `{Eq lbl} `{Eq loc} (σ : nv var lbl loc lang) :=
    forall ℓ, subst_loc_nv ℓ ℓ σ = σ.

  Definition subst_id_vl `{Eq lbl} `{Eq loc} (v : vl var lbl loc lang) :=
    forall ℓ, subst_loc_vl ℓ ℓ v = v.

  Definition subst_id_vnt `{Eq lbl} `{Eq loc} (E : vnt var lbl loc lang) :=
    forall ℓ, subst_loc_vnt ℓ ℓ E = E.
  
  Lemma subst_id `{Eq lbl} `{Eq loc} :
    (forall w, subst_id_wvl w) /\
    (forall σ, subst_id_nv σ) /\
    (forall v, subst_id_vl v) /\
    (forall E, subst_id_vnt E).
  Proof.
    apply pre_val_ind; ii; ss; repeat rw; eauto;
    repeat des_goal; repeat des_hyp;
    repeat first [eqb2eq loc | eqb2eq lbl]; clarify.
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
