From Basics Require Import Basics.
From LN Require Import Defs.

Section SubstFacts.
  Variable var : Set.
  Variable loc : Type.
  Variable lang : Type.

  Definition open_floc_wvl (w : wvl var loc lang) :=
    forall i ℓ x, In x (floc_wvl (open_loc_wvl i ℓ w)) -> x = ℓ \/ In x (floc_wvl w).

  Definition open_floc_nv (σ : nv var loc lang) :=
    forall i ℓ x, In x (floc_nv (open_loc_nv i ℓ σ)) -> x = ℓ \/ In x (floc_nv σ).

  Definition open_floc_vl (v : vl var loc lang) :=
    forall i ℓ x, In x (floc_vl (open_loc_vl i ℓ v)) -> x = ℓ \/ In x (floc_vl v).

  Lemma open_floc :
    (forall w, open_floc_wvl w) /\
    (forall σ, open_floc_nv σ) /\
    (forall v, open_floc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_floc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_floc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_floc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
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

  Lemma open_inc_floc :
    (forall w, open_inc_floc_wvl w) /\
    (forall σ, open_inc_floc_nv σ) /\
    (forall v, open_inc_floc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat match goal with
    | _ => solve [eauto]
    | H : open_inc_floc_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_inc_floc_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : open_inc_floc_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
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

  Lemma subst_intro `{Eq loc} :
    (forall w, subst_intro_wvl w) /\
    (forall σ, subst_intro_nv σ) /\
    (forall v, subst_intro_vl v).
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
    - f_equal.
      all: try_all;
        ii; apply FRESH; ss; rewrite in_app_iff; auto.
  Qed.

  Definition open_loc_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ, close_wvl i ℓ (open_loc_wvl i ℓ w) = close_wvl i ℓ w.

  Definition open_loc_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ, close_nv i ℓ (open_loc_nv i ℓ σ) = close_nv i ℓ σ.

  Definition open_loc_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ, close_vl i ℓ (open_loc_vl i ℓ v) = close_vl i ℓ v.

  Lemma open_loc_close `{Eq loc} :
    (forall w, open_loc_close_wvl w) /\
    (forall σ, open_loc_close_nv σ) /\
    (forall v, open_loc_close_vl v).
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

  Lemma close_fresh `{Eq loc} :
    (forall w, close_fresh_wvl w) /\
    (forall σ, close_fresh_nv σ) /\
    (forall v, close_fresh_vl v).
  Proof.
    apply pre_val_ind; ii; ss; split_nIn;
    try (progress des_ifs; eqb2eq loc; clarify).
    all: repeat match goal with
    | RR : close_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : close_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : close_fresh_vl _ |- _ => erewrite RR; eauto
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

  Lemma close_open_wvl `{Eq loc} :
    (forall w, close_open_wvl_wvl w) /\
    (forall σ, close_open_wvl_nv σ) /\
    (forall v, close_open_wvl_vl v).
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

  Lemma close_open_loc `{Eq loc} :
    (forall w, close_open_loc_wvl w) /\
    (forall σ, close_open_loc_nv σ) /\
    (forall v, close_open_loc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : close_open_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_nv _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_vl _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition open_wvl_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall i u, open_wvl_wvl i u w = w.

  Definition open_wvl_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall i u, open_wvl_nv i u σ = σ.

  Definition open_wvl_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall i u, open_wvl_vl i u v = v.

  Lemma open_wvl_lc `{Name loc} :
    (forall w W, open_wvl_lc_wvl w W) /\
    (forall σ Σ, open_wvl_lc_nv σ Σ) /\
    (forall v V, open_wvl_lc_vl v V).
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

  Lemma open_loc_lc `{Name loc} :
    (forall w W, open_loc_lc_wvl w W) /\
    (forall σ Σ, open_loc_lc_nv σ Σ) /\
    (forall v V, open_loc_lc_vl v V).
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

  Lemma open_wvl_subst_wvl `{Name loc} :
    (forall w, open_wvl_subst_wvl_wvl w) /\
    (forall σ, open_wvl_subst_wvl_nv σ) /\
    (forall v, open_wvl_subst_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_wvl_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_vl _ |- _ => erewrite RR; eauto
    end.
    assert (open_wvl_lc_wvl u U) by eapply open_wvl_lc.
    rw. eauto.
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

  Lemma open_loc_subst_wvl `{Name loc} :
    (forall w, open_loc_subst_wvl_wvl w) /\
    (forall σ, open_loc_subst_wvl_nv σ) /\
    (forall v, open_loc_subst_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_loc_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_vl _ |- _ => erewrite RR; eauto
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

  Lemma open_loc_subst_loc `{Eq loc} :
    (forall w, open_loc_subst_loc_wvl w) /\
    (forall σ, open_loc_subst_loc_nv σ) /\
    (forall v, open_loc_subst_loc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_loc_subst_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_vl _ |- _ => erewrite RR; eauto
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

  Ltac subst_wvl_close_tac :=
    repeat match goal with
    | H : subst_wvl_close_wvl _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_nv _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_vl _ |- _ => rewrite H; eauto
    end.

  Lemma subst_wvl_close `{Eq loc} :
    (forall w, subst_wvl_close_wvl w) /\
    (forall σ, subst_wvl_close_nv σ) /\
    (forall v, subst_wvl_close_vl v).
  Proof.
    apply pre_val_ind; ii; ss; subst_wvl_close_tac.
    repeat des_goal; repeat eqb2eq loc; clarify;
    subst_wvl_close_tac.
    assert (close_fresh_wvl u) by apply close_fresh.
    rw; eauto.
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

  Lemma floc_subst_wvl `{Eq loc} :
    (forall w, floc_subst_wvl_wvl w) /\
    (forall σ, floc_subst_wvl_nv σ) /\
    (forall v, floc_subst_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss;
    try solve [exploit H0; eauto].
    all: repeat des_hyp; repeat rewrite in_app_iff in *; des;
    repeat eqb2eq loc; subst; try solve [auto];
    match goal with
    | H : floc_subst_wvl_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    end.
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
