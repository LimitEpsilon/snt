From Stdlib Require Import
  Utf8
.
From Koika Require Import
  Common.CtxNotations
  Lang.Types
  Lang.Syntax
  Lang.BigStepSemantics
.
From Koika Require Export
  Lang.MayAbortSemantics
.

Section facts.
  Context {mod_t} {M : Modules.t mod_t}.
  Context {Σ : ∀ m, Sem.t (Modules.get_sig m)}.
  Context {St : State Σ}.

(* Useful lemmas *)
  Lemma linterp_pure_implies
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P P' (IMPLY : ∀ x' log', P x' log' → P' x' log'),
        linterp_pure St U x log P →
        linterp_pure St U x log P'
    | Effectful => fun _ => True
    end e.
  Proof.
  induction e; cbn; auto; intros.
  - eapply IHe; eauto. auto.
  - eapply IHe1; eauto; cbn.
    intros; eapply IHe2; eauto. auto.
  - match goal with
    | H : cfoldr _ _ _ ?f _ |- cfoldr _ _ _ ?f' _ =>
      revert H; set (Q := f); set (Q' := f')
    end.
    assert (IMPLYQ : ∀ x' log', Q x' log' → Q' x' log').
    { subst Q. subst Q'. cbn. intuition. }
    generalize Q Q' IMPLYQ. clear Q Q' IMPLYQ.
    revert U log P P' IMPLY.
    subst met_sig.
    generalize dependent args.
    induction args; cbn; auto.
    intros (HD & TL). intros. eapply HD; eauto.
    cbn; intros. eapply IHargs; eauto. cbn. auto.
  - destruct eff; cbn; auto; intros.
    eapply IHe; eauto; intros.
    eapply IHa2; eauto.
  - destruct eff; cbn; auto.
    intros. eapply IHe1; eauto. cbn. intros.
    destruct (Bits.single x'); eauto.
  Qed.

  Lemma interp_pure_implies
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P P' (IMPLY : ∀ x', P x' → P' x'),
        interp_pure St U x P →
        interp_pure St U x P'
    | Effectful => fun _ => True
    end e.
  Proof.
  induction e; cbn; auto; intros.
  - eapply IHe; eauto. auto.
  - eapply IHe1; eauto; cbn.
    intros; eapply IHe2; eauto. auto.
  - unfold fold_pure in *.
    match goal with
    | H : cfoldr _ _ _ ?f |- cfoldr _ _ _ ?f' =>
      revert H; set (Q := f); set (Q' := f')
    end.
    assert (IMPLYQ : ∀ x', Q x' → Q' x').
    { subst Q. subst Q'. cbn. intuition. }
    generalize Q Q' IMPLYQ. clear Q Q' IMPLYQ.
    revert U P P' IMPLY.
    subst met_sig.
    generalize dependent args.
    induction args; cbn; auto.
    intros (HD & TL). intros. eapply HD; eauto.
    cbn; intros. eapply IHargs; eauto. cbn. auto.
  - destruct eff; cbn; auto; intros.
    eapply IHe; eauto; intros.
    eapply IHa2; eauto.
  - destruct eff; cbn; auto.
    intros. eapply IHe1; eauto. cbn. intros.
    destruct (Bits.single x'); eauto.
  Qed.

  Lemma linterp_pure_ext
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P P' (EQ : ∀ x' log', P x' log' ↔ P' x' log'),
        linterp_pure St U x log P ↔
        linterp_pure St U x log P'
    | Effectful => fun _ => True
    end e.
  Proof.
  pose proof (linterp_pure_implies Pure) as HINT.
  destruct E; auto.
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma interp_pure_ext
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P P' (EQ : ∀ x', P x' ↔ P' x'),
        interp_pure St U x P ↔
        interp_pure St U x P'
    | Effectful => fun _ => True
    end e.
  Proof.
  pose proof (interp_pure_implies Pure) as HINT.
  destruct E; auto.
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma linterp_implies
  : ∀ E ty (e : t _ E ty) (U : Update Σ) log P P'
    (IMPLY : ∀ x' U' log', P x' U' log' → P' x' U' log'),
    linterp St e U log P → linterp St e U log P'.
  Proof.
  pose proof (linterp_pure_implies Pure) as HINT. cbn in HINT.
  induction e; cbn [linterp]; intros;
  try solve [eapply HINT; try eassumption; cbn; intuition].
  - match goal with
    | H : cfoldr _ _ _ ?f _ |- cfoldr _ _ _ ?f' _ =>
      revert H; set (Q := f); set (Q' := f')
    end.
    assert (IMPLYQ : ∀ x' log', Q x' log' → Q' x' log').
    { subst Q. subst Q'. cbn. intuition. }
    generalize Q Q' IMPLYQ. clear Q Q' IMPLYQ.
    revert U log P P' IMPLY.
    subst met_sig.
    generalize dependent args.
    induction args; cbn; auto.
    intros (HD & TL). intros. eapply HINT; eauto.
    cbn; intros. eapply IHargs; eauto. cbn. auto.
  - destruct eff; first [eapply HINT | eapply IHe]; try eassumption;
    auto. cbn.
    intros. eapply IHa2; try eassumption.
  - destruct eff; first [eapply HINT | eapply IHe]; try eassumption;
    auto. cbn.
    intros; destruct (Bits.single x'); eauto.
  Qed.

  Lemma interp_implies
  : ∀ E ty (e : t _ E ty) (U : Update Σ) P P'
    (IMPLY : ∀ x' U', P x' U' → P' x' U'),
    interp St e U P → interp St e U P'.
  Proof.
  pose proof (interp_pure_implies Pure) as HINT. cbn in HINT.
  induction e; cbn [interp]; intros;
  try solve [eapply HINT; try eassumption; cbn; intuition].
  - unfold fold_pure in *.
    match goal with
    | H : cfoldr _ _ _ ?f |- cfoldr _ _ _ ?f' =>
      revert H; set (Q := f); set (Q' := f')
    end.
    assert (IMPLYQ : ∀ x', Q x' → Q' x').
    { subst Q. subst Q'. cbn. intuition. }
    generalize Q Q' IMPLYQ. clear Q Q' IMPLYQ.
    revert U P P' IMPLY.
    subst met_sig.
    generalize dependent args.
    induction args; cbn; auto.
    intros (HD & TL). intros. eapply HINT; eauto.
    cbn; intros. eapply IHargs; eauto. cbn. auto.
  - destruct eff; first [eapply HINT | eapply IHe]; try eassumption;
    auto. cbn.
    intros. eapply IHa2; try eassumption.
  - destruct eff; first [eapply HINT | eapply IHe]; try eassumption;
    auto. cbn.
    intros; destruct (Bits.single x'); eauto.
  Qed.

  Lemma linterp_ext
  : ∀ E ty (e : t _ E ty) (U : Update Σ) log P P'
    (EQ : ∀ x' U' log', P x' U' log' ↔ P' x' U' log'),
    linterp St e U log P ↔ linterp St e U log P'.
  Proof. split; apply linterp_implies; intros; apply EQ; auto. Qed.

  Lemma interp_ext
  : ∀ E ty (e : t _ E ty) (U : Update Σ) P P'
    (EQ : ∀ x' U', P x' U' ↔ P' x' U'),
    interp St e U P ↔ interp St e U P'.
  Proof. split; apply interp_implies; intros; apply EQ; auto. Qed.

  Lemma linterp_atom_pure_implies
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P P'
        (IMPLY : ∀ x' log', P x' log' → P' x' log'),
        linterp_atom_pure St U x log P →
        linterp_atom_pure St U x log P'
    | Effectful => fun _ => True
    end a.
  Proof.
  destruct a; try destruct eff; cbn; intuition.
  Qed.

  Lemma interp_atom_pure_implies
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P P'
        (IMPLY : ∀ x', P x' → P' x'),
        interp_atom_pure St U x P →
        interp_atom_pure St U x P'
    | Effectful => fun _ => True
    end a.
  Proof.
  destruct a; try destruct eff; cbn; intuition.
  Qed.

  Lemma linterp_atom_pure_ext
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P P'
        (EQ : ∀ x' log', P x' log' ↔ P' x' log'),
        linterp_atom_pure St U x log P ↔
        linterp_atom_pure St U x log P'
    | Effectful => fun _ => True
    end a.
  Proof.
  pose proof (linterp_atom_pure_implies Pure) as HINT.
  destruct E; auto.
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma interp_atom_pure_ext
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P P'
        (EQ : ∀ x', P x' ↔ P' x'),
        interp_atom_pure St U x P ↔
        interp_atom_pure St U x P'
    | Effectful => fun _ => True
    end a.
  Proof.
  pose proof (interp_atom_pure_implies Pure) as HINT.
  destruct E; auto.
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma linterp_atom_pure_ext_st
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U U' : Update Σ) log P
        (EQ : ∀ m, U m = U' m),
        linterp_atom_pure St U x log P →
        linterp_atom_pure St U' x log P
    | Effectful => fun _ => True
    end a.
  Proof.
  destruct a; try destruct eff; cbn; intuition.
  unfold rd_st in VSTEP. rewrite <- EQ in *. eauto.
  Qed.

  Lemma interp_atom_pure_ext_st
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U U' : Update Σ) P
        (EQ : ∀ m, U m = U' m),
        interp_atom_pure St U x P →
        interp_atom_pure St U' x P
    | Effectful => fun _ => True
    end a.
  Proof.
  destruct a; try destruct eff; cbn; intuition.
  unfold rd_st in VSTEP. rewrite <- EQ in *. eauto.
  Qed.

  Lemma linterp_atom_implies
  : ∀ E ty (a : atom _ E ty) (U : Update Σ) log P P'
      (IMPLY : ∀ x' U' log', P x' U' log' → P' x' U' log'),
      linterp_atom St a U log P →
      linterp_atom St a U log P'.
  Proof.
  pose proof (linterp_atom_pure_implies Pure) as HINT. cbn in HINT.
  destruct a; cbn [linterp_atom];
  try solve [
    intros; eapply HINT; try eassumption; cbn; intuition
  ]; intuition.
  Qed.

  Lemma interp_atom_implies
  : ∀ E ty (a : atom _ E ty) (U : Update Σ) P P'
      (IMPLY : ∀ x' U', P x' U' → P' x' U'),
      interp_atom St a U P →
      interp_atom St a U P'.
  Proof.
  pose proof (interp_atom_pure_implies Pure) as HINT. cbn in HINT.
  destruct a; cbn [interp_atom];
  try solve [
    intros; eapply HINT; try eassumption; cbn; intuition
  ]; intuition.
  Qed.

  Lemma linterp_atom_ext
  : ∀ E ty (a : atom _ E ty) (U : Update Σ) log P P'
      (EQ : ∀ x' U' log', P x' U' log' ↔ P' x' U' log'),
      linterp_atom St a U log P ↔
      linterp_atom St a U log P'.
  Proof.
  pose proof (linterp_atom_implies) as HINT.
  destruct E;
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma interp_atom_ext
  : ∀ E ty (a : atom _ E ty) (U : Update Σ) P P'
      (EQ : ∀ x' U', P x' U' ↔ P' x' U'),
      interp_atom St a U P ↔
      interp_atom St a U P'.
  Proof.
  pose proof (interp_atom_implies) as HINT.
  destruct E;
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma linterp_atom_ext_st
  : ∀ E ty (a : atom _ E ty) (U U' : Update Σ) log P
      (EXTP : ∀ x U U' log, (∀ m, U m = U' m) → P x U log → P x U' log)
      (EQ : ∀ m, U m = U' m),
      linterp_atom St a U log P →
      linterp_atom St a U' log P.
  Proof.
  pose proof (linterp_atom_pure_ext_st Pure) as HINT. cbn in HINT.
  destruct a; cbn [linterp_atom];
    intros; try eapply HINT; eauto; simpl in *; intuition; eauto.
  - eapply EXTP. instantiate (1 := upd_st U m st').
    intros; simpl. cbv.
    match goal with
    | |- match ?E with _ => _ end = match ?E with _ => _ end => destruct E
    end; eauto.
    unfold rd_st in ASTEP. rewrite <- EQ in *. eauto.
  Qed.

  Lemma interp_atom_ext_st
  : ∀ E ty (a : atom _ E ty) (U U' : Update Σ) P
      (EXTP : ∀ x U U', (∀ m, U m = U' m) → P x U → P x U')
      (EQ : ∀ m, U m = U' m),
      interp_atom St a U P →
      interp_atom St a U' P.
  Proof.
  pose proof (interp_atom_pure_ext_st Pure) as HINT. cbn in HINT.
  destruct a; cbn [interp_atom];
    intros; try eapply HINT; eauto; simpl in *; intuition; eauto.
  - eapply EXTP. instantiate (1 := upd_st U m st').
    intros; simpl. cbv.
    match goal with
    | |- match ?E with _ => _ end = match ?E with _ => _ end => destruct E
    end; eauto.
    unfold rd_st in ASTEP. rewrite <- EQ in *. eauto.
  Qed.

  Lemma linterp_linear_pure_implies
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P P'
        (IMPLY : ∀ x' log', P x' log' → P' x' log'),
        linterp_linear_pure St U x log P →
        linterp_linear_pure St U x log P'
    | Effectful => fun _ => True
    end l.
  Proof.
  pose proof (linterp_atom_pure_implies Pure) as HINT. cbn in HINT.
  induction l; cbn; destruct eff; auto; cbn; intros; eauto.
  - eapply HINT; try eassumption; eauto.
  - eapply HINT; try eassumption; cbn; intros.
    set (Q ret log' := linterp_linear_pure St U (cont ret) log' P).
    destruct (Bits.single _);
    first [apply (IHl1 _ _ Q) | apply (IHl2 _ _ Q)];
    subst Q; cbn; eauto.
  Qed.

  Lemma interp_linear_pure_implies
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P P'
        (IMPLY : ∀ x', P x' → P' x'),
        interp_linear_pure St U x P →
        interp_linear_pure St U x P'
    | Effectful => fun _ => True
    end l.
  Proof.
  pose proof (interp_atom_pure_implies Pure) as HINT. cbn in HINT.
  induction l; cbn; destruct eff; auto; cbn; intros; eauto.
  - eapply HINT; try eassumption; eauto.
  - eapply HINT; try eassumption; cbn; intros.
    set (Q ret := interp_linear_pure St U (cont ret) P).
    destruct (Bits.single _);
    first [apply (IHl1 _ Q) | apply (IHl2 _ Q)];
    subst Q; cbn; eauto.
  Qed.

  Lemma linterp_linear_pure_ext
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P P'
        (EQ : ∀ x' log', P x' log' ↔ P' x' log'),
        linterp_linear_pure St U x log P ↔
        linterp_linear_pure St U x log P'
    | Effectful => fun _ => True
    end l.
  Proof.
  pose proof (linterp_linear_pure_implies Pure) as HINT. cbn in HINT.
  destruct E;
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma interp_linear_pure_ext
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P P'
        (EQ : ∀ x', P x' ↔ P' x'),
        interp_linear_pure St U x P ↔
        interp_linear_pure St U x P'
    | Effectful => fun _ => True
    end l.
  Proof.
  pose proof (interp_linear_pure_implies Pure) as HINT. cbn in HINT.
  destruct E;
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma linterp_linear_pure_ext_st
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U U' : Update Σ) log P
        (EQ : ∀ m, U m = U' m),
        linterp_linear_pure St U x log P →
        linterp_linear_pure St U' x log P
    | Effectful => fun _ => True
    end l.
  Proof.
  pose proof (linterp_atom_pure_ext_st Pure) as HINT. cbn in HINT.
  induction l; destruct eff; cbn; auto.
  - apply HINT.
  - intros. eapply HINT; eauto.
    eapply (linterp_atom_pure_implies Pure); try eassumption.
    eauto.
  - intros. eapply HINT; eauto.
    eapply (linterp_atom_pure_implies Pure); try eassumption.
    cbn. intros. destruct (Bits.single x');
    [eapply IHl1 | eapply IHl2]; eauto;
    eapply (linterp_linear_pure_implies Pure); try eassumption;
    cbn; intros; eauto.
  Qed.

  Lemma interp_linear_pure_ext_st
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U U' : Update Σ) P
        (EQ : ∀ m, U m = U' m),
        interp_linear_pure St U x P →
        interp_linear_pure St U' x P
    | Effectful => fun _ => True
    end l.
  Proof.
  pose proof (interp_atom_pure_ext_st Pure) as HINT. cbn in HINT.
  induction l; destruct eff; cbn; auto.
  - apply HINT.
  - intros. eapply HINT; eauto.
    eapply (interp_atom_pure_implies Pure); try eassumption.
    eauto.
  - intros. eapply HINT; eauto.
    eapply (interp_atom_pure_implies Pure); try eassumption.
    cbn. intros. destruct (Bits.single x');
    [eapply IHl1 | eapply IHl2]; eauto;
    eapply (interp_linear_pure_implies Pure); try eassumption;
    cbn; intros; eauto.
  Qed.

  Lemma linterp_linear_implies
  : ∀ E ty (l : linear _ E ty) (U : Update Σ) log P P'
      (IMPLY : ∀ x' U' log', P x' U' log' → P' x' U' log'),
      linterp_linear St l U log P →
      linterp_linear St l U log P'.
  Proof.
  pose proof (linterp_linear_pure_implies Pure) as HINT. cbn in HINT.
  pose proof (linterp_atom_pure_implies Pure) as HINT1. cbn in HINT1.
  induction l; cbn [linterp_linear].
  - intros. eapply linterp_atom_implies; eassumption.
  - destruct eff; intros;
    try (eapply HINT; try eassumption; cbn; intuition).
    eapply linterp_atom_implies; try eassumption. cbn.
    intros. eapply IHa2; try eassumption.
  - destruct eff; intros;
    try (eapply HINT; try eassumption; cbn; intuition).
    eapply HINT1; try eassumption. cbn.
    intros. destruct (Bits.single _);
    first [eapply IHl1 | eapply IHl2]; try eassumption; cbn;
    intros; eapply IHcont; try eassumption; intuition.
  Qed.

  Lemma interp_linear_implies
  : ∀ E ty (l : linear _ E ty) (U : Update Σ) P P'
      (IMPLY : ∀ x' U', P x' U' → P' x' U'),
      interp_linear St l U P →
      interp_linear St l U P'.
  Proof.
  pose proof (interp_linear_pure_implies Pure) as HINT. cbn in HINT.
  pose proof (interp_atom_pure_implies Pure) as HINT1. cbn in HINT1.
  induction l; cbn [interp_linear].
  - intros. eapply interp_atom_implies; eassumption.
  - destruct eff; intros;
    try (eapply HINT; try eassumption; cbn; intuition).
    eapply interp_atom_implies; try eassumption. cbn.
    intros. eapply IHa2; try eassumption.
  - destruct eff; intros;
    try (eapply HINT; try eassumption; cbn; intuition).
    eapply HINT1; try eassumption. cbn.
    intros. destruct (Bits.single _);
    first [eapply IHl1 | eapply IHl2]; try eassumption; cbn;
    intros; eapply IHcont; try eassumption; intuition.
  Qed.

  Lemma linterp_linear_ext
  : ∀ E ty (l : linear _ E ty) (U : Update Σ) log P P'
      (EQ : ∀ x' U' log', P x' U' log' ↔ P' x' U' log'),
      linterp_linear St l U log P ↔
      linterp_linear St l U log P'.
  Proof.
  pose proof (linterp_linear_implies) as HINT.
  destruct E;
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma interp_linear_ext
  : ∀ E ty (l : linear _ E ty) (U : Update Σ) P P'
      (EQ : ∀ x' U', P x' U' ↔ P' x' U'),
      interp_linear St l U P ↔
      interp_linear St l U P'.
  Proof.
  pose proof (interp_linear_implies) as HINT.
  destruct E;
  intuition; eapply HINT; try eassumption; intros; apply EQ; auto.
  Qed.

  Lemma linterp_linear_ext_st
  : ∀ E ty (l : linear _ E ty) (U U' : Update Σ) log P
      (EXTP : ∀ x U U' log, (∀ m, U m = U' m) → P x U log → P x U' log)
      (EQ : ∀ m, U m = U' m),
      linterp_linear St l U log P →
      linterp_linear St l U' log P.
  Proof.
  pose proof (linterp_linear_pure_ext_st Pure) as HINT. cbn in HINT.
  pose proof (linterp_atom_pure_ext_st Pure) as HINT1. cbn in HINT1.
  induction l; cbn [linterp_linear].
  - intros. eapply linterp_atom_ext_st; eauto.
  - destruct eff; intros.
    + eapply HINT; try eassumption.
      eapply (linterp_linear_pure_implies Pure); eauto.
      simpl. eauto.
    + eapply linterp_atom_ext_st; eauto.
  - destruct eff; intros.
    + eapply HINT; try eassumption.
      eapply (linterp_linear_pure_implies Pure); eauto.
      simpl. eauto.
    + eapply HINT1; try eassumption.
      eapply (linterp_atom_pure_implies Pure); try eassumption.
      simpl.
      intros. destruct (Bits.single _); eauto.
  Qed.

  Lemma interp_linear_ext_st
  : ∀ E ty (l : linear _ E ty) (U U' : Update Σ) P
      (EXTP : ∀ x U U', (∀ m, U m = U' m) → P x U → P x U')
      (EQ : ∀ m, U m = U' m),
      interp_linear St l U P →
      interp_linear St l U' P.
  Proof.
  pose proof (interp_linear_pure_ext_st Pure) as HINT. cbn in HINT.
  pose proof (interp_atom_pure_ext_st Pure) as HINT1. cbn in HINT1.
  induction l; cbn [interp_linear].
  - intros. eapply interp_atom_ext_st; eauto.
  - destruct eff; intros.
    + eapply HINT; try eassumption.
      eapply (interp_linear_pure_implies Pure); eauto.
      simpl. eauto.
    + eapply interp_atom_ext_st; eauto.
  - destruct eff; intros.
    + eapply HINT; try eassumption.
      eapply (interp_linear_pure_implies Pure); eauto.
      simpl. eauto.
    + eapply HINT1; try eassumption.
      eapply (interp_atom_pure_implies Pure); try eassumption.
      simpl.
      intros. destruct (Bits.single _); eauto.
  Qed.

  Lemma uncover_linterp_atom_pure
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P,
        let P' x' log' := P x' U log' in
        linterp_atom St x U log P =
        linterp_atom_pure St U x log P'
    | Effectful => fun _ => True
    end a.
  Proof. destruct a; auto; destruct eff; auto. Qed.

  Lemma uncover_interp_atom_pure
  : ∀ E ty (a : atom _ E ty),
    match E as h return atom Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P,
        let P' x' := P x' U in
        interp_atom St x U P =
        interp_atom_pure St U x P'
    | Effectful => fun _ => True
    end a.
  Proof. destruct a; auto; destruct eff; auto. Qed.

  Lemma uncover_linterp_linear_pure
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P,
        let P' x' log' := P x' U log' in
        linterp_linear St x U log P =
        linterp_linear_pure St U x log P'
    | Effectful => fun _ => True
    end l.
  Proof.
  destruct l; destruct eff; auto.
  apply (uncover_linterp_atom_pure Pure).
  Qed.

  Lemma uncover_interp_linear_pure
  : ∀ E ty (l : linear _ E ty),
    match E as h return linear Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P,
        let P' x' := P x' U in
        interp_linear St x U P =
        interp_linear_pure St U x P'
    | Effectful => fun _ => True
    end l.
  Proof.
  destruct l; destruct eff; auto.
  apply (uncover_interp_atom_pure Pure).
  Qed.

  Lemma uncover_linterp_pure
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) log P,
        let P' x' log' := P x' U log' in
        linterp St x U log P =
        linterp_pure St U x log P'
    | Effectful => fun _ => True
    end e.
  Proof. destruct e; auto; destruct eff; auto. Qed.

  Lemma uncover_interp_pure
  : ∀ E ty (e : t _ E ty),
    match E as h return t Bits.bits h ty → Prop with
    | Pure => fun x =>
      ∀ (U : Update Σ) P,
        let P' x' := P x' U in
        interp St x U P =
        interp_pure St U x P'
    | Effectful => fun _ => True
    end e.
  Proof. destruct e; auto; destruct eff; auto. Qed.
End facts.

