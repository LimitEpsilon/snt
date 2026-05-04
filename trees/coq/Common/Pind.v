From Stdlib Require Import Utf8.

Section pind.
  Context {State : Type}.

  (* The complete lattice we are working in: set of states *)
  Definition bot (st : State) := False.
  Definition top (st : State) := True.
  Definition meet (a b : State → Prop) st := a st ∧ b st.
  Definition join (a b : State → Prop) st := a st ∨ b st.
  Definition leq (a b : State → Prop) := ∀ st (LOW : a st), b st.
  Definition equiv (a b : State → Prop) := leq a b ∧ leq b a.
  Definition mon (f : (State → Prop) → (State → Prop)) :=
    ∀ a b (LE : leq a b), leq (f a) (f b)
  .

  Notation "⊥" := bot.
  Notation "⊤" := top.
  Infix "⊓" := meet (at level 40).
  Infix "⊔" := join (at level 50).
  Infix "⊑" := leq (at level 60).
  Infix "≡" := equiv (at level 60).

  (* preorder *)
  Lemma leq_refl a : a ⊑ a.
  Proof. repeat intro; auto. Qed.

  Lemma leq_trans a b c (LEa : a ⊑ b) (LEb : b ⊑ c) : a ⊑ c.
  Proof. repeat intro; auto. Qed.

  (* equivalence relation *)
  Lemma equiv_refl a : a ≡ a.
  Proof. split; apply leq_refl. Qed.

  Lemma equiv_trans a b c (EQa : a ≡ b) (EQb : b ≡ c) : a ≡ c.
  Proof. split; eapply leq_trans; first [eapply EQa | eapply EQb]. Qed.

  Lemma equiv_comm a b (EQ : a ≡ b) : b ≡ a.
  Proof. split; destruct EQ; auto. Qed.

  Lemma equiv_iff a b (EQ : a ≡ b) x : a x ↔ b x.
  Proof. destruct EQ; split; intros; auto. Qed.

  (* Boolean algebra *)
  Ltac prove_algebra :=
    try split;
    unfold join, meet, bot, top in *;
    repeat intro;
    simpl in *;
    repeat match goal with
    | H : _ ∧ _ |- _ => destruct H
    | H : _ ∨ _ |- _ => destruct H
    | H : False |- _ => destruct H
    end;
    auto.

  Lemma join_assoc a b c :
    a ⊔ (b ⊔ c) ≡ (a ⊔ b) ⊔ c.
  Proof. prove_algebra. Qed.

  Lemma meet_assoc a b c :
    a ⊓ (b ⊓ c) ≡ (a ⊓ b) ⊓ c.
  Proof. prove_algebra. Qed.

  Lemma join_comm a b :
    a ⊔ b ≡ b ⊔ a.
  Proof. prove_algebra. Qed.

  Lemma meet_comm a b :
    a ⊓ b ≡ b ⊓ a.
  Proof. prove_algebra. Qed.

  Lemma join_distrib a b c :
    a ⊔ (b ⊓ c) ≡ (a ⊔ b) ⊓ (a ⊔ c).
  Proof. prove_algebra. Qed.

  Lemma meet_distrib a b c :
    a ⊓ (b ⊔ c) ≡ (a ⊓ b) ⊔ (a ⊓ c).
  Proof. prove_algebra. Qed.

  Lemma join_ident a :
    a ⊔ ⊥ ≡ a.
  Proof. prove_algebra. Qed.

  Lemma meet_ident a :
    a ⊓ ⊤ ≡ a.
  Proof. prove_algebra. Qed.

  Lemma join_annih a :
    a ⊔ ⊤ ≡ ⊤.
  Proof. prove_algebra. Qed.

  Lemma meet_annih a :
    a ⊓ ⊥ ≡ ⊥.
  Proof. prove_algebra. Qed.

  Lemma join_idemp a :
    a ⊔ a ≡ a.
  Proof. prove_algebra. Qed.

  Lemma meet_idemp a :
    a ⊓ a ≡ a.
  Proof. prove_algebra. Qed.

  Lemma join_absorp a b :
    a ⊔ (a ⊓ b) ≡ a.
  Proof. prove_algebra. Qed.

  Lemma meet_absorp a b :
    a ⊓ (a ⊔ b) ≡ a.
  Proof. prove_algebra. Qed.

  Lemma mon_equiv a b
    (f : (State → Prop) → (State → Prop))
    (MON : mon f)
    (EQ : a ≡ b)
  : f a ≡ f b.
  Proof. split; destruct EQ; auto. Qed.

  Lemma join_leq a b x
    (LEa : a ⊑ x)
    (LEb : b ⊑ x)
  : a ⊔ b ⊑ x.
  Proof. prove_algebra. Qed.

  Lemma join_equiv a b a' b'
    (EQa : a ≡ a')
    (EQb : b ≡ b')
  : a ⊔ b ≡ a' ⊔ b'.
  Proof. destruct EQa, EQb; prove_algebra. Qed.

  Lemma meet_leq a b x
    (LEa : x ⊑ a)
    (LEb : x ⊑ b)
  : x ⊑ a ⊓ b.
  Proof. prove_algebra. Qed.

  Lemma meet_equiv a b a' b'
    (EQa : a ≡ a')
    (EQb : b ≡ b')
  : a ⊓ b ≡ a' ⊓ b'.
  Proof. destruct EQa, EQb; prove_algebra. Qed.

  Lemma leq_meet a b
  : a ⊑ b ↔ a ⊓ b ≡ a.
  Proof.
    split; intro; prove_algebra.
    destruct H as (A & B).
    apply B in LOW. apply LOW.
  Qed.

  Lemma leq_join a b
  : a ⊑ b ↔ a ⊔ b ≡ b.
  Proof.
    split; intro; prove_algebra.
    destruct H as (A & B).
    apply A. auto.
  Qed.

  Lemma leq_equiv a b a' b'
    (EQa : a ≡ a')
    (EQb : b ≡ b')
  : a ⊑ b ↔ a' ⊑ b'.
  Proof. split; repeat intro; destruct EQa, EQb; auto. Qed.

  (* Knaster-Tarski Fixpoint Theorem *)
  (* smallest prefixed point *)
  (* which is the induction principle *)
  Variant lfp f st : Prop :=
  | lfp_intro (LFP : ∀ x (PREFIX : f x ⊑ x), x st)
  .

  (* greatest postfixed point *)
  Variant gfp f st : Prop :=
  | gfp_intro x (POSTFIX : x ⊑ f x) (INx : x st)
  .

  (* parameterized least fixpoint *)
  Variant plfpF f plfp r (st : State) : Prop :=
  | plfp_intro
    (SIM : ∀ x (LE : r ⊓ plfp r ⊑ x), f x st : Prop)
  .

  Variant plfp f r st : Prop :=
  | plfp_observe
    (PLFP : ∀ X (PREFIX : ∀ r', plfpF f X r' ⊑ X r'), X r st)
  .

  (* parameterized greatest fixpoint *)
  Variant pgfpF f pgfp r (st : State) : Prop :=
  | pgfp_intro x
    (LE : x ⊑ r ⊔ pgfp r)
    (SIM : f x st : Prop)
  .

  Variant pgfp f r st : Prop :=
  | pgfp_observe X
    (POSTFIX : ∀ r', X r' ⊑ pgfpF f X r')
    (INX : X r st)
  .

  (* unfolded plfp *)
  Variant uplfp f r st : Prop :=
  | uplfp_intro (BASE : r st) (IND : plfp f r st)
  .

  (* unfolded pgfp *)
  Variant upgfp f r st : Prop :=
  | upgfp_base (BASE : r st)
  | upgfp_ind (IND : pgfp f r st)
  .

  Lemma plfpF_mon f plfp plfp' r
    (LEf : ∀ r', plfp r' ⊑ plfp' r')
  : plfpF f plfp r ⊑ plfpF f plfp' r.
  Proof.
    repeat intro; destruct LOW.
    econstructor; eauto.
    intros. apply SIM.
    eapply leq_trans; eauto.
    eapply meet_leq.
    - repeat intro; destruct LOW; auto.
    - repeat intro; destruct LOW. apply LEf. auto.
  Qed.

  Lemma plfp_as_lfp r
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : plfp f r ≡ lfp (fun y => f (r ⊓ y)).
  Proof.
    split; repeat intro; destruct LOW.
    - constructor. intros.
      specialize (PLFP (fun r st => ∀ x, f (r ⊓ x) ⊑ x → f (r ⊓ x) st)).
      simpl in PLFP.
      apply PREFIX. apply PLFP; auto.
      repeat intro. destruct LOW.
      eapply MON; try eapply SIM.
      instantiate (1 := r' ⊓ f (r' ⊓ _)).
      all: repeat intro; destruct LOW; split; eauto.
    - constructor. intros. apply LFP.
      repeat intro. eapply PREFIX.
      constructor. repeat intro.
      eapply MON; eauto.
  Qed.

  Lemma pgfpF_mon f pgfp pgfp' r
    (LE : ∀ r', pgfp r' ⊑ pgfp' r')
  : pgfpF f pgfp r ⊑ pgfpF f pgfp' r.
  Proof.
    repeat intro; destruct LOW.
    econstructor; eauto.
    eapply leq_trans; eauto.
    eapply join_leq.
    - repeat intro; left; auto.
    - repeat intro; right. eapply LE. eauto.
  Qed.

  Lemma pgfp_as_gfp r
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : pgfp f r ≡ gfp (fun y => f (r ⊔ y)).
  Proof.
    split; repeat intro; destruct LOW.
    - econstructor; eauto.
      repeat intro.
      destruct (POSTFIX _ _ LOW).
      eapply MON; eauto.
    - specialize (POSTFIX _ INx) as HINT.
      exists (fun r st => ∃ x, f (r ⊔ x) st ∧ x ⊑ f (r ⊔ x)); eauto.
      repeat intro. destruct LOW as (? & ? & LOW).
      econstructor; eauto.
      apply join_leq; repeat intro; [left | right]; eauto.
  Qed.

  Lemma lfp_prefix
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : f (lfp f) ⊑ lfp f.
  Proof.
    repeat intro. constructor. intros. apply PREFIX. eapply MON.
    instantiate (1 := lfp f). all:auto.
    intro st'. intro ST'. apply ST'; eauto.
  Qed.

  Lemma plfp_prefix f r
  : plfpF f (plfp f) r ⊑ plfp f r.
  Proof.
    repeat intro. constructor. intros. apply PREFIX. eapply plfpF_mon.
    instantiate (1 := plfp f). all:auto.
    clear LOW. repeat intro.
    destruct LOW. apply PLFP. auto.
  Qed.

  Lemma gfp_postfix
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : gfp f ⊑ f (gfp f).
  Proof.
    repeat intro. destruct LOW.
    eapply MON. instantiate (1 := x). all:auto.
    repeat intro. exists x; auto.
  Qed.

  Lemma pgfp_postfix f r
  : pgfp f r ⊑ pgfpF f (pgfp f) r.
  Proof.
    repeat intro. destruct LOW.
    eapply pgfpF_mon. instantiate (1 := X).
    - repeat intro. exists X; auto.
    - eapply POSTFIX. auto.
  Qed.

  Lemma lfp_postfix
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : lfp f ⊑ f (lfp f).
  Proof.
    repeat intro. destruct LOW. specialize (LFP (f (lfp f))).
    auto using lfp_prefix.
  Qed.

  Lemma plfp_postfix f r
  : plfp f r ⊑ plfpF f (plfp f) r.
  Proof.
    repeat intro. destruct LOW. apply PLFP.
    repeat intro. eapply plfpF_mon; eauto.
    auto using plfp_prefix.
  Qed.

  Lemma gfp_prefix
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : f (gfp f) ⊑ gfp f.
  Proof.
    repeat intro. exists (f (gfp f)); auto.
    repeat intro. eapply MON; eauto.
    apply gfp_postfix; auto.
  Qed.

  Lemma pgfp_prefix f r
  : pgfpF f (pgfp f) r ⊑ pgfp f r.
  Proof.
    repeat intro. exists (pgfpF f (pgfp f)); auto.
    repeat intro. eapply pgfpF_mon; eauto.
    apply pgfp_postfix.
  Qed.

  Lemma lfp_fix
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : lfp f ≡ f (lfp f).
  Proof. split; auto using lfp_prefix, lfp_postfix. Qed.

  Lemma plfp_fix f r
  : plfp f r ≡ plfpF f (plfp f) r.
  Proof. split; auto using plfp_prefix, plfp_postfix. Qed.

  Lemma gfp_fix
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : gfp f ≡ f (gfp f).
  Proof. split; auto using gfp_prefix, gfp_postfix. Qed.

  Lemma pgfp_fix f r
  : pgfp f r ≡ pgfpF f (pgfp f) r.
  Proof. split; auto using pgfp_prefix, pgfp_postfix. Qed.

  Lemma plfp_init
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : lfp f ≡ plfp f ⊤.
  Proof.
    eapply equiv_trans; [|apply equiv_comm; eapply plfp_as_lfp; auto].
    split; repeat intro.
    - destruct LOW.
      constructor. intros. apply LFP.
      repeat intro. apply PREFIX.
      eapply MON; eauto. repeat intro.
      cbv. auto.
    - destruct LOW.
      constructor. intros. apply LFP.
      repeat intro. apply PREFIX.
      eapply MON; try apply LOW.
      clear LOW. repeat intro.
      apply LOW.
  Qed.

  Lemma pgfp_init
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : gfp f ≡ pgfp f ⊥.
  Proof.
    eapply equiv_trans; [|apply equiv_comm; eapply pgfp_as_gfp; auto].
    split; repeat intro.
    - destruct LOW.
      exists x; auto.
      eapply leq_trans; eauto.
      eapply MON; eauto.
      repeat intro. right; auto.
    - destruct LOW.
      exists x; auto.
      eapply leq_trans; eauto.
      eapply MON; eauto.
      repeat intro. destruct LOW; eauto.
      contradiction.
  Qed.

  Lemma plfp_mon_gen f f' r r'
    (LEf : ∀ x, f x ⊑ f' x)
    (LEr : r ⊑ r')
  : plfp f r ⊑ plfp f' r'.
  Proof.
    repeat intro. destruct LOW.
    specialize (PLFP (fun r st => ∀ (LEr' : r ⊑ r'), plfp f' r' st)).
    simpl in PLFP. apply PLFP; auto.
    repeat intro. destruct LOW.
    apply plfp_prefix. constructor.
    intros. apply LEf. apply SIM.
    repeat intro. apply LE. destruct LOW; split; auto.
  Qed.

  Lemma pgfp_mon_gen f f' r r'
    (LEf : ∀ x, f x ⊑ f' x)
    (LEr : r ⊑ r')
  : pgfp f r ⊑ pgfp f' r'.
  Proof.
    repeat intro.
    exists (fun r' st => r ⊑ r' ∧ ∃ x, f' x st ∧ x ⊑ r' ⊔ pgfp f r).
    - clear LOW. repeat intro.
      destruct LOW as (LEr' & r'' & LOW & LEr'').
      econstructor; eauto. clear LOW.
      repeat intro.
      apply LEr'' in LOW.
      destruct LOW as [LOW | LOW].
      + left; auto.
      + right. apply pgfp_postfix in LOW.
        destruct LOW. split; auto.
        exists x.
        split; [apply LEf; auto|].
        repeat intro. apply LE in LOW. destruct LOW.
        { left. apply LEr'; auto. }
        { right. auto. }
    - split; auto.
      apply pgfp_postfix in LOW.
      destruct LOW.
      exists x.
      split; [apply LEf; auto|].
      repeat intro. apply LE in LOW. destruct LOW.
      { left. apply LEr. auto. }
      { right. auto. }
  Qed.

  Lemma plfp_mon
    (f : (State → Prop) → State → Prop)
  : mon (plfp f).
  Proof. repeat intro. eapply plfp_mon_gen; eauto using leq_refl. Qed.

  Lemma pgfp_mon
    (f : (State → Prop) → State → Prop)
  : mon (pgfp f).
  Proof. repeat intro. eapply pgfp_mon_gen; eauto using leq_refl. Qed.

  Lemma plfp_mult_strong f r
  : plfp f r ⊑ plfp f (uplfp f r).
  Proof.
    repeat intro. destruct LOW. apply PLFP.
    repeat intro. destruct LOW.
    apply plfp_prefix. constructor. intros.
    apply SIM. repeat intro.
    apply LE. destruct LOW as (? & LOW).
    split; auto. split; auto.
    eapply plfp_mon; eauto.
    clear LOW. repeat intro. destruct LOW. auto.
  Qed.

  Lemma pgfp_mult_strong f r
  : pgfp f (upgfp f r) ⊑ pgfp f r.
  Proof.
    repeat intro.
    exists (fun r' st => pgfp f (upgfp f r') st); auto.
    clear st LOW. repeat intro.
    apply pgfp_postfix in LOW. destruct LOW.
    econstructor; eauto.
    repeat intro. apply LE in LOW.
    destruct LOW as [LOW | LOW].
    - destruct LOW as [LOW | LOW]; [left; auto|].
      right. eapply pgfp_mon; eauto.
      repeat intro. left; auto.
    - right. auto.
  Qed.

  Lemma plfp_fold r
    (f : (State → Prop) → State → Prop)
  : plfp f r ⊑ f (uplfp f r).
  Proof.
    repeat intro.
    eapply plfp_postfix in LOW.
    destruct LOW. apply SIM.
    repeat intro; destruct LOW; split; auto.
  Qed.

  Lemma pgfp_fold r
    (f : (State → Prop) → State → Prop)
  : f (upgfp f r) ⊑ pgfp f r.
  Proof.
    repeat intro.
    eapply pgfp_prefix.
    econstructor; eauto. clear LOW.
    repeat intro; destruct LOW; [left | right]; auto.
  Qed.

  Lemma plfp_unfold r
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : f (uplfp f r) ⊑ plfp f r.
  Proof.
    repeat intro.
    eapply plfp_prefix.
    constructor. intros.
    eapply MON; try apply LOW. clear LOW.
    repeat intro. apply LE. destruct LOW; split; auto.
  Qed.

  Lemma pgfp_unfold r
    (f : (State → Prop) → State → Prop)
    (MON : mon f)
  : pgfp f r ⊑ f (upgfp f r).
  Proof.
    repeat intro.
    apply pgfp_postfix in LOW.
    destruct LOW.
    eapply MON; eauto.
    repeat intro. apply LE in LOW.
    destruct LOW; [left | right]; auto.
  Qed.

  Lemma plfp_acc f l r
    (OBG : ∀ φ (LEφ : φ ⊑ r) (IH : φ ⊑ l), plfp f φ ⊑ l)
  : plfp f r ⊑ l.
  Proof.
    repeat intro. apply OBG with (φ := r ⊓ l).
    1, 2: prove_algebra.
    destruct LOW.
    specialize (PLFP (fun r' st => ∀ (LEr : r' ⊑ r), plfp f (r' ⊓ l) st)).
    apply PLFP; auto using leq_refl.
    repeat intro. destruct LOW. apply plfp_prefix.
    constructor. intros. apply SIM.
    repeat intro. apply LE. destruct LOW.
    split; auto. split; auto.
    eapply OBG. instantiate (1 := r' ⊓ l).
    all:auto; repeat intro; destruct LOW; auto.
  Qed.

  Lemma pgfp_acc f l r
    (OBG : ∀ φ (LEφ : r ⊑ φ) (IH : l ⊑ φ), l ⊑ pgfp f φ)
  : l ⊑ pgfp f r.
  Proof.
    repeat intro.
    assert (SIM : pgfp f (r ⊔ l) st).
    { apply OBG; auto; prove_algebra. }
    exists (fun r' st => r ⊑ r' ∧ pgfp f (r' ⊔ l) st);
    eauto using leq_refl.
    clear st LOW SIM.
    repeat intro.
    destruct LOW as (LEr & LOW).
    apply pgfp_postfix in LOW. destruct LOW.
    econstructor; eauto.
    repeat intro.
    apply LE in LOW.
    destruct LOW as [LOW | LOW].
    - destruct LOW; [left; auto|].
      right. split; auto. apply OBG; eauto.
      { repeat intro. left; auto. }
      { repeat intro. right; auto. }
    - right. split; auto.
  Qed.
End pind.

Notation "⊥" := bot.
Notation "⊤" := top.
Infix "⊓" := meet (at level 40).
Infix "⊔" := join (at level 50).
Infix "⊑" := leq (at level 60).
Infix "≡" := equiv (at level 60).

Module Reach.
  Inductive t {State} (Next : State → State → Prop) (Init : State → Prop)
  : State → Prop :=
  | init st (INIT : Init st)
  : t Next Init st
  | next st st' (REACH : t Next Init st) (NEXT : Next st st')
  : t Next Init st'
  .
End Reach.

Create HintDb pind.

Section safety.
  Context {State : Type} (Next : State → State → Prop).

  (* set of states that can be reached from Init in 0 or more steps *)
  Variant reachF (Init : State → Prop) (reach : State → Prop) (st' : State) : Prop :=
  | initF (INIT : Init st')
  | nextF st (REACH : reach st) (NEXT : Next st st')
  .

  (* set of states such that every state reachable in 0 or more steps are in Final *)
  Variant reachB (Final : State → Prop) (reach : State → Prop) (st : State) : Prop :=
  | prevF
    (FINAL : Final st) (* in 0 steps *)
    (REACH : ∀ st' (PREV : Next st st'), reach st')
  .

  Lemma reachF_mon (Init : State → Prop) : mon (reachF Init).
  Proof.
    repeat intro. destruct LOW.
    - econstructor 1; eauto.
    - econstructor 2; eauto.
  Qed.

  #[local] Hint Resolve reachF_mon : core.

  Lemma reachB_mon (Final : State → Prop) : mon (reachB Final).
  Proof.
    repeat intro. destruct LOW.
    - econstructor 1; eauto.
  Qed.

  #[local] Hint Resolve reachB_mon : core.

  Lemma reach_lfp (Init : State → Prop) st :
    Reach.t Next Init st ↔ lfp (reachF Init) st.
  Proof.
    split; intro R.
    - induction R; constructor; repeat intro; apply PREFIX.
      econstructor 1; auto. destruct IHR.
      specialize (LFP x PREFIX).
      econstructor 2; eauto.
    - apply R with (x := Reach.t Next Init).
      repeat intro. destruct LOW.
      econstructor 1; auto.
      econstructor 2; eauto.
  Qed.

  Lemma forward_backward
    (Init : State → Prop)
    (Final : State → Prop)
  : lfp (reachF Init) ⊑ Final ↔ Init ⊑ gfp (reachB Final).
  Proof.
    split; intro R.
    - repeat intro.
      exists (lfp (reachF Init)).
      + clear st LOW.
        repeat intro.
        split. auto.
        clear R.
        intros.
        apply lfp_fix; auto.
        econstructor 2; eauto.
      + apply lfp_fix; auto.
        econstructor 1; auto.
    - eapply leq_trans.
      instantiate (1 := gfp (reachB Final)).
      + repeat intro. destruct LOW.
        apply (LFP (gfp (reachB Final))).
        repeat intro.
        destruct LOW. auto.
        apply gfp_fix in REACH; auto.
        destruct REACH; auto.
      + repeat intro.
        apply gfp_fix in LOW; auto.
        destruct LOW; auto.
  Qed.
End safety.

Hint Resolve reachF_mon : pind.
Hint Resolve reachB_mon : pind.

