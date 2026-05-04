(*! Utilities | Environments used to track variable bindings !*)
Require Import Common.
Require Export Member.

Section Contexts.
  Context {K: Type}.
  Context {V: K -> Type}.

  Inductive context : forall (sig: list K), Type :=
  | CtxEmpty: context []
  | CtxCons {sig} (k: K) (v: V k) (ctx: context sig): context (k :: sig).

  Context {V': K -> list K -> Type}.

  Definition cdestruct {sig} (ctx: context sig)
    : match sig return context sig -> Type with
      | [] => fun ctx => ctx = CtxEmpty
      | k :: sig => fun ctx => { vs: V k * context sig | ctx = CtxCons k (fst vs) (snd vs) }
      end ctx.
  Proof.
    destruct ctx.
    - reflexivity.
    - exists (v, ctx); reflexivity.
  Defined.

  Definition chd {k sig} (ctx: context (k :: sig)) : V k :=
    match ctx in (context sig')
          return match sig' with [] => unit | k :: _ => V k end with
    | CtxEmpty => tt
    | CtxCons _ v _ => v
    end.

  Definition ctl {k sig} (ctx: context (k :: sig)) : context sig :=
    match ctx in (context sig')
          return match sig' with [] => unit | _ :: sig => context sig end with
    | CtxEmpty => tt
    | CtxCons _ _ ctx' => ctx'
    end.

  Lemma ceqn {sig} (ctx: context sig)
    : match sig with
      | [] => fun ctx => ctx = CtxEmpty
      | k :: sig => fun ctx => ctx = CtxCons k (chd ctx) (ctl ctx)
      end ctx.
  Proof. destruct ctx; reflexivity. Defined.

  #[export] Instance EqDecContext `{EqDec K, !forall k, EqDec (V k)} l : EqDec (context l).
  Proof. refine {| eq_dec := _ |}.
    revert l.
    refine (fix go l {struct l} :=
      match l with
      | [] => fun ctx ctx' => left _
      | hd :: tl => fun ctx ctx' => _
      end).
    - rewrite (ceqn ctx), (ceqn ctx'). reflexivity.
    - rewrite (ceqn ctx), (ceqn ctx').
      refine match eq_dec (chd ctx) (chd ctx') with
      | left EQ =>
        match go tl (ctl ctx) (ctl ctx') with
        | left EQ' => left _
        | right NEQ => right _
        end
      | right NEQ => right _
      end.
      + congruence.
      + abstract (intro CONTRA; apply NEQ; inversion CONTRA;
                  eapply inj_pair2; assumption).
      + abstract (intro CONTRA; apply NEQ; inversion CONTRA;
                  eapply inj_pair2; assumption).
  Defined.

  Fixpoint ctx_to_list {l} : context l -> list {k : K & V k} :=
    match l with
    | [] => fun _ => []
    | hd :: tl => fun ctx => (existT _ hd (chd ctx)) :: ctx_to_list (ctl ctx)
    end.

  Fixpoint list_to_ctx (l : list {k : K & V k}) : context (map (projT1 (P:=V)) l) :=
    match l as l' return context (map (projT1 (P:=V)) l') with
    | [] => CtxEmpty
    | hd :: tl => CtxCons _ (projT2 hd) (list_to_ctx tl)
    end.

  Definition list_to_ctx_cast {l} :
    forall (ctx : context l), map (projT1 (P:=V)) (ctx_to_list ctx) = l.
  Proof.
    revert l.
    refine (fix go l {struct l} :=
    match l with
    | [] => fun ctx => eq_refl
    | hd :: tl => fun ctx => _
    end).
    cbn [map ctx_to_list].
    f_equal.
    simple apply go.
  Defined.

  Lemma list_to_ctx_to_list l (ctx : context l) :
    (rew [context] (list_to_ctx_cast ctx) in list_to_ctx (ctx_to_list ctx)) = ctx.
  Proof.
    induction ctx; simpl; auto.
    revert IHctx.
    generalize (list_to_ctx_cast ctx).
    generalize (ctx_to_list ctx). destruct e.
    simpl. intros. f_equal. auto.
  Qed.

  Lemma ctx_to_list_to_ctx l :
    ctx_to_list (list_to_ctx l) = l.
  Proof.
    induction l; simpl; auto.
    f_equal; destruct a; auto.
  Qed.

  Section Const.
    Context (f: forall k, V k).

    Fixpoint cconst (sig: list K)  : context sig :=
      match sig as sig' return context sig' with
      | nil => CtxEmpty
      | cons h t => CtxCons h (f h) (cconst t)
      end.
  End Const.

  Fixpoint ccreate (sig: list K) (f: forall k, member k sig -> V k) : context sig :=
    match sig return (forall k, member k sig -> V k) -> context sig with
    | nil => fun _ => CtxEmpty
    | cons h t => fun f => CtxCons h (f h (MemberHd h t))
                               (ccreate t (fun k m => f k (MemberTl k h t m)))
    end f.

  Fixpoint cassoc {sig} {k} (m: member k sig)
           (ctx: context sig) {struct m} : V k :=
    match m in (member y l) return (context l -> V y) with
    | MemberHd k sig => fun ctx => chd ctx
    | MemberTl k k' sig m => fun ctx => cassoc m (ctl ctx)
    end ctx.

  Lemma cassoc_cconst {sig} (f: forall k, V k) {k} (m: member k sig) :
    cassoc m (cconst f sig) = f k.
  Proof.
    induction sig; cbn.
    inversion m.
    pose proof (mdestruct m) as [(eqn & Heq) | (m' & Heq)].
    + destruct eqn; cbn in *; rewrite Heq.
      reflexivity.
    + rewrite Heq; cbn.
      apply IHsig.
  Qed.

  Lemma cassoc_ccreate {sig} (f: forall k, _ -> V k) {k} (m: member k sig) :
    cassoc m (ccreate sig f) = f k m.
  Proof.
    induction sig; cbn.
    - pose proof (mdestruct m) as Hd; elim Hd.
    - pose proof (mdestruct m) as [(eqn & Heq) | (m' & Heq)].
      + destruct eqn; cbn in *; rewrite Heq.
        reflexivity.
      + rewrite Heq; cbn.
        apply IHsig.
  Qed.

  Lemma ccreate_funext {sig} (f1 f2: forall k, _ -> V k):
    (forall k m, f1 k m = f2 k m) ->
    ccreate sig f1 = ccreate sig f2.
  Proof.
    induction sig; cbn.
    - intros; reflexivity.
    - intros Heq; rewrite Heq; eauto using f_equal.
  Qed.

  Lemma ccreate_cassoc {sig} (ctx: context sig):
    ccreate sig (fun k m => cassoc m ctx) = ctx.
  Proof.
    induction sig; cbn; intros.
    - rewrite (ceqn ctx).
      reflexivity.
    - rewrite (ceqn ctx); cbn.
      rewrite IHsig; reflexivity.
  Qed.

  Fixpoint creplace {sig} {k} (m: member k sig) (v: V k)
           (ctx: context sig) {struct m} : context sig.
  Proof.
    destruct m.
    - eapply (CtxCons k v (ctl ctx)).
    - eapply (CtxCons k' (chd ctx) (creplace sig k m v (ctl ctx))).
  Defined.

  Lemma cassoc_creplace_eq {sig} :
    forall (ctx: context sig) {k} (m: member k sig) (v: V k),
      cassoc m (creplace m v ctx) = v.
  Proof.
    induction m; cbn; intros.
    - reflexivity.
    - rewrite IHm; reflexivity.
  Qed.

  Lemma cassoc_creplace_neq_idx {sig} :
    forall (ctx: context sig) {k k'} (m: member k sig) (m': member k' sig) (v: V k),
      member_idx m <> member_idx m' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    induction m; cbn; intros; rewrite (ceqn ctx).
    - destruct (mdestruct m') as [ (-> & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn in *.
      + congruence.
      + reflexivity.
    - destruct (mdestruct m') as [ (-> & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn in *.
      + reflexivity.
      + rewrite IHm; eauto.
  Qed.

  Lemma cassoc_creplace_neq_k {sig} :
    forall (ctx: context sig) {k k'} (m: member k sig) (m': member k' sig) (v: V k),
      k <> k' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    eauto using cassoc_creplace_neq_idx, member_idx_inj_k_contra.
  Qed.

  Global Instance EqDec_member sig (k: K) {EQ: EqDec K} : EqDec (member k sig).
  Proof.
    econstructor.
    induction sig; intros m1 m2.
    - destruct (mdestruct m1).
    - destruct (mdestruct m1) as [(-> & Heq) | (m1' & Heq)]; subst; cbn in *; subst; cbn;
        destruct (mdestruct m2) as [(eqn & Heq) | (m2' & Heq)];
        try (rewrite <- Eqdep_dec.eq_rect_eq_dec in Heq by apply eq_dec);
        unfold eq_type in *; subst; cbn in *; subst.
      + left; reflexivity.
      + right; intro; discriminate.
      + right; intro; discriminate.
      + destruct (IHsig m1' m2'); subst.
        * left; reflexivity.
        * right; intro; inversion H as [H'].
          apply Eqdep_dec.inj_pair2_eq_dec in H'; try apply eq_dec.
          apply Eqdep_dec.inj_pair2_eq_dec in H'; try apply eq_dec.
          eauto.
  Defined.

  Lemma cassoc_creplace_neq_members {sig} {EQ:EqDec K} :
    forall (ctx: context sig) {k } (m: member k sig) (m': member k sig) (v: V k),
      m <> m' ->
      cassoc m' (creplace m v ctx) = cassoc m' ctx.
  Proof.
    induction m; cbn; intros; rewrite (ceqn ctx).
    -
      destruct (mdestruct m') as [ (eqn & Heq) | (m'' & Heq)]; rewrite Heq in *.
      + rewrite <- Eqdep_dec.eq_rect_eq_dec in H by apply eq_dec.
        congruence.
      + reflexivity.
    -
      destruct (mdestruct m') as [ (eqn & Heq) | (m'' & Heq)]; subst; cbn in *; subst; cbn.
      + rewrite Heq in *. destruct eqn. reflexivity.
      + rewrite IHm; intuition congruence.
  Qed.

  Fixpoint capp {sig sig'} (ctx: context sig) (ctx': context sig'): context (sig ++ sig') :=
    match sig return context sig -> context (sig ++ sig') with
    | [] => fun _ => ctx'
    | k :: sig => fun ctx => CtxCons k (chd ctx) (capp (ctl ctx) ctx')
    end ctx.

  Context (V_app : forall k ls ls', V' k ls -> V' k (ls ++ ls')).

  Fixpoint capp_nil_r {A} (l: list A) {struct l}:
    l ++ [] = l.
  Proof. destruct l; cbn; [ | f_equal ]; eauto. Defined.

  Lemma capp_empty:
    forall {sig} (ctx: context sig),
      capp ctx CtxEmpty =
      rew <- capp_nil_r sig in ctx.
  Proof.
    induction ctx; cbn.
    - reflexivity.
    - rewrite IHctx.
      rewrite eq_trans_refl_l.
      unfold eq_rect_r.
      rewrite eq_sym_map_distr.
      rewrite <- rew_map.
      destruct (eq_sym _); reflexivity.
  Qed.

  Fixpoint csplit {sig sig'} (ctx: context (sig ++ sig')): (context sig * context sig') :=
    match sig return context (sig ++ sig') -> (context sig * context sig') with
    | [] => fun ctx => (CtxEmpty, ctx)
    | k :: sig => fun ctx =>
                  let split := csplit (ctl ctx) in
                  (CtxCons k (chd ctx) (fst split), (snd split))
    end ctx.

  Lemma csplit_capp :
    forall {sig sig'} (ctx: context sig) (ctx': context sig'),
      csplit (capp ctx ctx') = (ctx, ctx').
  Proof.
    induction sig; cbn; intros; rewrite (ceqn ctx).
    - reflexivity.
    - rewrite IHsig; reflexivity.
  Qed.

  Lemma capp_csplit :
    forall {sig sig'} (ctx : context (sig ++ sig')),
      ctx = capp (fst (csplit ctx)) (snd (csplit ctx)).
  Proof.
    induction sig; simpl; eauto; intros.
    rewrite (ceqn ctx) at 1. f_equal; auto.
  Qed.

  Definition infix_context {infix} (ctx': context infix)
             {sig sig'} (ctx: context (sig ++ sig')) :=
    capp (fst (csplit ctx)) (capp ctx' (snd (csplit ctx))).

  Lemma cassoc_mprefix:
    forall {k prefix sig} (m: member k sig)
      (ctx: context sig) (ctx': context prefix),
      cassoc (mprefix prefix m) (capp ctx' ctx) = cassoc m ctx.
  Proof. induction prefix; cbn; eauto. Qed.

  Lemma cassoc_minfix:
    forall {k sig sig'} (m: member k (sig ++ sig')) {infix}
      (ctx: context (sig ++ sig')) (ctx': context infix),
      cassoc (minfix infix m) (infix_context ctx' ctx) = cassoc m ctx.
  Proof.
    induction sig; cbn; intros.
    - apply cassoc_mprefix.
    - destruct (mdestruct m) as [(eqn & Heq) | (m' & Heq)];
        [ destruct eqn | ]; cbn in *; subst; rewrite (ceqn ctx).
      + reflexivity.
      + setoid_rewrite IHsig; reflexivity.
  Qed.

  Lemma creplace_mprefix:
    forall {k prefix sig} (m: member k sig)
      (ctx: context sig) (ctx': context prefix)
      (v : V k),
    creplace (mprefix prefix m) v (capp ctx' ctx) =
    capp ctx' (creplace m v ctx).
  Proof. induction prefix; cbn; eauto using f_equal. Qed.

  Lemma creplace_minfix:
    forall {k sig sig'} (m: member k (sig ++ sig')) {infix}
      (ctx: context (sig ++ sig')) (ctx': context infix) v,
      creplace (minfix infix m) v (infix_context ctx' ctx) =
      (infix_context ctx' (creplace m v ctx)).
  Proof.
    induction sig; cbn; intros.
    - apply creplace_mprefix.
    - destruct (mdestruct m) as [(eqn & Heq) | (m' & Heq)];
        [ destruct eqn | ]; cbn in *; subst; rewrite (ceqn ctx).
      + reflexivity.
      + setoid_rewrite IHsig; reflexivity.
  Qed.

  Lemma capp_as_infix':
    forall {sig sig'} (ctx: context sig) (ctx': context sig'),
      (rew <- [fun sig' => context (sig ++ sig')] capp_nil_r sig' in capp ctx ctx') =
      infix_context ctx' (rew <- capp_nil_r sig in ctx).
  Proof.
    unfold infix_context; intros.
    rewrite <- capp_empty.
    rewrite !csplit_capp; cbn.
    rewrite capp_empty.
    unfold eq_rect_r; cbn.
    destruct (eq_sym _); reflexivity.
  Qed.

  Lemma capp_as_infix:
    forall {sig sig'} (ctx: context sig) (ctx': context sig'),
      capp ctx ctx' =
      (rew [fun sig' => context (sig ++ sig')] capp_nil_r sig' in
          infix_context ctx' (rew <- capp_nil_r sig in ctx)).
  Proof.
    intros; rewrite <- capp_as_infix', rew_opp_r; reflexivity.
  Qed.
End Contexts.

Arguments context {K} V sig : assert.

Section Maps.
  Context {K K': Type}.
  Context {V: K -> Type} {V': K' -> Type}.
  Context (fK: K -> K').
  Context (fV: forall k, V k -> V' (fK k)).

  Fixpoint cmap {sig} (ctx: context V sig) {struct ctx} : context V' (List.map fK sig) :=
    match ctx in context _ sig return context V' (List.map fK sig) with
    | CtxEmpty => CtxEmpty
    | CtxCons k v ctx => CtxCons (fK k) (fV k v) (cmap ctx)
    end.

  Lemma cmap_creplace :
    forall {sig} (ctx: context V sig) {k} (m: member k sig) v,
      cmap (creplace m v ctx) =
      creplace (member_map fK m) (fV k v) (cmap ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Lemma cmap_cassoc :
    forall {sig} (ctx: context V sig) {k} (m: member k sig),
      cassoc (member_map fK m) (cmap ctx) =
      fV k (cassoc m ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Lemma cmap_ctl :
    forall {k sig} (ctx: context V (k :: sig)),
      cmap (ctl ctx) = ctl (cmap ctx).
  Proof.
    intros; rewrite (ceqn ctx); reflexivity.
  Qed.

  Lemma cmap_map : forall [l],
    context V' (List.map fK l) ->
    context (fun x => V' (fK x)) l.
  Proof.
    induction l.
    intro. econstructor.
    inversion 1.
    constructor. apply v.
    apply IHl. apply ctx.
  Defined.

End Maps.

Section ValueMaps.
  Context {K: Type}.
  Context {V: K -> Type} {V': K -> Type}.
  Context (fV: forall k, V k -> V' k).

  Fixpoint cmapv {sig} (ctx: context V sig) {struct ctx} : context V' sig :=
    match ctx in context _ sig return context V' sig with
    | CtxEmpty => CtxEmpty
    | CtxCons k v ctx => CtxCons k (fV k v) (cmapv ctx)
    end.

  Lemma cmapv_creplace :
    forall {sig} (ctx: context V sig) {k} (m: member k sig) v,
      cmapv (creplace m v ctx) =
      creplace m (fV k v) (cmapv ctx).
  Proof.
    induction ctx; cbn; intros.
    - destruct (mdestruct m).
    - destruct (mdestruct m) as [(-> & ->) | (? & ->)]; cbn in *.
      + reflexivity.
      + rewrite IHctx; reflexivity.
  Qed.

  Fixpoint cmapv_cassoc {sig} (ctx: context V sig) {struct ctx}:
    forall {k} (m: member k sig),
      cassoc m (cmapv ctx) = fV k (cassoc m ctx).
  Proof.
    refine (
      match ctx as ctx' in context _ sig
      return
        forall (k : K) (m: member k sig),
          cassoc m (cmapv ctx') = fV k (cassoc m ctx')
      with
      | CtxEmpty => fun _ m => False_rect _ (member_nil m)
      | CtxCons hd chd ctl => fun k m => _
      end
    ).
    cbn.
    refine (
      match m as m' in member k' l
      return
        match l as l' return member k' l' -> Type with
        | [] => fun _ => unit
        | k'' :: tl => fun m'' =>
          forall v c,
            (forall m''', cassoc m''' (cmapv c) = fV k' (cassoc m''' c)) ->
            cassoc m'' (CtxCons k'' (fV k'' v) (cmapv c)) =
            fV k' (cassoc m'' (CtxCons k'' v c))
        end m'
      with
      | MemberHd _ _ => fun v c _ => eq_refl
      | MemberTl _ _ _ m => fun v c IH => IH _
      end chd ctl (cmapv_cassoc _ _ _)
    ).
  Defined.

  Lemma cmapv_ctl :
    forall {k sig} (ctx: context V (k :: sig)),
      cmapv (ctl ctx) = ctl (cmapv ctx).
  Proof.
    intros; rewrite (ceqn ctx); reflexivity.
  Qed.
End ValueMaps.

Section Folds.
  Context {K: Type}.
  Context {V: K -> Type}.

  Section foldl.
    Context {T: Type}.
    Context (f: forall (k: K) (v: V k) (acc: T), T).

    Fixpoint cfoldl {sig} (ctx: context V sig) (init: T) :=
      match ctx with
      | CtxEmpty => init
      | CtxCons k v ctx => cfoldl ctx (f k v init)
      end.

    Definition cfoldl' {sig} (ctx: context V sig) (init: T) :=
      match sig return context V sig -> T with
      | [] => fun _ => init
      | k :: sig => fun ctx => cfoldl (ctl ctx) (f k (chd ctx) init)
      end ctx.

  End foldl.

  Section foldl.
    Context {T: Type}.
    Context (F: forall (k: K) (v: V k) (acc: T), T -> Prop).

    Inductive CFoldL : forall {sig}, context V sig -> T -> T -> Prop :=
    | CFoldL_nil : forall init,  CFoldL CtxEmpty init init
    | CFoldL_cons :
      forall sig k v init final t ctx,
      F k v init t ->
      CFoldL ctx t final ->
      CFoldL (CtxCons (sig:=sig) k v ctx) init final.
  End foldl.

  Section foldl.
    Context {T: Type}.
    Context (f: forall (k: K) (v: V k) (acc: T), T).
    Context (F: forall (k: K) (v: V k) (acc: T), T -> Prop).
    Context {H: forall (k: K) (v: V k) (acc t: T), f k v acc = t <-> F k v acc t}.

    Local Hint Constructors CFoldL : core.

    Lemma cfoldl_CFoldL : forall sig (ctx: context V sig) init t,
      cfoldl f ctx init = t -> CFoldL F ctx init t.
    Proof.
      induction ctx; cbn; intros; subst; eauto.
      econstructor 2. eapply H; eauto. eauto.
    Qed.

    Lemma CFoldL_cfoldl : forall sig (ctx: context V sig) init t,
      CFoldL F ctx init t -> cfoldl f ctx init = t.
    Proof.
      induction 1; cbn; intros; subst; eauto.
      f_equal. eapply H. eauto.
    Qed.
  End foldl.

  Section foldr.
    Context {T: list K -> Type}.
    Context (f: forall (sg: list K) (k: K) (v: V k), T sg -> T (k :: sg)).

    Fixpoint cfoldr {sig} (ctx: context V sig) (init: T []) :=
      match ctx with
      | CtxEmpty => init
      | CtxCons k v ctx => f _ k v (cfoldr ctx init)
      end.

    Fixpoint cfoldr' {sig} (ctx: context V sig) (init: T []) :=
      match sig return context V sig -> T sig with
      | [] => fun _ => init
      | k :: sig => fun ctx => f sig k (chd ctx) (cfoldr' (ctl ctx) init)
      end ctx.
  End foldr.
End Folds.


Section Forall.
  Context {K: Type}.
  Context {V: K -> Type}.

  Section ForallT.

    Inductive CForallT (P : forall (k : K), (V k) -> Type) : forall [ls], context V ls -> Type :=
    | CForallT_nil : CForallT P CtxEmpty
    | CForallT_cons : forall [sig] k v (ctx : context _ sig),
      P k v -> CForallT P ctx -> CForallT P (CtxCons k v ctx).

    Global Arguments CForallT_cons [P]%_function_scope [sig] _ _ _ _.

    Global Arguments CForallT_rect [P]%_function_scope P%_function_scope f f0%_function_scope [ls]%_list_scope c f : rename.
    Global Arguments CForallT_ind [P]%_function_scope P%_function_scope f f0%_function_scope [ls]%_list_scope c f : rename.

  End ForallT.

  Section ForallP.

    Inductive CForall (P : forall (k : K), (V k) -> Prop) : forall [ls], context V ls -> Prop :=
    | CForall_nil : CForall P CtxEmpty
    | CForall_cons : forall [sig] k v (ctx : context _ sig),
      P k v -> CForall P ctx -> CForall P (CtxCons k v ctx).

    Global Arguments CForall_cons [P]%_function_scope [sig] _ _ _ _.

    Context {V': K -> Type}.

    Inductive CForall2 (P : forall (k : K), (V k) -> (V' k) -> Prop) : forall [ls], context V ls -> context V' ls -> Prop :=
    | CForall2_nil : CForall2 P CtxEmpty CtxEmpty
    | CForall2_cons : forall [sig] k v v' (ctx : context _ sig) (ctx' : context _ sig),
      P k v v' -> CForall2 P ctx ctx' -> CForall2 P (CtxCons k v ctx) (CtxCons k v' ctx').

    Global Arguments CForall_cons [P]%_function_scope [sig] _ _ _ _.
    Global Arguments CForall2_cons [P]%_function_scope [sig] _ _ _ _ _ _.

  End ForallP.
End Forall.

Section Forall2V.
  Context {K: Type}.
  Context {V V': K -> Type}.

  Inductive CForall2V (P : forall (k : K), (V k) -> (V' k) -> Prop) : forall [ls], context V ls -> context V' ls -> Prop :=
  | CForall2V_nil : CForall2V P CtxEmpty CtxEmpty
  | CForall2V_cons : forall [sig] k v v' (ctx ctx' : context _ sig),
    P k v v' -> CForall2V P ctx ctx' -> CForall2V P (CtxCons k v ctx) (CtxCons k v' ctx').

  Global Arguments CForall2V_cons [P]%_function_scope [sig] _ _ _ _ _ _ _ .

End Forall2V.

