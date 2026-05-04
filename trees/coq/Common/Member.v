(*! Utilities | Dependent type tracking membership into a list !*)
Require Import Common.
Open Scope type.

Inductive member {K: Type}: K -> list K -> Type :=
| MemberHd: forall k sig, member k (k :: sig)
| MemberTl: forall k k' sig, member k sig -> member k (k' :: sig).

Definition member_nil {K} {k : K} : member k [] -> (False : Type) :=
  fun H => 
    match H in (member _ l) return (l = [] -> _ ) with 
    | MemberHd _ _ => fun H => False_rect _ 
      (eq_rect_r (x:=[]) (fun ls => match ls with | [] => True | _ => False end) I H)
    | MemberTl _ _ _ _ => fun H => False_rect _ 
      (eq_rect_r (x:=[]) (fun ls => match ls with | [] => True | _ => False end) I H)
    end eq_refl.

(* https://github.com/coq/coq/issues/10749 *)
Definition eq_type {A} (a a': A) : Type :=
  eq a a'.

Definition mdestruct {K sig} {k: K} (m: member k sig)
  : match sig return member k sig -> Type with
    | [] => fun m => False
    | k' :: sig =>
      fun m => ({ eqn: (eq_type k k') & m = eq_rect _ _ (fun _ => MemberHd k sig) _ eqn m } +
             { m': member k sig & m = MemberTl k k' sig m' })%type
    end m :=
  match m as m' in member k sig return
    match sig return member k sig -> Type with
    | [] => fun m => False
    | k' :: sig =>
      fun m => ({ eqn: (eq_type k k') & m = eq_rect _ _ (fun _ => MemberHd k sig) _ eqn m } +
            { m': member k sig & m = MemberTl k k' sig m' })%type
    end m'
  with 
  | MemberHd _ _ =>  inl (existT _ eq_refl eq_refl)
  | MemberTl _ _ _ _ => inr (existT _ _ eq_refl)
  end.

Lemma member_In {K} (sig: list K):
  forall k, member k sig -> List.In k sig.
Proof.
  induction 1; firstorder.
Qed.

Fixpoint member_idx {K sig} {k: K} (m: member k sig) : nat :=
  match m with
  | MemberHd k sig => 0
  | MemberTl k k' sig m' => S (member_idx m')
  end.

Lemma member_idx_nth {K sig} (k: K) (m: member k sig) :
  List.nth_error sig (member_idx m) = Some k.
Proof.
  induction m; firstorder.
Qed.

Lemma nth_member {T}:
  forall (ls: list T) idx t,
    List.nth_error ls idx = Some t ->
    member t ls.
Proof.
  induction ls; destruct idx; cbn; inversion 1; subst;
    eauto using MemberHd, MemberTl.
Defined.

Lemma member_idx_inj {K sig} `{EqDec K} {k: K}
      (m m': member k sig) :
  member_idx m = member_idx m' ->
  m = m'.
Proof.
  induction m; cbn; intros * Hidx;
    destruct (mdestruct m') as [(Hr & Heq) | (m'' & ->)]; cbn in *; subst; cbn in *;
      try destruct Hr; try rewrite <- Eqdep_dec.eq_rect_eq_dec in * by apply eq_dec;
        cbn in *; subst; cbn in *; inversion Hidx; subst.
  - reflexivity.
  - f_equal; eauto.
Qed.

Lemma member_idx_inj_contra {K sig} `{EqDec K} {k: K}
      (m m': member k sig) :
  m <> m' ->
  member_idx m <> member_idx m'.
Proof.
  intros ** Heq%member_idx_inj; congruence.
Qed.

Lemma member_idx_inj_k {K sig} {k k': K}
      (m: member k sig) (m': member k' sig) :
  member_idx m = member_idx m' ->
  k = k'.
Proof.
  intros * Heq;
    eapply f_equal in Heq; erewrite !member_idx_nth in Heq;
      congruence.
Qed.

Lemma member_idx_inj_k_contra {K sig} {k k': K}
      (m: member k sig) (m': member k' sig) :
  k <> k' -> member_idx m <> member_idx m'.
Proof.
  intros ** Heq%member_idx_inj_k; congruence.
Qed.

Fixpoint member_map {K K'} (f: K -> K') {k: K} {ls: list K}
         (m: member k ls) : member (f k) (List.map f ls) :=
  match m in (member k ls) return (member (f k) (List.map f ls)) with
  | MemberHd k sig =>
    MemberHd (f k) (List.map f sig)
  | MemberTl k k' sig m' =>
    MemberTl (f k) (f k') (List.map f sig) (member_map f m')
  end.

Lemma member_map_idx  {K K'} (f: K -> K') (k: K) (ls: list K)
      (m: member k ls) :
  member_idx (member_map f m) = member_idx m.
Proof.
  induction m; cbn; eauto.
Qed.

Lemma member_NoDup {K} {sig: list K} k:
  EqDec K ->
  NoDup sig ->
  forall (m1 m2: member k sig),
    m1 = m2.
Proof.
  induction 2.
  - intros; destruct (mdestruct m1).
  - intros; destruct (mdestruct m1) as [(-> & ->) | (mem & ->)]; cbn.
    + intros; destruct (mdestruct m2) as [(? & ->) | (absurd & ->)]; cbn.
      * rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_dec.
        reflexivity.
      * exfalso; apply member_In in absurd; auto.
    + intros; destruct (mdestruct m2) as [(-> & ->) | (? & ->)]; cbn.
      * exfalso; apply member_In in mem. auto.
      * f_equal; apply IHNoDup.
Qed.

Fixpoint mem {K} `{EqDec K} (k: K) sig {struct sig} : member k sig + (member k sig -> False).
Proof.
  destruct sig.
  - right; intro m; destruct (mdestruct m).
  - destruct (eq_dec k k0) as [Heq | Hneq].
    + subst. left. apply MemberHd.
    + destruct (mem _ _ k sig) as [m | ].
      * left. apply MemberTl. exact m.
      * right. intros m.
        destruct (mdestruct m) as [(eqn & Heq) | (m' & Heq)]; congruence.
Defined.

Fixpoint mem_opt {K} `{EqDec K} (k: K) sig {struct sig} : option (member k sig) :=
  match sig with
  | [] => None
  | k' :: sig =>
    match eq_dec k k' return option (member k (k' :: sig)) with
    | left eqn => Some (rew <-[fun k => member k (k' :: sig)] eqn in MemberHd k' sig)
    | right _ =>
      match mem_opt k sig with
      | Some m => Some (MemberTl k k' sig m)
      | None => None
      end
    end
  end.

Lemma mem_opt_correct  {K} `{EqDec K} (k: K) (sig: list K) :
  mem_opt k sig = match mem k sig with
                  | inl m => Some m
                  | inr _ => None
                  end.
Proof.
  induction sig as [| k0 sig0 IHsig]; cbn.
  - reflexivity.
  - destruct (eq_dec k k0) as [Heq | Hneq].
    + destruct Heq; reflexivity.
    + rewrite IHsig; destruct mem; reflexivity.
Qed.

Fixpoint find {K} (fn: K -> bool) sig {struct sig} : option { k: K & member k sig }.
Proof.
  destruct sig.
  - right.
  - destruct (fn k) eqn:?.
    + left. eexists. apply MemberHd.
    + destruct (find _ fn sig) as [ (k' & m) | ].
      * left. eexists. apply MemberTl. eassumption.
      * right.
Defined.

Fixpoint assoc {K1 K2: Type} `{EqDec K1}
         (k1: K1) sig {struct sig} : option { k2: K2 & member (k1, k2) sig }.
Proof.
  destruct sig as [ | (k1' & k2) sig ].
  - right.
  - destruct (eq_dec k1 k1'); subst.
    + left. eexists. apply MemberHd.
    + destruct (assoc _ _ _ k1 sig) as [ (k2' & m) | ].
      * left. eexists. apply MemberTl. eassumption.
      * right.
Defined.

Fixpoint mmap {K V} (l: list K) (f: forall k: K, member k l -> V) {struct l} : list V :=
  match l return ((forall k : K, member k l -> V) -> list V) with
   | [] => fun _ => []
   | k :: l => fun f => f k (MemberHd k l) :: mmap l (fun k' m => f k' (MemberTl k' k l m))
   end f.

Fixpoint mprefix {K} (prefix: list K) {sig: list K} {k} (m: member k sig)
  : member k (prefix ++ sig) :=
  match prefix return member k sig -> member k (prefix ++ sig) with
  | [] => fun m => m
  | k' :: prefix => fun m => MemberTl k k' (prefix ++ sig) (mprefix prefix m)
  end m.

Fixpoint minfix {K} (infix: list K) {sig sig': list K} {k} (m: member k (sig ++ sig'))
  : member k (sig ++ infix ++ sig').
Proof.
  destruct sig as [ | k' sig].
  - exact (mprefix infix m).
  - destruct (mdestruct m) as [(eqn & Heq) | (m' & Heq)];
      [ destruct eqn | ]; cbn in *.
    + exact (MemberHd k (sig ++ infix ++ sig')).
    + exact (MemberTl k k' (sig ++ infix ++ sig') (minfix _ infix sig sig' k m')).
Defined.

Definition mprefix_pair {K sig} (k: K) (p: {k': K & member k' sig})
  : {k': K & member k' (k :: sig)} :=
  let '(existT _ k' m) := p in
  existT _ k' (MemberTl k' k _ m).

Fixpoint all_members {K} (sig: list K): list { k: K & member k sig } :=
  match sig with
  | [] => []
  | k :: sig => let ms := all_members sig in
              let ms := List.map (mprefix_pair k) ms in
              (existT _ k (MemberHd k sig)) :: ms
  end.

Definition mreplace {K} {x: K} {ls : list K}
  : member x ls -> forall (y : K), { ls' & member y ls'}.
Proof.
  refine (
    fun H y => 
      member_rect _ (fun x ls _ => forall (y : K), { ls' & member y ls'})
      _
      _
      _ _ H y
  ).
  refine (
    fun _ ls' y' => existT _ _ (MemberHd y' ls')
  ).
  refine (
    fun x x' ls' m IH y' => 
      let (_, m') := IH y' in existT _ _ (MemberTl _ x' _ m')
  ).
Defined.

