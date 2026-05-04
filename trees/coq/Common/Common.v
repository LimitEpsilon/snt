(*! Utilities | Shared utilities !*)
Require Export Stdlib.micromega.Lia.
Require Export Stdlib.Arith.Arith.
Require Export Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.Strings.String.
Require Export EqDec Vect FiniteType Show.

Unset Universe Minimization ToSet.

Export EqNotations.
Export ListNotations.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Arguments Nat.log2_up !_.
Ltac bool_step :=
  match goal with
  | [ H: _ && _ = true |- _ ] => rewrite andb_true_iff in H
  | [ H: _ && _ = false |- _ ] => rewrite andb_false_iff in H
  | [ H: _ || _ = true |- _ ] => rewrite orb_true_iff in H
  | [ H: _ || _ = false |- _ ] => rewrite orb_false_iff in H
  | [ H: negb _ = true |- _ ] => rewrite negb_true_iff in H
  | [ H: negb _ = false |- _ ] => rewrite negb_false_iff in H
  | [ H: forallb _ (_ ++ _) = _ |- _ ] => rewrite forallb_app in H
  end.

Lemma app_if_comm {A B} (f : A -> B) (x y : A) (b : bool) :
  f (if b then x else y) = if b then f x else f y.
Proof. now destruct b. Qed.

Lemma Some_inj : forall {T} (x y: T), Some x = Some y -> x = y.
Proof.
  congruence.
Qed.

Lemma pair_inj : forall {T U} (t1: T) (u1: U) (t2: T) (u2: U),
    (t1, u1) = (t2, u2) -> t1 = t2 /\ u1 = u2.
Proof.
  inversion 1. auto.
Qed.

Lemma cons_inj : forall {T} (hd1 hd2 : T) (tl1 tl2 : list T),
    hd1 :: tl1 = hd2 :: tl2 -> hd1 = hd2 /\ tl1 = tl2.
Proof.
  inversion 1. auto.
Qed.

Ltac cleanup_step :=
  match goal with
  | _ => discriminate
  | _ => progress (subst; cbn)
  | [ H: Some _ = Some _ |- _ ] =>
    apply Some_inj in H
  | [ H: (_, _) = (_, _) |- _ ] =>
    apply pair_inj in H
  | [ H: _ /\ _ |- _ ] =>
    destruct H
  end.

Ltac destruct_match :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] =>
    destruct x eqn:?
  end.

(** find the head of the given expression **)
Ltac head expr :=
  match expr with
    | ?f _ => head f
    | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

Ltac rewrite_all_hypotheses :=
  repeat match goal with
         | [ H: ?x = ?y |- _ ] => rewrite H
         end.

Ltac setoid_rewrite_all_hypotheses :=
  repeat match goal with
         | [ H: ?x = ?y |- _ ] => setoid_rewrite H
         end.

(** Fails if x is equal to v. Can work for hypotheses **)
Ltac assert_neq x v :=
  tryif (let _ := (constr:(eq_refl x : x = v)) in idtac) then fail else idtac.

(** Rewrite using setoid_rewrite the hypothesis in all
    other hypotheses, as well as in the goal. **)
Tactic Notation "setoid_rewrite_in_all" constr(Hx) :=
  repeat match goal with
         | _ =>
           progress (setoid_rewrite Hx)
         | [ H: _ |- _ ] =>
           assert_neq Hx H;
           progress (setoid_rewrite Hx in H)
         end.

Tactic Notation "setoid_rewrite_in_all" "<-" constr(Hx) :=
  repeat match goal with
         | _ =>
           progress (setoid_rewrite <-Hx)
         | [ H: _ |- _ ] =>
           assert_neq Hx H;
           progress (setoid_rewrite <-Hx in H)
         end.

Ltac set_fixes :=
  repeat match goal with
         | [  |- context[?x] ] => is_fix x; set x in *
         end.

Inductive DP {A: Type} (a: A) : Prop :=.

Inductive Posed : list Prop -> Prop :=
| AlreadyPosed1 : forall {A} a, Posed [@DP A a]
| AlreadyPosed2 : forall {A1 A2} a1 a2, Posed [@DP A1 a1; @DP A2 a2]
| AlreadyPosed3 : forall {A1 A2 A3} a1 a2 a3, Posed [@DP A1 a1; @DP A2 a2; @DP A3 a3]
| AlreadyPosed4 : forall {A1 A2 A3 A4} a1 a2 a3 a4, Posed [@DP A1 a1; @DP A2 a2; @DP A3 a3; @DP A4 a4].

Tactic Notation "_pose_once" constr(witness) constr(thm) :=
  let tw := (type of witness) in
  match goal with
  | [ H: Posed ?tw' |- _ ] =>
    unify tw (Posed tw')
  | _ => pose proof thm;
        pose proof witness
  end.

Tactic Notation "pose_once" constr(thm) :=
  progress (let witness := constr:(AlreadyPosed1 thm) in
            _pose_once witness thm).

Tactic Notation "pose_once" constr(thm) constr(arg) :=
  progress (let witness := constr:(AlreadyPosed2 thm arg) in
            _pose_once witness (thm arg)).

Tactic Notation "pose_once" constr(thm) constr(arg) constr(arg') :=
  progress (let witness := constr:(AlreadyPosed3 thm arg arg') in
            _pose_once witness (thm arg arg')).

Tactic Notation "pose_once" constr(thm) constr(arg) constr(arg') constr(arg'') :=
  progress (let witness := constr:(AlreadyPosed4 thm arg arg' arg'') in
            _pose_once witness (thm arg arg' arg'')).

Ltac remember_once x :=
  match goal with
  | [ H: ?v = x |- _ ] =>
    is_var v
  | _ =>
    let Hx := fresh "H" in
    remember x eqn:Hx;
    setoid_rewrite_in_all <- Hx
  end.

Ltac constr_hd c :=
      match c with
      | ?f ?x => constr_hd f
      | ?g => g
      end.

Definition and_fst {A B} := fun '(conj a _: and A B) => a.
Definition and_snd {A B} := fun '(conj _ b: and A B) => b.

Fixpoint upto (n: nat) :=
  match n with
  | O => [0]
  | S x => n :: upto x
  end.

Notation log2 := Nat.log2_up.
Notation Nlog2 x := (N.to_nat (N.log2_up x)).

Instance EqDec_FiniteType {T} {FT: FiniteType T} : EqDec T | 3.
Proof.
  econstructor; intros.
  destruct (PeanoNat.Nat.eq_dec (finite_index t1) (finite_index t2)) as [ ? | Hneq ].
  - eauto using finite_index_injective.
  - right; intro Habs; apply (f_equal finite_index) in Habs.
    contradiction.
Defined.

Definition opt_bind {A B} (o: option A) (f: A -> option B) :=
  match o with
  | Some x => f x
  | None => None
  end.

Lemma opt_bind_f_equal {A B} o o' f f':
  o = o' ->
  (forall a, f a = f' a) ->
  @opt_bind A B o f = opt_bind o' f'.
Proof.
  intros * -> **; destruct o'; eauto.
Qed.

Notation "'let/opt' var ':=' expr 'in' body" :=
  (opt_bind expr (fun var => body)) (at level 200).

Notation "'let/opt2' v1 ',' v2 ':=' expr 'in' body" :=
  (opt_bind expr (fun '(v1, v2) => body)) (at level 200).

Notation "'let/opt3' v1 ',' v2 ',' v3 ':=' expr 'in' body" :=
  (opt_bind expr (fun '(v1, v2, v3) => body)) (at level 200).

Definition must {A} (o: option A) : if o then A else unit :=
  match o with
  | Some a => a
  | None => tt
  end.

Definition opt_lift_binop {T} (op : T -> T -> T) ox oy :=
  match ox with
  | Some x =>
    match oy with
    | Some y => Some (op x y)
    | None => Some x
    end
  | None => oy
  end.

Definition assert_opt {A} (o : option A) : o <> None -> A :=
  match o with
  | Some x => fun _ => x
  | None => fun NEQ => False_rect _ (NEQ eq_refl)
  end.

Lemma assert_opt_eqn {A} (o : option A) pf : o = Some (assert_opt o pf).
Proof.
  destruct o; auto; contradiction.
Qed.

Lemma assert_opt_Some {A} (x : A) pf : assert_opt (Some x) pf = x.
Proof. reflexivity. Qed.

Lemma assert_opt_spec {A} (o : option A) pf :
  forall x, assert_opt o pf = x <-> o = Some x.
Proof.
  destruct o; [|contradiction].
  simpl; split; inversion 1; subst; auto.
Qed.

Section Lists.
  Fixpoint list_find_opt {A B} (f: A -> option B) (l: list A) : option B :=
    match l with
    | [] => None
    | x :: l =>
      let fx := f x in
      match fx with
      | Some y => Some y
      | None => list_find_opt f l
      end
    end.

  Definition list_sum' n l :=
    List.fold_right (fun x acc => acc + x) n l.

  Definition list_sum l :=
    list_sum' 0 l.

  Definition list_max' n l :=
    List.fold_right (fun x acc => max acc x) n l.

  Definition list_max l :=
    list_max' 0 l.

  Lemma list_sum'_0 :
    forall l n, list_sum' n l = list_sum' 0 l + n.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - rewrite IHl.
      rewrite <- !Nat.add_assoc.
      rewrite (Nat.add_comm n a); reflexivity.
  Qed.

  Lemma list_sum_app :
    forall l1 l2, list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
  Proof.
    unfold list_sum, list_sum'; intros.
    rewrite fold_right_app, list_sum'_0.
    reflexivity.
  Qed.

  Lemma list_sum_firstn_le :
    forall n l, list_sum (firstn n l) <= list_sum l.
  Proof.
    induction n; destruct l; cbn; auto with arith.
  Qed.

  Lemma list_sum_skipn_le :
    forall n l, list_sum (skipn n l) <= list_sum l.
  Proof.
    induction n; destruct l; cbn; auto with arith.
  Qed.

  Fixpoint skipn_firstn {A} n n' (l: list A):
    List.skipn n (List.firstn n' l) =
    List.firstn (n' - n) (List.skipn n l).
  Proof.
    destruct n, n', l; cbn; try reflexivity.
    - destruct (n' - n); reflexivity.
    - rewrite skipn_firstn; reflexivity.
  Qed.

  Fixpoint firstn_skipn {A} n n' (l: list A):
    List.firstn n (List.skipn n' l) =
    List.skipn n' (List.firstn (n' + n) l).
  Proof.
    destruct n, n', l; cbn; try reflexivity;
      rewrite <- firstn_skipn; reflexivity.
  Qed.

  Fixpoint firstn_firstn {A} n n' (l: list A):
    List.firstn n (List.firstn n' l) =
    List.firstn (Nat.min n n') l.
  Proof.
    destruct n, n', l; cbn; auto using f_equal.
  Qed.

  Lemma firstn_map {A B} (f : A -> B) :
    forall n (l: list A),
      List.firstn n (List.map f l) =
      List.map f (List.firstn n l).
  Proof.
    induction n; destruct l; subst; cbn; auto using f_equal.
  Qed.

  Lemma skipn_map {A B} (f : A -> B) :
    forall n (l: list A),
      List.skipn n (List.map f l) =
      List.map f (List.skipn n l).
  Proof.
    induction n; destruct l; subst; cbn; auto using f_equal.
  Qed.

  Lemma skipn_app {A}:
    forall (l1 l2: list A) n,
      n <= List.length l1 ->
      skipn n (List.app l1 l2) = List.app (skipn n l1) l2.
  Proof.
    induction l1; destruct n; cbn; try (inversion 1; reflexivity).
    - intros; apply IHl1; lia.
  Qed.

  Lemma forallb_pointwise {A} :
    forall f1 f2 (ls: list A),
      (forall x, List.In x ls -> f1 x = f2 x) ->
      forallb f1 ls = forallb f2 ls.
  Proof.
    induction ls; cbn.
    - reflexivity.
    - intros; f_equal; eauto.
  Qed.

  Fixpoint dedup {A} {EQ: EqDec A} (acc: list A) (l: list A) :=
    match l with
    | [] => acc
    | a :: l =>
      let already_seen := List.in_dec eq_dec a acc in
      let acc := if already_seen then acc else a :: acc in
      dedup acc l
    end.

  Fixpoint iterate_tr (n: nat) {A} (f: A -> A) (init: A) :=
    match n with
    | 0 => init
    | S n => iterate_tr n f (f init)
    end.

  Fixpoint iterate (n: nat) {A} (f: A -> A) (init: A) :=
    match n with
    | 0 => init
    | S n => f (iterate n f init)
    end.

  Lemma iterate_assoc:
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate n f (f init) = f (iterate n f init).
  Proof.
    induction n; simpl; intros; try rewrite IHn; reflexivity.
  Qed.

  Lemma iterate_S_acc :
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate (S n) f init = iterate n f (f init).
  Proof. intros; symmetry; apply iterate_assoc. Qed.

  Lemma iterate_tr_correct :
    forall (n: nat) {A} (f: A -> A) (init: A),
      iterate_tr n f init = iterate n f init.
  Proof.
    induction n; simpl; intros.
    - reflexivity.
    - rewrite IHn, iterate_assoc; reflexivity.
  Qed.

  Lemma iterate_pointwise_inv {A} (f g: A -> A) (inv: A -> Prop):
    (* Use g because that's usually the simpler one *)
    (forall x, inv x -> inv (g x)) ->
    (forall x, inv x -> f x = g x) ->
    forall n,
    forall init: A,
      inv (init) ->
      iterate n f init = iterate n g init.
  Proof.
    intros Hinv Heq; induction n; intros init Hinvi.
    - reflexivity.
    - simpl; rewrite <- !iterate_assoc, Heq; auto.
  Qed.

  Lemma split_app {A B} (l1 l2 : list (A * B)) :
    split (l1 ++ l2) = (fst (split l1) ++ fst (split l2), snd (split l1) ++ snd (split l2)).
  Proof.
    revert l2. induction l1; simpl; eauto using surjective_pairing.
    destruct a; simpl; intros; rewrite IHl1.
    now destruct (split l1).
  Qed.

  Lemma split_inj {A B} (l1 l2 : list (A * B)) :
    split l1 = split l2 -> l1 = l2.
  Proof.
    intros.
    rewrite <- (split_combine _ (surjective_pairing (split l1))).
    rewrite <- (split_combine _ (surjective_pairing (split l2))).
    rewrite H. auto.
  Qed.

  Lemma fold_left_max_monotonic l :
    forall x y, x <= y -> fold_left max l x <= fold_left max l y.
  Proof.
    induction l; simpl; auto. intros. eapply IHl. lia.
  Qed.

  Lemma fold_left_max_expansive l :
    forall x y, x <= y -> x <= fold_left max l y.
  Proof.
    induction l; simpl; auto. intros. apply IHl. lia.
  Qed.

  Lemma fold_left_max_split l :
    forall init, fold_left max l init = max (fold_left max l 0) init.
  Proof.
    induction l; simpl; auto. intros. rewrite IHl. symmetry. rewrite IHl. lia. 
  Qed.

  Lemma fold_left_max_Forall l :
    forall init,
      let t := fold_left max l init in
      Forall (fun x => x <= t) l.
  Proof.
    induction l; simpl; auto. intros. rewrite Forall_cons_iff.
    split; auto. apply fold_left_max_expansive. lia.
  Qed.

  Lemma fold_left_max_In (l : list nat) :
    forall init,
      let t := fold_left max l init in
      t = init \/ In t l.
  Proof.
    induction l; simpl; auto. intros.
    specialize (IHl (max init a)).
    cbn zeta in IHl. destruct IHl as [IHl|IHl]; eauto.
    rewrite IHl. lia.
  Qed.

  Lemma fold_left_rev_append {T} {l : list (list T)} :
    forall init,
      fold_left (fun acc x => rev_append x acc) l init =
      fold_left (fun acc x => rev_append x acc) l [] ++ init.
  Proof.
    induction l; simpl; auto.
    intros. rewrite IHl. symmetry. rewrite IHl.
    rewrite <- app_assoc. f_equal. repeat rewrite rev_append_rev.
    rewrite <- app_assoc. auto.
  Qed.

  Lemma rev_fold_left_rev_append {T} {l : list (list T)} :
    rev (fold_left (fun acc x => rev_append x acc) l []) =
    fold_right (fun x y => x ++ y) [] l.
  Proof.
    intros. induction l; simpl; auto.
    rewrite <- IHl, <- (rev_involutive a), <- rev_app_distr.
    f_equal. rewrite rev_append_rev, rev_involutive, app_nil_r.
    apply fold_left_rev_append.
  Qed.

  Lemma app_fold_right {A} {l : list (list A)} :
    forall init : list A, fold_right (@app A) init l = fold_right (@app A) [] l ++ init.
  Proof.
    induction l; simpl; auto.
    intros. now rewrite IHl, app_assoc.
  Qed.

  Lemma Forall_filter {A P f} {l : list A} :
    Forall P (filter f l) <-> Forall (fun x => f x = true -> P x) l.
  Proof.
    induction l; simpl; auto.
    { intuition auto. }
    destruct (f a) eqn:EQ.
    - repeat rewrite Forall_cons_iff. rewrite IHl.
      intuition auto.
    - rewrite IHl, Forall_cons_iff, EQ. intuition auto. congruence.
  Qed.

  Lemma filter_filter {A P Q} {l : list A} :
    filter P (filter Q l) = filter (fun x => P x && Q x) l.
  Proof.
    induction l; simpl; auto. destruct (Q a) eqn:QQ; simpl.
    - destruct (P a); simpl; auto. now rewrite IHl.
    - rewrite andb_false_r. auto.
  Qed.

  Lemma combine_app {A B} (x1 x2 : list A) (y1 y2 : list B) :
    List.length x1 = List.length y1 ->
    combine (x1 ++ x2)%list (y1 ++ y2)%list = (combine x1 y1 ++ combine x2 y2)%list.
  Proof.
    revert y1 x2 y2. induction x1; simpl; auto.
    - intros. apply eq_sym in H. now rewrite length_zero_iff_nil in *; subst.
    - intros [|hd tl]; simpl; inversion 1. f_equal. auto.
  Qed.

  Lemma combine_fst {A B} (a : list A) (b : list B) :
    List.length a = List.length b ->
    map fst (combine a b) = a.
  Proof.
    revert b. induction a; simpl; auto.
    intros [|hd tl]; simpl; inversion 1. f_equal. auto.
  Qed.

  Lemma combine_snd {A B} (a : list A) (b : list B) :
    List.length a = List.length b ->
    map snd (combine a b) = b.
  Proof.
    revert b. induction a; simpl; auto.
    - intros. apply eq_sym in H. now rewrite length_zero_iff_nil in *; subst.
    - intros [|hd tl]; simpl; inversion 1. f_equal. auto.
  Qed.
End Lists.

Require Stdlib.Streams.Streams.

Declare Scope stream_scope.
Open Scope stream_scope.

Module StreamNotations.
  Infix ":::" := Streams.Cons (at level 60, right associativity) : stream_scope.
End StreamNotations.

Module Streams.
  Include Stdlib.Streams.Streams.

  Import StreamNotations.

  CoFixpoint coiterate {A} (f: A -> A) (init: A) :=
    init ::: coiterate f (f init).

  Lemma coiterate_eqn {A} (f: A -> A) (init: A) :
    coiterate f init =
    init ::: coiterate f (f init).
  Proof.
    rewrite (Streams.unfold_Stream (coiterate f init)) at 1; reflexivity.
  Qed.

  Lemma map_eqn {A B} (f: A -> B) (s: Streams.Stream A) :
    Streams.map f s =
    f (Streams.hd s) ::: Streams.map f (Streams.tl s).
  Proof.
    rewrite (Streams.unfold_Stream (Streams.map f s)) at 1; reflexivity.
  Qed.

  Lemma Str_nth_0 {A} (hd: A) tl:
    Streams.Str_nth 0 (hd ::: tl) = hd.
  Proof. reflexivity. Qed.

  Lemma Str_nth_S {A} (hd: A) tl n:
    Streams.Str_nth (S n) (hd ::: tl) = Streams.Str_nth n tl.
  Proof. reflexivity. Qed.

  Lemma Str_nth_coiterate {A} (f: A -> A) :
    forall n (init: A),
      Streams.Str_nth n (coiterate f init) =
      iterate n f init.
  Proof.
    setoid_rewrite <- iterate_tr_correct.
    induction n; cbn; intros.
    - reflexivity.
    - rewrite coiterate_eqn.
      apply IHn.
  Qed.

  Lemma coiterate_pointwise {A} (f g: A -> A):
    (forall x, f x = g x) ->
    forall init: A,
      Streams.EqSt (coiterate f init) (coiterate g init).
  Proof.
    intros Heq; cofix IH; intros init.
    constructor; simpl.
    - reflexivity.
    - rewrite Heq; apply IH.
  Qed.

  Lemma coiterate_pointwise_inv {A} (f g: A -> A) (inv: A -> Prop):
    (forall x, inv x -> inv (g x)) -> (* Use g because that's usually the simpler one *)
    (forall x, inv x -> f x = g x) ->
    forall init: A,
      inv (init) ->
      Streams.EqSt (coiterate f init) (coiterate g init).
  Proof.
    intros Hinv Heq; cofix IH; intros init Hinvi.
    constructor; simpl.
    - reflexivity.
    - rewrite Heq; auto.
  Qed.

  Fixpoint firstn {A} (n: nat) (s: Stream A) : list A :=
    match n with
    | 0 => []
    | S n => match s with
            | Cons hd tl => hd :: firstn n tl
            end
    end.
End Streams.

Inductive result {S F} :=
| Success (s: S)
| Failure (f: F).

Arguments result : clear implicits.

Definition result_map_failure {S F1 F2} (fn: F1 -> F2) (r: result S F1) :=
  match r with
  | Success s => Success s
  | Failure f => Failure (fn f)
  end.

Definition opt_result {S F} (o: option S) (f: F): result S F :=
  match o with
  | Some x => Success x
  | None => Failure f
  end.

Notation "'let/res' var ':=' expr 'in' body" :=
  (match expr with
   | Success var => body
   | Failure f => Failure f
   end)
    (at level 200).

Section result_list_map.
  Context {A B F: Type}.
  Context (f: A -> result B F).

  (* Written this way to allow use in fixpoints *)
  Fixpoint result_list_map (la: list A): result (list B) F :=
    match la with
    | [] => Success []
    | a :: la => let/res b := f a in
               let/res la := result_list_map la in
               Success (b :: la)
    end.
End result_list_map.

Definition is_success {S F} (r: result S F) :=
  match r with
  | Success s => true
  | Failure f => false
  end.

Definition extract_success {S F} (r: result S F) (pr: is_success r = true) :=
  match r return is_success r = true -> S with
  | Success s => fun _ => s
  | Failure f => fun pr => match Bool.diff_false_true pr with end
  end pr.

Global Instance EqDec_positive : EqDec positive := _.

#[local] Lemma mp : forall P Q, P -> (P -> Q) -> Q. intuition. Qed.

Ltac exploit H := eapply mp; [eapply H |].

Ltac des :=
  repeat match goal with
  | H : _ \/ _ |- _ => destruct H as [H | H]
  | H : _ /\ _ |- _ =>
    let H' := fresh H in
    destruct H as [H H']
  | H : exists x, _ |- _ =>
    let x := fresh x in
    destruct H as [x H]
  end.

Ltac clarify :=
  repeat match goal with
  | H : ?A _ = ?A _ |- _ => injection H; clear H; repeat intro; subst
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => solve [inversion H]
  | H : False |- ?G => exact (False_rect G H)
  | H : True |- _ => clear H
  | H : _ <> _ |- _ => specialize (H eq_refl)
  end; subst.

Tactic Notation "rew_under" ident_list(x) "in" ident(H) "with" uconstr(RR) :=
  let H' := fresh H in
  assert _ as H' by (intros x;
                     repeat match goal with
                     | x : ?T |- _ => is_evar T; refine (let H := H x in _)
                     end; rewrite RR in H; exact H);
  clear H; rename H' into H
.

