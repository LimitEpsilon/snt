(*! Equations showing how to implement functions on structures and arrays as bitfuns !*)
From Koika Require Export
  Lang.Types
  Lang.Primitives
.
Import
  PrimTyped
  CircuitSignatures
  CircuitPrimSpecs
  Primitives.BitFuns
.

Lemma one_bit_case (x : bits 1) : x = Ob~1 \/ x = Ob~0.
Proof. destruct x as [vhd []]; destruct vhd; eauto. Qed.

Lemma unfold_single x : Bits.single Ob~x = x.
Proof. reflexivity. Qed.

Lemma length_const {T} :
  forall n (b : T), List.length (const n b) = n.
Proof. induction n; cbn; auto. Qed.

Lemma const_app {T} :
  forall m n (a : T), const m a ++ const n a = const (m + n) a.
Proof. induction m; cbn; intros; f_equal; auto. Qed.

Lemma skipn_const {c : bool} :
  forall k x, skipn k (const x c) = const (x - k) c.
Proof.
  induction k; simpl. intros; f_equal; lia. destruct x; simpl; auto.
Qed.

Lemma firstn_const {c : bool} :
  forall k x, firstn k (const x c) = const (Nat.min k x) c.
Proof.
  induction k; simpl; auto. destruct x; simpl; f_equal; auto.
Qed.

Ltac min_t :=
  repeat match goal with
  | [ |- context[Nat.min ?x ?y] ] =>
    first [rewrite (Nat.min_l x y) by min_t |
      rewrite (Nat.min_r x y) by min_t ]
  | _ => lia
  end.

Lemma slice_end :
  forall sz sz' (v : bits (sz + sz')),
    Bits.slice sz sz' v = vect_skipn_plus sz v.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold Bits.slice, vect_skipn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  min_t; rewrite Nat.sub_diag by lia; cbn.
  rewrite app_nil_r.
  rewrite firstn_skipn.
  rewrite firstn_all2 by (rewrite vect_to_list_length; reflexivity).
  reflexivity.
Qed.

Lemma slice_front :
  forall n sz (v: bits (n + sz)) offset width,
    offset + width <= n ->
    Bits.slice offset width v =
    Bits.slice offset width (vect_firstn_plus n v).
Proof.
  intros.
  apply vect_to_list_inj.
  unfold Bits.slice, vect_extend_end_firstn, vect_extend_end, vect_firstn_plus.
  autorewrite with vect_to_list.
  rewrite skipn_firstn, firstn_firstn.
  min_t; reflexivity.
Qed.

Ltac unfold_slice :=
  cbv [Bits.slice vect_extend_end_firstn Bits.extend_end]
.

Lemma slice_zero :
  forall offset sz (x : bits sz), Bits.slice offset 0 x = Ob.
Proof.
  intros.
  apply vect_to_list_inj.
  unfold_slice.
  autorewrite with vect_to_list.
  reflexivity.
Qed.

Lemma slice_shift_width1 prefix offset width sz (x : bits sz):
  sz >= prefix + offset ->
  Bits.slice offset (prefix + width) x =
  (Bits.slice offset prefix x ++ Bits.slice (prefix + offset) width x)%vect.
Proof.
  intro LE.
  apply vect_to_list_inj.
  rewrite vect_to_list_app.
  unfold_slice.
  autorewrite with vect_to_list.
  assert (sz < prefix + offset + width \/ sz >= prefix + offset + width)
    as [CASE | CASE] by lia;
  min_t;
  repeat rewrite Nat.sub_diag;
  repeat rewrite app_nil_r.
  1:rewrite app_assoc; f_equal; [|f_equal; lia].
  all:specialize (vect_to_list_length x);
    generalize (vect_to_list x); clear x; intros; subst.
  all:rewrite <- firstn_app_2, length_firstn, length_skipn.
  all:min_t; f_equal; rewrite <- skipn_skipn, List.firstn_skipn.
  all:reflexivity.
Qed.

Lemma slice_shift_width2 prefix offset width sz (x : bits sz):
  sz < prefix + offset ->
  Bits.slice offset (prefix + width) x =
  (Bits.slice offset prefix x ++ Bits.slice (prefix + offset) width x)%vect.
Proof.
  intro LT.
  apply vect_to_list_inj.
  rewrite vect_to_list_app.
  unfold_slice.
  autorewrite with vect_to_list.
  min_t.
  specialize (vect_to_list_length x);
  generalize (vect_to_list x); clear x; intros; subst.
  rewrite (skipn_all2 (n := prefix + offset)); [|lia].
  rewrite firstn_nil.
  rewrite app_nil_l.
  repeat rewrite firstn_skipn.
  rewrite <- app_assoc.
  f_equal.
  - f_equal.
    repeat rewrite firstn_all2; first [lia | reflexivity].
  - rewrite const_app.
    f_equal.
    lia.
Qed.

Lemma slice_shift_width prefix offset width sz (x : bits sz) :
  Bits.slice offset (prefix + width) x =
  (Bits.slice offset prefix x ++ Bits.slice (prefix + offset) width x)%vect.
Proof.
  assert (sz >= prefix + offset \/ sz < prefix + offset) as
    [CASE | CASE] by lia;
  [apply slice_shift_width1 | apply slice_shift_width2]; assumption.
Qed.

Lemma slice_app p sz width (prefix : bits p) (x : bits sz) :
  Bits.slice p width (prefix ++ x)%vect = Bits.slice 0 width x.
Proof.
  apply vect_to_list_inj.
  unfold_slice.
  autorewrite with vect_to_list.
  repeat (lia || f_equal).
  rewrite Nat.sub_diag.
  rewrite <- app_nil_l.
  f_equal.
  apply skipn_all2.
  rewrite vect_to_list_length.
  constructor.
Qed.

Lemma slice_subst_end :
  forall sz0 sz (bs0: bits (sz0 + sz)) (bs: bits sz),
    Bits.slice_subst sz0 sz bs0 bs = Bits.app bs (fst (Bits.split bs0)).
Proof.
  unfold Bits.split; intros; rewrite vect_split_firstn_skipn; cbn.
  apply vect_to_list_inj.
  unfold Bits.slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite !vect_skipn_plus_cast, vect_to_list_length, Nat.sub_diag; cbn.
  rewrite firstn_firstn by lia; min_t.
  rewrite (firstn_all2 (n := sz)) by (rewrite vect_to_list_length; lia).
  rewrite app_nil_r; reflexivity.
Qed.

Lemma slice_subst_front :
  forall sz0 sz width (bs0: bits (sz0 + sz)) (bs: bits width) offset,
    offset + width <= sz0 ->
    Bits.slice_subst offset width bs0 bs =
    Bits.app (vect_skipn_plus sz0 bs0) (Bits.slice_subst offset width (vect_firstn_plus sz0 bs0) bs).
Proof.
  clear.
  intros.
  apply vect_to_list_inj;
    unfold Bits.slice_subst, vect_skipn_plus, vect_firstn_plus, vect_extend_end_firstn, vect_extend_end.
  autorewrite with vect_to_list.
  rewrite !firstn_app.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite vect_to_list_length; cbn.
  rewrite !firstn_firstn; repeat min_t.
  rewrite firstn_length_le by (rewrite vect_to_list_length; lia).
  rewrite <- !app_assoc.
  rewrite skipn_firstn, firstn_firstn.
  min_t.
  rewrite !(firstn_all2 (vect_to_list bs)) by (rewrite vect_to_list_length; lia).
  replace (sz0 + sz - offset - width) with (sz0 + sz - (offset + width)) by lia.
  replace (sz0 - offset - width) with (sz0 - (offset + width)) by lia.
  rewrite <- !skipn_firstn.
  rewrite (firstn_all2 (n := sz0 + sz)) by (rewrite vect_to_list_length; lia).
  rewrite <- skipn_app by (rewrite length_firstn, vect_to_list_length; min_t; lia).
  rewrite List.firstn_skipn.
  reflexivity.
Qed.

Ltac _eq_t :=
  unfold _eq, _neq, beq_dec;
    intros; repeat destruct eq_dec; subst; congruence.

Lemma sel_msb {sz} (bs: bits sz):
  sel bs (Bits.of_nat (log2 sz) (pred sz)) =
  Ob~(Bits.msb bs).
Proof.
  unfold sel, Bits.to_index.
  rewrite Bits.to_nat_of_nat by eauto using pred_lt_pow2_log2.
  destruct sz.
  - reflexivity.
  - rewrite index_of_nat_largest.
    setoid_rewrite vect_last_nth; reflexivity.
Qed.

Definition le_plus_minus_r :=
  fun n m Hle => eq_trans (Nat.add_comm _ _) (Nat.sub_add n m Hle)
.

Hint Unfold Bits.slice : vect_to_list.
Hint Unfold Bits.slice_subst : vect_to_list.
Hint Unfold vect_extend_end : vect_to_list.
Hint Unfold vect_extend_end_firstn : vect_to_list.

Ltac vect_to_list_t_step :=
  match goal with
  | _ => progress cbn
  | _ => progress (autounfold with vect_to_list)
  | _ => progress autorewrite with vect_to_list vect_to_list_cleanup
  | [ |- context[match ?x with _ => _ end] ] => destruct x
  | _ => repeat rewrite ?Nat.min_l, ?Nat.min_r by lia
  end.

Ltac vect_to_list_t :=
  try apply vect_to_list_inj; repeat vect_to_list_t_step.

Lemma slice_full {sz}:
  forall (bs: bits sz),
    Bits.slice 0 sz bs = bs.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz)) by (autorewrite with vect_to_list; lia);
    reflexivity.
Qed.

Lemma slice_shift_offset shift offset width sz (x : bits sz) :
  Bits.slice (shift + offset) width x =
  Bits.slice shift width (Bits.slice offset (shift + width) x).
Proof.
  rewrite slice_shift_width.
  rewrite slice_app.
  symmetry.
  apply slice_full.
Qed.

Lemma slice_concat_l {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    Bits.slice 0 sz1 (bs1 ++ bs2)%vect = bs1.
Proof.
  intros; vect_to_list_t.
  rewrite (firstn_all2 (n := sz1)) by (autorewrite with vect_to_list; lia);
    reflexivity.
Qed.

Lemma slice_concat_r {sz1 sz2} :
  forall (bs1: bits sz1) (bs2: bits sz2),
    Bits.slice sz1 sz2 (bs1 ++ bs2)%vect = bs2.
Proof.
  intros; vect_to_list_t.
  rewrite (skipn_all2 (n := sz1)) by (autorewrite with vect_to_list; lia).
  vect_to_list_t.
  rewrite (firstn_all2 (n := sz2)) by (autorewrite with vect_to_list; lia).
  reflexivity.
Qed.

Lemma slice_eat_front {x y} z (a : bits x) {m} (b : bits m) :
  Bits.slice (x + y) z (a ++ b)%vect = Bits.slice y z b.
Proof.
  intros.
  replace (x + y) with (y + x) by lia.
  rewrite slice_shift_offset, slice_app.
  rewrite <- slice_shift_offset. f_equal; lia.
Qed.

Lemma slice_extend_end_cast {sz sz'} (LE : sz <= sz') :
  sz + (sz' - sz) = sz'.
Proof. lia. Qed.

Lemma slice_extend_end {sz sz'} (x : bits sz) (LE : sz <= sz') :
  Bits.slice 0 sz' x =
  cast (V := Bits.bits) (x ++ Bits.zero)%vect (slice_extend_end_cast LE).
Proof.
  unfold cast. destruct (eq_dec _ _). 2: lia.
  vect_to_list_t. f_equal.
  apply firstn_all2.
  rewrite vect_to_list_length. assumption.
Qed.

Lemma slice_cast {sz sz'} (x : bits sz) (EQ : sz = sz') offset width :
  Bits.slice offset width (cast x EQ) =
  Bits.slice offset width x.
Proof.
  destruct EQ; subst. unfold cast. rewrite eq_dec_refl; auto.
Qed.

Lemma slice_injective {sz sz'} (x y : bits sz) (LE : sz <= sz') :
  Bits.slice 0 sz' x = Bits.slice 0 sz' y -> x = y.
Proof.
  do 2 rewrite (slice_extend_end _ LE).
  intro EQ.
  apply (f_equal (Bits.slice 0 sz)) in EQ.
  repeat rewrite slice_cast in EQ.
  repeat rewrite slice_concat_l in EQ.
  auto.
Qed.

Lemma slice_divide {m n} (x y : bits m) :
  Bits.slice 0 n x = Bits.slice 0 n y ->
  Bits.slice n (m - n) x = Bits.slice n (m - n) y ->
  x = y.
Proof.
  intros LOWER UPPER.
  assert (Bits.slice 0 n x ++ Bits.slice (n + 0) (m - n) x =
    Bits.slice 0 n y ++ Bits.slice (n + 0) (m - n) y)%vect by
    (rewrite Nat.add_0_r, LOWER, UPPER; auto).
  repeat rewrite <- slice_shift_width in *|-.
  assert (m <= n + (m - n)) as LE by lia.
  eapply slice_injective; eauto.
Qed.

Definition forall_option_comm_bits {T} :=
  fix go {n} : (bits n -> option T) -> option (bits n -> T) :=
  match n with
  | 0 => fun f =>
    match f Ob with
    | Some t => Some (fun _ => t)
    | None => None
    end
  | S n => fun f =>
    let f0 := go (fun bs => f bs~0) in
    let f1 := go (fun bs => f bs~1) in
    match f0, f1 with
    | Some f0, Some f1 => Some (fun bs : bits (S n) =>
      if vect_hd bs then f1 (vect_tl bs) else f0 (vect_tl bs))
    | _, _ => None
    end
  end.

Lemma forall_option_comm_bits_spec {T n} :
  forall f,
    match @forall_option_comm_bits T n f with
    | Some g => forall bs, f bs = Some (g bs)
    | None => exists bs, f bs = None
    end.
Proof.
  induction n; simpl; eauto.
  - intros. destruct (f Ob) eqn:F; eauto.
    now intros [].
  - intros.
    specialize (IHn (fun bs => f bs~0)) as IHn0.
    specialize (IHn (fun bs => f bs~1)) as IHn1.
    destruct (forall_option_comm_bits _); [|des; eauto].
    destruct (forall_option_comm_bits _); [|des; eauto].
    intros ([|] & tl); eauto.
Qed.

Fixpoint forallb_bits {n} : (bits n -> bool) -> bool :=
  match n with
  | 0 => fun f => f Ob
  | S n => fun f =>
    let b0 := forallb_bits (fun bs => f bs~0) in
    let b1 := forallb_bits (fun bs => f bs~1) in
    b0 && b1
  end.

Lemma forallb_bits_spec {n} :
  forall f,
    if @forallb_bits n f then forall bs, f bs = true else exists bs, f bs = false.
Proof.
  induction n; simpl.
  - intros. destruct (f Ob) eqn:F; eauto.
    now intros [].
  - intros.
    specialize (IHn (fun bs => f bs~0)) as IHn0.
    specialize (IHn (fun bs => f bs~1)) as IHn1.
    destruct (forallb_bits _); simpl; [|des; eauto].
    destruct (forallb_bits _); [|des; eauto].
    intros ([|] & tl); eauto.
Qed.

Lemma forall_exists_comm_bits {n T P}
  (FORALL : forall bs : bits n, exists t : T, P bs t) :
  exists f, forall bs, P bs (f bs).
Proof.
  induction n. { specialize (FORALL Ob). des. exists (fun _ => t). now intros []. }
  exploit (IHn (fun bs => P bs~0)); eauto.
  exploit (IHn (fun bs => P bs~1)); eauto.
  intros [f1 ?] [f0 ?].
  exists (fun bs : bits (S n) => if vect_hd bs then f1 (vect_tl bs) else f0 (vect_tl bs)).
  intros ([|] & tl); eauto.
Qed.

Lemma dec_forall_bits {n P} (FORALL : forall bs : bits n, P bs \/ ~ P bs) :
  (forall bs, P bs) \/ (exists bs, ~ P bs).
Proof.
  induction n.
  { specialize (FORALL Ob). des; [left; now intros [] | right; eauto]. }
  exploit (IHn (fun bs => P bs~0)); eauto.
  exploit (IHn (fun bs => P bs~1)); eauto.
  intros; des; eauto.
  left. intros ([|] & tl); eauto.
Qed.

