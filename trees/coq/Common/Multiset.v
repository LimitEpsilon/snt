From Stdlib Require Import Utf8 Program.Basics.
From Koika Require Import Common GMap Environments IndexUtils.

Local Generalizable All Variables.

Section multiset.
  (* in case we inferred a different EqDec class *)
  Lemma count_occ_irrel {T} {l : list T} :
    forall t eq1 eq2, count_occ eq1 l t = count_occ eq2 l t.
  Proof.
    induction l; simpl; auto.
    intros. destruct (eq1 a t); subst.
    rewrite (@eq_dec_refl _ {| eq_dec := eq2 |}). auto.
    destruct (eq2 a t); subst; auto; contradiction.
  Qed.

  Context `{Ok : Countable T}.

  Definition multiset := gmap T positive.

  Definition multiplicity (m : multiset) x :=
    match get m x with
    | Some p => Pos.to_nat p
    | None => 0
    end%nat.

  Definition cardinality : multiset -> nat :=
    fold (fun acc _ mul => Pos.to_nat mul + acc)%nat 0%nat
  .

  Definition mincr (m : multiset) x : multiset := alter m x (fun x =>
    match x with None => Some xH | Some p => Some (Pos.succ p) end
  ).

  Definition madd (m : multiset) x p : multiset := alter m x (fun x =>
    match x with None => Some p | Some q => Some (p + q) end
  )%positive.

  Definition mdecr (m : multiset) x : multiset := alter m x (fun x =>
    match x with None | Some xH => None | Some p => Some (Pos.pred p) end
  ).

  Definition msub (m : multiset) x p : multiset := alter m x (fun x =>
    match x with
    | None => None
    | Some q => if q <=? p then None else Some (q - p)
    end)%positive.

  Definition singleton x : multiset := mincr empty x.

  Definition union (m : multiset) l : multiset := List.fold_left mincr l m.

  Definition diff (m : multiset) l : multiset := List.fold_left mdecr l m.

  Definition of_list l : multiset := union empty l.

  Definition to_list (m : multiset) := fold (fun acc k mul =>
    repeat k (Pos.to_nat mul) ++ acc
  )%list [] m.

  Definition munion : multiset -> multiset -> multiset := fold madd.

  Definition mdiff : multiset -> multiset -> multiset := fold msub.

  Definition minter (m1 : multiset) (m2 : multiset) : multiset := fold (fun acc k p =>
    match get m1 k with
    | None => acc
    | Some q => put acc k (Pos.min p q)
    end
  ) empty m2.

  Definition mmax (m1 : multiset) (m2 : multiset) : multiset := fold (fun acc k p =>
    match get acc k with
    | None => put acc k p
    | Some q => put acc k (Pos.max p q)
    end
  ) m1 m2.

  Definition mfilter (P : _ -> bool) : multiset -> multiset := fold (fun acc k v =>
    if P k then madd acc k v else acc
  ) empty.

  Definition union_nil {m} : union m [] = m := eq_refl.

  Definition union_cons {m x l} : union m (x :: l) = union (mincr m x) l := eq_refl.

  Definition diff_nil {m} : diff m [] = m := eq_refl.

  Definition diff_cons {m x l} : diff m (x :: l) = diff (mdecr m x) l := eq_refl.

  Lemma multiplicity_ext {m1 m2} :
    (forall x, multiplicity m1 x = multiplicity m2 x) ->
    m1 = m2.
  Proof.
    intro EQ. apply gmap_ext. intros.
    specialize (EQ k). unfold multiplicity in EQ.
    destruct (get m1 k), (get m2 k);
      solve [f_equal; auto using Pnat.Pos2Nat.inj|lia].
  Qed.

  Lemma multiplicity_empty {x} : multiplicity empty x = 0%nat.
  Proof.
    cbv [multiplicity]. rewrite get_empty. auto.
  Qed.

  Lemma multiplicity_nonempty m : m <> empty -> exists x, multiplicity m x <> 0.
  Proof.
    destruct m. contradiction.
    intros _. specialize (get_nonempty m).
    intros (x & GET).
    exists x. unfold multiplicity. simpl.
    destruct (get' _ _); auto.
    lia.
  Qed.

  Lemma multiplicity_mincr_same {m x} :
    multiplicity (mincr m x) x = S (multiplicity m x).
  Proof.
    cbv [multiplicity mincr]. rewrite get_alter_same. destruct (get m x); lia.
  Qed.

  Lemma multiplicity_mincr_diff {m x y} (NEQ : x ≠ y) :
    multiplicity (mincr m y) x = multiplicity m x.
  Proof.
    cbv [multiplicity mincr]. rewrite get_alter_diff; auto.
  Qed.

  Lemma multiplicity_mincr {m x y} :
    multiplicity (mincr m y) x =
    if eq_dec y x then S (multiplicity m x) else multiplicity m x.
  Proof.
    destruct (eq_dec y x); subst; auto using multiplicity_mincr_same, multiplicity_mincr_diff.
  Qed.

  Lemma multiplicity_madd_same {m x p} :
    multiplicity (madd m x p) x = Pos.to_nat p + (multiplicity m x).
  Proof.
    cbv [multiplicity madd]. rewrite get_alter_same. destruct (get m x); lia.
  Qed.

  Lemma multiplicity_madd_diff {m x y p} (NEQ : x ≠ y) :
    multiplicity (madd m y p) x = multiplicity m x.
  Proof.
    cbv [multiplicity madd]. rewrite get_alter_diff; auto.
  Qed.

  Lemma multiplicity_madd {m x y p} :
    multiplicity (madd m y p) x =
    if eq_dec y x then Pos.to_nat p + multiplicity m x else multiplicity m x.
  Proof.
    destruct (eq_dec y x); subst; auto using multiplicity_madd_same, multiplicity_madd_diff.
  Qed.

  Lemma multiplicity_mdecr_same {m x} :
    multiplicity (mdecr m x) x = pred (multiplicity m x).
  Proof.
    cbv [multiplicity mdecr]. rewrite get_alter_same.
    destruct (get m x) as [[ | | ]|]; lia.
  Qed.

  Lemma multiplicity_mdecr_diff {m x y} (NEQ : x ≠ y) :
    multiplicity (mdecr m y) x = multiplicity m x.
  Proof.
    cbv [multiplicity mdecr]. rewrite get_alter_diff; auto.
  Qed.

  Lemma multiplicity_mdecr {m x y} :
    multiplicity (mdecr m y) x =
    if eq_dec y x then Nat.pred (multiplicity m x) else multiplicity m x.
  Proof.
    destruct (eq_dec y x); subst; auto using multiplicity_mdecr_same, multiplicity_mdecr_diff.
  Qed.

  Lemma multiplicity_msub_same {m x p} :
    multiplicity (msub m x p) x = multiplicity m x - (Pos.to_nat p).
  Proof.
    cbv [multiplicity msub]. rewrite get_alter_same. destruct (get m x); try lia.
    destruct (_ <=? _)%positive eqn:?;
      [rewrite Pos.leb_le in *|rewrite Pos.leb_gt in *]; lia.
  Qed.

  Lemma multiplicity_msub_diff {m x y p} (NEQ : x ≠ y) :
    multiplicity (msub m y p) x = multiplicity m x.
  Proof.
    cbv [multiplicity msub]. rewrite get_alter_diff; auto.
  Qed.

  Lemma multiplicity_msub {m x y p} :
    multiplicity (msub m y p) x =
    if eq_dec y x then multiplicity m x - Pos.to_nat p else multiplicity m x.
  Proof.
    destruct (eq_dec y x); subst; auto using multiplicity_msub_same, multiplicity_msub_diff.
  Qed.

  Lemma multiplicity_singleton_same {x} : multiplicity (singleton x) x = 1.
  Proof.
    unfold singleton. now rewrite multiplicity_mincr_same, multiplicity_empty.
  Qed.

  Lemma multiplicity_singleton_diff {x y} (NEQ : x ≠ y) :
    multiplicity (singleton x) y = 0.
  Proof.
    unfold singleton. now rewrite multiplicity_mincr_diff, multiplicity_empty by auto.
  Qed.

  Lemma multiplicity_singleton {x y} :
    multiplicity (singleton y) x =
    if eq_dec y x then 1 else 0.
  Proof.
    destruct (eq_dec y x); subst; auto using multiplicity_singleton_same, multiplicity_singleton_diff.
  Qed.

  Lemma multiplicity_union {m l} :
    forall x, multiplicity (union m l) x = multiplicity m x + count_occ eq_dec l x.
  Proof.
    revert m. induction l; auto.
    intros. rewrite union_cons. rewrite IHl.
    cbn - [eq_dec].
    destruct (eq_dec a x); subst.
    - rewrite multiplicity_mincr_same. lia.
    - rewrite multiplicity_mincr_diff; auto.
  Qed.

  Lemma multiplicity_diff {m l} :
    forall x, multiplicity (diff m l) x = multiplicity m x - count_occ eq_dec l x.
  Proof.
    revert m. induction l. simpl; lia.
    intros. rewrite diff_cons. rewrite IHl.
    cbn - [eq_dec].
    destruct (eq_dec a x); subst.
    - rewrite multiplicity_mdecr_same. lia.
    - rewrite multiplicity_mdecr_diff; auto.
  Qed.

  Lemma multiplicity_of_list l :
    forall x, multiplicity (of_list l) x = count_occ eq_dec l x.
  Proof.
    intros. unfold of_list. rewrite multiplicity_union, multiplicity_empty. auto.
  Qed.

  Lemma count_occ_to_list m :
    forall x, count_occ eq_dec (to_list m) x = multiplicity m x.
  Proof.
    unfold to_list. eapply fold_spec.
    - intros. unshelve erewrite multiplicity_empty; eauto.
    - intros. rewrite count_occ_app.
      destruct (eq_dec i x); subst.
      + rewrite count_occ_repeat_eq; auto.
        unfold multiplicity. rewrite get_put_same.
        rewrite IHfold. unfold multiplicity. rewrite Hget. auto.
      + rewrite count_occ_repeat_neq; auto.
        unfold multiplicity. rewrite get_put_diff; auto.
        apply IHfold.
  Qed.

  Lemma of_list_to_list m : of_list (to_list m) = m.
  Proof.
    apply multiplicity_ext. intros. rewrite multiplicity_of_list.
    apply count_occ_to_list.
  Qed.

  Lemma to_list_of_list {l x} :
    count_occ eq_dec (to_list (of_list l)) x = count_occ eq_dec l x.
  Proof.
    repeat rewrite <- multiplicity_of_list.
    rewrite of_list_to_list. reflexivity.
  Qed.

  Lemma multiplicity_munion {m1 m2} :
    forall x, multiplicity (munion m1 m2) x = multiplicity m1 x + multiplicity m2 x.
  Proof.
    intros; unfold munion.
    apply fold_spec. { rewrite multiplicity_empty. lia. }
    intros. destruct (eq_dec i x); subst.
    - rewrite multiplicity_madd_same, IHfold.
      unfold multiplicity.
      rewrite get_put_same, Hget. lia.
    - rewrite multiplicity_madd_diff by auto.
      rewrite IHfold.
      unfold multiplicity.
      rewrite get_put_diff; auto.
  Qed.

  Lemma multiplicity_mdiff {m1 m2} :
    forall x, multiplicity (mdiff m1 m2) x = multiplicity m1 x - multiplicity m2 x.
  Proof.
    intros; unfold mdiff.
    apply fold_spec. { rewrite multiplicity_empty. lia. }
    intros. destruct (eq_dec i x); subst.
    - rewrite multiplicity_msub_same, IHfold.
      unfold multiplicity.
      rewrite get_put_same, Hget. lia.
    - rewrite multiplicity_msub_diff by auto.
      rewrite IHfold.
      unfold multiplicity.
      rewrite get_put_diff; auto.
  Qed.

  Lemma multiplicity_minter {m1 m2} :
    forall x, multiplicity (minter m1 m2) x = min (multiplicity m1 x) (multiplicity m2 x).
  Proof.
    intros; unfold minter.
    apply fold_spec. { rewrite multiplicity_empty. lia. }
    intros. destruct (eq_dec i x); subst.
    - unfold multiplicity.
      rewrite get_put_same.
      destruct (get m1 x) eqn:Hget'.
      rewrite get_put_same. lia.
      unfold multiplicity in IHfold. rewrite Hget, Hget' in IHfold.
      auto.
    - unfold multiplicity.
      rewrite get_put_diff by auto.
      destruct (get m1 i) eqn: Hget'; auto.
      now rewrite get_put_diff by auto.
  Qed.

  Lemma multiplicity_mmax {m1 m2} :
    forall x, multiplicity (mmax m1 m2) x = max (multiplicity m1 x) (multiplicity m2 x).
  Proof.
    intros; unfold mmax.
    apply fold_spec. { rewrite multiplicity_empty. lia. }
    intros. destruct (eq_dec i x); subst.
    - unfold multiplicity.
      rewrite get_put_same.
      destruct (get m1 x) eqn:Hget';
      unfold multiplicity in IHfold; rewrite Hget, Hget' in IHfold.
      all: destruct (get r x); try rewrite get_put_same; lia.
    - unfold multiplicity in *.
      rewrite get_put_diff by auto. rewrite <- IHfold.
      destruct (get r i); now rewrite get_put_diff by auto.
  Qed.

  Lemma multiplicity_mfilter {P m} :
    forall x, multiplicity (mfilter P m) x = if P x then multiplicity m x else 0.
  Proof.
    unfold mfilter. apply fold_spec.
    { intros. rewrite multiplicity_empty. destruct (P x); auto. }
    clear m. intros. destruct (eq_dec i x); subst.
    - destruct (P x) eqn:HPx.
      rewrite multiplicity_madd_same.
      unfold multiplicity at 2. rewrite get_put_same, IHfold, HPx.
      unfold multiplicity. rewrite Hget. lia.
      rewrite IHfold. rewrite HPx. auto.
    - destruct (P i); repeat rewrite multiplicity_madd_diff by auto;
      unfold multiplicity at 2; rewrite get_put_diff by auto.
      all: apply IHfold.
  Qed.

  Lemma union_to_munion {m l} : union m l = munion m (of_list l).
  Proof.
    apply multiplicity_ext. intros.
    now rewrite multiplicity_union, multiplicity_munion, multiplicity_of_list.
  Qed.

  Lemma diff_to_mdiff {m l} : diff m l = mdiff m (of_list l).
  Proof.
    apply multiplicity_ext. intros.
    now rewrite multiplicity_diff, multiplicity_mdiff, multiplicity_of_list.
  Qed.

  Lemma mincr_mincr m x y :
    mincr (mincr m x) y = mincr (mincr m y) x.
  Proof.
    apply multiplicity_ext. intro k.
    destruct (eq_dec x k), (eq_dec y k); subst;
    now repeat first
      [rewrite multiplicity_mincr_same|rewrite multiplicity_mincr_diff by auto].
  Qed.

  Lemma union_mincr m x y :
    union (mincr m x) y = mincr (union m y) x.
  Proof.
    apply multiplicity_ext. intro k.
    destruct (eq_dec x k); subst;
    now repeat first
      [rewrite multiplicity_union|
       rewrite multiplicity_mincr_same|
       rewrite multiplicity_mincr_diff by auto].
  Qed.

  Lemma union_union m x y :
    union (union m x) y = union (union m y) x.
  Proof.
    apply multiplicity_ext. intro k.
    repeat rewrite multiplicity_union. lia.
  Qed.

  Lemma cardinality_spec {m} : cardinality m = List.length (to_list m).
  Proof.
    unfold cardinality, to_list.
    apply (@fold_parametricity _ _ _ nat (list T)); auto.
    intros; subst.
    rewrite List.length_app, repeat_length. auto.
  Qed.

  Lemma cardinality_singleton {m} : cardinality m = 1 → ∃ x, m = of_list [x].
  Proof.
    rewrite cardinality_spec.
    destruct (to_list m) as [|hd tl] eqn:EQ. inversion 1.
    destruct tl. 2: inversion 1. intros.
    rewrite <- (of_list_to_list m), EQ. eauto.
  Qed.

  Lemma cardinality_empty {m} : cardinality m = 0 → m = empty.
  Proof.
    rewrite cardinality_spec.
    destruct (to_list m) eqn:EQ. 2: inversion 1.
    intros. rewrite <- (of_list_to_list m), EQ. auto.
  Qed.

  Lemma vect_fold_left_union :
    ∀ sz (v : vect _ sz) i s,
      vect_fold_left union s v =
      union (vect_fold_left union s (vect_replace v i [])) (vect_nth v i).
  Proof.
    induction sz. { intros _ []. }
    intros (hd & tl) [|idx] s; simpl; auto.
    rewrite (IHsz _ idx).
    apply multiplicity_ext. intros.
    repeat rewrite multiplicity_union. lia.
  Qed.

  Lemma vect_fold_left_munion :
    ∀ sz (v : vect _ sz) i s,
      vect_fold_left munion s v =
      munion (vect_fold_left munion s (vect_replace v i empty)) (vect_nth v i).
  Proof.
    induction sz. { intros _ []. }
    intros (hd & tl) [|idx] s; simpl; auto.
    rewrite (IHsz _ idx).
    apply multiplicity_ext. intros.
    repeat rewrite multiplicity_munion. lia.
  Qed.

  (* deq *)
  Lemma mincr_cons :
    ∀ hd tl, mincr (of_list tl) hd = of_list (hd :: tl).
  Proof.
    intros. apply multiplicity_ext. intros x.
    rewrite multiplicity_of_list.
    cbn - [eq_dec]. destruct (eq_dec hd x); subst.
    - rewrite multiplicity_mincr_same, multiplicity_of_list. auto.
    - rewrite multiplicity_mincr_diff by auto. rewrite multiplicity_of_list. auto.
  Qed.

  Lemma of_list_app l1 l2 :
    of_list (l1 ++ l2) = munion (of_list l1) (of_list l2).
  Proof.
    apply multiplicity_ext. intros.
    rewrite multiplicity_of_list, multiplicity_munion, count_occ_app.
    now repeat rewrite multiplicity_of_list.
  Qed.

  (* enq *)
  Lemma mincr_snoc :
    ∀ tl l, mincr (of_list l) tl = of_list (l ++ [tl]).
  Proof.
    intros. apply multiplicity_ext. intros.
    rewrite multiplicity_of_list, count_occ_app.
    cbn - [eq_dec]. destruct (eq_dec tl x); subst.
    - rewrite multiplicity_mincr_same, multiplicity_of_list. lia.
    - rewrite multiplicity_mincr_diff by auto. rewrite multiplicity_of_list. lia.
  Qed.

  Lemma mincr_spec m x :
    mincr m x = of_list (x :: to_list m).
  Proof.
    rewrite <- (of_list_to_list m).
    rewrite mincr_cons. now rewrite of_list_to_list.
  Qed.

  Lemma mIn_In m x :
    multiplicity m x > 0 ↔ In x (to_list m).
  Proof.
    rewrite count_occ_In, count_occ_to_list. reflexivity.
  Qed.

  Lemma mIn_munion m1 m2 x :
    multiplicity (munion m1 m2) x > 0 ↔ (multiplicity m1 x > 0 ∨ multiplicity m2 x > 0).
  Proof.
    rewrite multiplicity_munion. lia.
  Qed.

  Lemma mIn_alt m x :
    multiplicity m x > 0 ↔ ∃ m', m = mincr m' x.
  Proof.
    split; intro IN.
    - exists (mdecr m x). apply multiplicity_ext.
      intro y. rewrite multiplicity_mincr, multiplicity_mdecr.
      destruct (eq_dec x y); subst; lia.
    - des; subst. rewrite multiplicity_mincr_same. lia.
  Qed.

  Lemma mForall_Forall m P :
    (∀ x (IN : multiplicity m x > 0), P x) ↔ Forall P (to_list m).
  Proof.
    rewrite Forall_forall. setoid_rewrite mIn_In. reflexivity.
  Qed.

  Lemma Forall_munion m1 m2 P :
    Forall P (to_list (munion m1 m2)) ↔ (Forall P (to_list m1) ∧ Forall P (to_list m2)).
  Proof.
    repeat rewrite <- mForall_Forall.
    setoid_rewrite mIn_munion.
    intuition auto.
  Qed.

  Lemma Forall_to_list_of_list l P :
    Forall P (to_list (of_list l)) ↔ Forall P l.
  Proof.
    rewrite <- mForall_Forall.
    setoid_rewrite multiplicity_of_list. setoid_rewrite <- count_occ_In.
    symmetry. apply Forall_forall.
  Qed.

  Lemma munion_singleton m x : munion (singleton x) m = mincr m x.
  Proof.
    apply multiplicity_ext. intro y. rewrite multiplicity_munion.
    unfold singleton.
    destruct (eq_dec x y); subst.
    - repeat rewrite multiplicity_mincr_same. now rewrite multiplicity_empty.
    - repeat rewrite multiplicity_mincr_diff by auto.
      now rewrite multiplicity_empty.
  Qed.

  Lemma madd_spec m x v :
    madd m x v = of_list (repeat x (Pos.to_nat v) ++ to_list m).
  Proof.
    apply multiplicity_ext. intro y.
    rewrite multiplicity_of_list, count_occ_app.
    destruct (eq_dec x y); subst.
    now rewrite multiplicity_madd_same, count_occ_repeat_eq, count_occ_to_list.
    now rewrite multiplicity_madd_diff, count_occ_repeat_neq, count_occ_to_list by auto.
  Qed.

  Lemma munion_spec m1 m2 :
    munion m1 m2 = of_list (to_list m1 ++ to_list m2).
  Proof.
    apply multiplicity_ext.
    intros. rewrite multiplicity_munion, multiplicity_of_list, count_occ_app.
    now repeat rewrite count_occ_to_list.
  Qed.

  Lemma munion_comm m1 m2 : munion m1 m2 = munion m2 m1.
  Proof.
    apply multiplicity_ext. intros. repeat rewrite multiplicity_munion.
    apply Nat.add_comm.
  Qed.

  Lemma munion_assoc m1 m2 m3 :
    munion m1 (munion m2 m3) = munion (munion m1 m2) m3.
  Proof.
    apply multiplicity_ext. intros. repeat rewrite multiplicity_munion.
    apply Nat.add_assoc.
  Qed.

  Lemma multiplicity_In :
    ∀ x l, multiplicity (of_list l) x > 0 ↔ In x l.
  Proof.
    intros. rewrite multiplicity_of_list. symmetry. apply count_occ_In.
  Qed.

  Lemma mfilter_of_list {P} l :
    mfilter P (of_list l) = of_list (filter P l).
  Proof.
    apply multiplicity_ext. intros.
    rewrite multiplicity_mfilter.
    repeat rewrite multiplicity_of_list.
    induction l; cbn - [eq_dec].
    - destruct (P x); auto.
    - destruct (eq_dec a x); subst.
      + destruct (P x); cbn - [eq_dec]; auto.
        rewrite eq_dec_refl; now f_equal.
      + destruct (P x); destruct (P a); cbn - [eq_dec]; auto.
        all: rewrite <- IHl.
        all: destruct (eq_dec a x); subst; try contradiction; auto.
  Qed.

  Lemma mfilter_spec {P} m :
    mfilter P m = of_list (filter P (to_list m)).
  Proof.
    rewrite <- (of_list_to_list m) at 1. apply mfilter_of_list.
  Qed.

  Lemma mfilter_mincr {P} m k :
    mfilter P (mincr m k) = if P k then mincr (mfilter P m) k else mfilter P m.
  Proof.
    apply multiplicity_ext; intros.
    rewrite multiplicity_mfilter.
    destruct (eq_dec k x); subst.
    - rewrite multiplicity_mincr_same. destruct (P x) eqn:HPx.
      now rewrite multiplicity_mincr_same, multiplicity_mfilter, HPx.
      now rewrite multiplicity_mfilter, HPx.
    - rewrite multiplicity_mincr_diff by auto. destruct (P k).
      now rewrite multiplicity_mincr_diff, multiplicity_mfilter by auto.
      now rewrite multiplicity_mfilter.
  Qed.

  Lemma mfilter_madd {P} m k v :
    mfilter P (madd m k v) = if P k then madd (mfilter P m) k v else mfilter P m.
  Proof.
    apply multiplicity_ext; intros.
    rewrite multiplicity_mfilter.
    destruct (eq_dec k x); subst.
    - rewrite multiplicity_madd_same. destruct (P x) eqn:HPx.
      now rewrite multiplicity_madd_same, multiplicity_mfilter, HPx.
      now rewrite multiplicity_mfilter, HPx.
    - rewrite multiplicity_madd_diff by auto. destruct (P k).
      now rewrite multiplicity_madd_diff, multiplicity_mfilter by auto.
      now rewrite multiplicity_mfilter.
  Qed.

  Lemma mfilter_munion {P} m1 m2 :
    mfilter P (munion m1 m2) = munion (mfilter P m1) (mfilter P m2).
  Proof.
    apply multiplicity_ext; intros.
    rewrite multiplicity_mfilter.
    repeat rewrite multiplicity_munion.
    repeat rewrite multiplicity_mfilter.
    destruct (P x); lia.
  Qed.

  Lemma permutation_length_filter_same {l1 l2 P} :
    (∀ x : T, count_occ eq_dec l1 x = count_occ eq_dec l2 x) →
    List.length (filter P l1) = List.length (filter P l2).
  Proof.
    revert l2.
    remember (List.length l1) as n.
    revert l1 Heqn. pose proof (lt_wf n) as ACC.
    induction ACC. clear H0. rename H1 into IH, x into n.
    destruct l1 as [|hd tl]; intros; simpl in Heqn; try congruence.
    - assert (l2 = []).
      { rewrite <- count_occ_inv_nil; intros; rewrite <- H0; auto. }
      subst; auto.
    - intros. destruct n as [|n]. inversion Heqn.
      apply Nat.succ_inj in Heqn.
      specialize (H0 hd) as IN.
      cbn - [eq_dec] in IN. rewrite eq_dec_refl in IN.
      specialize (Nat.lt_0_succ (count_occ eq_dec tl hd)).
      rewrite IN. intro IN'. apply count_occ_In in IN'.
      apply in_split in IN'.
      des; subst.
      assert (∀ x, count_occ eq_dec tl x = count_occ eq_dec (l1 ++ l0) x).
      { intros. specialize (H0 x). rewrite count_occ_app in H0. cbn - [eq_dec] in H0.
        destruct (eq_dec hd x); subst; rewrite count_occ_app; auto.
        rewrite Nat.add_succ_r in H0. apply Nat.succ_inj in H0. auto. }
      rewrite filter_app, List.length_app; simpl. destruct (P hd).
      + simpl. rewrite Nat.add_succ_r. f_equal.
        rewrite <- List.length_app, <- filter_app.
        eapply IH; eauto.
      + rewrite <- List.length_app, <- filter_app.
        eapply IH; eauto.
  Qed.

  Lemma permutation_length_same {l1 l2} :
    (∀ x : T, count_occ eq_dec l1 x = count_occ eq_dec l2 x) →
    List.length l1 = List.length l2.
  Proof.
    intros.
    rewrite <- (filter_true l1), <- (filter_true l2).
    now apply permutation_length_filter_same.
  Qed.

  Lemma length_filter_to_list_of_list {P l} :
    List.length (filter P (to_list (of_list l))) = List.length (filter P l).
  Proof.
    apply permutation_length_filter_same.
    intros. now rewrite count_occ_to_list, multiplicity_of_list.
  Qed.

  Lemma length_to_list_of_list {l} :
    List.length (to_list (of_list l)) = List.length l.
  Proof.
    rewrite <- (filter_true (to_list (of_list l))).
    now rewrite length_filter_to_list_of_list, filter_true.
  Qed.

  Lemma partition_spec f l :
    of_list l =
    munion (of_list (filter f l)) (of_list (filter (fun x => negb (f x)) l)).
  Proof.
    apply multiplicity_ext. intros.
    rewrite multiplicity_munion. repeat rewrite multiplicity_of_list.
    induction l; cbn - [eq_dec]; auto.
    destruct (f a); cbn - [eq_dec]; destruct (eq_dec _ _); now rewrite IHl.
  Qed.

  Lemma mpartition_spec f m :
    m = munion (mfilter f m) (mfilter (fun x => negb (f x)) m).
  Proof.
    repeat rewrite mfilter_spec.
    rewrite <- (of_list_to_list m) at 1.
    apply partition_spec.
  Qed.

  Lemma cardinality_mincr {m x} : cardinality (mincr m x) = S (cardinality m).
  Proof.
    repeat rewrite cardinality_spec.
    assert (mincr m x = of_list (x :: to_list m)) as ->.
    { apply multiplicity_ext. intro y.
      now rewrite <- mincr_cons, of_list_to_list. }
    change (S _) with (List.length (x :: to_list m)).
    apply permutation_length_same.
    intro y. now rewrite count_occ_to_list, multiplicity_of_list.
  Qed.

  Lemma cardinality_madd {m x v} :
    cardinality (madd m x v) = Pos.to_nat v + cardinality m.
  Proof.
    repeat rewrite cardinality_spec.
    now rewrite madd_spec, length_to_list_of_list, List.length_app, repeat_length.
  Qed.

  Lemma cardinality_munion m1 m2 :
    cardinality (munion m1 m2) = cardinality m1 + cardinality m2.
  Proof.
    rewrite cardinality_spec, munion_spec, length_to_list_of_list, List.length_app.
    f_equal; now rewrite cardinality_spec.
  Qed.

  Lemma cardinality_of_list {l} : cardinality (of_list l) = List.length l.
  Proof.
    induction l; simpl; auto.
    rewrite <- mincr_cons, cardinality_mincr.
    f_equal; auto.
  Qed.

  Lemma multiset_ind (P : multiset → Prop)
    (Hempty : P empty) (Hincr : ∀ m x (IHm : P m), P (mincr m x)) :
    ∀ m, P m.
  Proof.
    intro. remember (cardinality m). generalize dependent m.
    induction n; intros; symmetry in Heqn.
    - apply cardinality_empty in Heqn. subst; auto.
    - rewrite cardinality_spec in Heqn.
      destruct (to_list m) eqn:EQ. { inversion Heqn. }
      assert (m = mincr (of_list l) t).
      { now rewrite mincr_cons, <- EQ, of_list_to_list. }
      subst. apply Hincr, IHn. cbn [List.length] in Heqn.
      apply Nat.succ_inj in Heqn. subst.
      symmetry. apply cardinality_of_list.
  Qed.

  #[export] Instance EqDecMultiset : EqDec multiset := _.
End multiset.

#[global] Arguments multiset _ {_ _}.

Definition mmap `{Ok : Countable T} `{Ok' : Countable T'} (f : T -> T') :
  multiset T -> multiset T' :=
  fold (fun acc k mul => madd acc (f k) mul) empty
.

Lemma mmap_spec `{Ok : Countable T} `{Ok' : Countable T'} (f : T -> T') (m : multiset T) :
  mmap f m = of_list (map f (to_list m)).
Proof.
  unfold mmap, to_list.
  apply fold_parametricity with
    (fa := fun acc k mul => madd acc (f k) mul)
    (fb := fun acc k mul => (repeat k (Pos.to_nat mul) ++ acc)%list); auto.
  intros; subst.
  rewrite map_app, map_repeat.
  apply multiplicity_ext.
  intros.
  rewrite multiplicity_of_list, count_occ_app.
  destruct (eq_dec (f i) x); subst.
  - rewrite multiplicity_madd_same, count_occ_repeat_eq by auto.
    f_equal. apply multiplicity_of_list.
  - rewrite multiplicity_madd_diff, count_occ_repeat_neq by auto.
    apply multiplicity_of_list.
Qed.

Lemma multiplicity_mmap `{Ok : Countable T} `{Ok' : Countable T'} f (m : multiset T) x :
  multiplicity (mmap f m) x =
  cardinality (mfilter (fun t => beq_dec (f t) x) m).
Proof.
  unfold mmap, mfilter.
  apply fold_parametricity with
    (fa := fun acc k mul => madd acc (f k) mul)
    (fb := fun acc k v => if beq_dec (f k) x then madd acc k v else acc); auto.
  clear m. intros. unfold beq_dec. destruct (eq_dec _ _); subst.
  - now rewrite multiplicity_madd_same, REL, cardinality_madd.
  - now rewrite multiplicity_madd_diff, REL by auto.
Qed.

Lemma mmap_mmap `{Ok : Countable T} `{Ok' : Countable T'} `{Ok'' : Countable T''}
  (f : T' → T'') (g : T → T') (m : multiset T) :
  mmap f (mmap g m) = mmap (fun x => f (g x)) m.
Proof.
  intros. apply multiplicity_ext.
  intros. repeat rewrite multiplicity_mmap.
  repeat rewrite cardinality_spec, mfilter_spec.
  rewrite mmap_spec. generalize (to_list m). clear m.
  intros.
  repeat rewrite length_to_list_of_list.
  rewrite length_filter_to_list_of_list.
  now rewrite filter_map_swap, length_map.
Qed.

Lemma mmap_ext `{Ok : Countable T} `{Ok' : Countable T'} f g (m : multiset T) :
  (∀ x, f x = g x) → mmap f m = mmap g m.
Proof.
  intros EXT.
  unfold mmap. apply fold_parametricity; auto.
  intros. subst; now rewrite EXT.
Qed.

Lemma mmap_id `{Ok : Countable T} (m : multiset T) : mmap id m = m.
Proof.
  now rewrite mmap_spec, map_id, of_list_to_list.
Qed.

Lemma mmap_mincr `{Ok : Countable T} `{Ok' : Countable T'} f (m : multiset T) x :
  mmap f (mincr m x) = mincr (mmap f m) (f x).
Proof.
  apply multiplicity_ext. intro y.
  rewrite multiplicity_mmap, cardinality_spec, mfilter_spec, length_to_list_of_list.
  rewrite <- (of_list_to_list m), mincr_cons.
  rewrite length_filter_to_list_of_list.
  simpl. unfold beq_dec. destruct (eq_dec _ _); subst.
  - rewrite multiplicity_mincr_same. cbn [List.length].
    f_equal.
    rewrite multiplicity_mmap, cardinality_spec, mfilter_spec, of_list_to_list.
    now rewrite length_to_list_of_list.
  - rewrite multiplicity_mincr_diff by auto.
    rewrite multiplicity_mmap, cardinality_spec, mfilter_spec, of_list_to_list.
    now rewrite length_to_list_of_list.
Qed.

Lemma count_occ_map `{Ok : Countable T} `{Ok' : Countable T'} (f : T -> T')
  (l : list T) x :
  count_occ eq_dec (map f l) x =
  List.length (filter (fun t => beq_dec (f t) x) l).
Proof.
  induction l; cbn - [eq_dec]; auto.
  unfold beq_dec. destruct (eq_dec _ _); subst; auto.
  cbn - [eq_dec]; f_equal; auto.
Qed.

Lemma mmap_munion `{Ok : Countable T} `{Ok' : Countable T'} f (m1 m2 : multiset T) :
  mmap f (munion m1 m2) = munion (mmap f m1) (mmap f m2).
Proof.
  apply multiplicity_ext.
  intros. rewrite multiplicity_mmap. repeat rewrite munion_spec.
  rewrite multiplicity_of_list, count_occ_app, mfilter_spec.
  rewrite cardinality_spec.
  rewrite length_to_list_of_list, length_filter_to_list_of_list.
  rewrite filter_app, List.length_app.
  now repeat rewrite mmap_spec, to_list_of_list, count_occ_map.
Qed.

Lemma mmap_of_list `{Ok : Countable T} `{Ok' : Countable T'} (f : T -> T') l :
  mmap f (of_list l) = of_list (map f l).
Proof.
  rewrite mmap_spec. apply multiplicity_ext. intros.
  repeat rewrite multiplicity_of_list, count_occ_map.
  apply permutation_length_filter_same.
  intros.
  now rewrite <- multiplicity_of_list, of_list_to_list, multiplicity_of_list.
Qed.
