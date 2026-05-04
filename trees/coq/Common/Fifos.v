From Stdlib Require Import Utf8 Program.Basics.
From Koika Require Import Common GMap Environments IndexUtils.

Local Open Scope program_scope.
Local Generalizable All Variables.

Section fifos.
  Context `{Ok : Countable fifo_key} {V : Type}.
  Definition fifos := gmap fifo_key (V * list V).
  Definition get_fifos f k : list V :=
    match get f k with
    | Some (hd, tl) => hd :: tl
    | None => []
    end.
  Definition put_fifos f k l : fifos :=
    match l with
    | [] => remove f k
    | hd :: tl => put f k (hd, tl)
    end.
  Definition enq_fifos (f : fifos) k v : fifos :=
    alter f k (fun x => Some
      match x with
      | Some (hd, tl) => (hd, tl ++ [v])
      | None => (v, [])
      end
    ).
  Definition cons_fifos (f : fifos) k v : fifos :=
    alter f k (fun x => Some
      match x with
      | Some (hd, tl) => (v, hd :: tl)
      | None => (v, [])
      end
    ).
  Definition deq_fifos (f : fifos) k : option (V * fifos) :=
    match get f k with
    | Some (hd, tl) => Some (hd,
      match tl with [] => remove f k | hd' :: tl' => put f k (hd', tl') end)
    | None => None
    end.
  Lemma fifos_ext x y (EXT : ∀ k, get_fifos x k = get_fifos y k) : x = y.
  Proof.
    apply gmap_ext. intros. specialize (EXT k).
    unfold get_fifos in *.
    destruct (get x k) as [[??]|], (get y k) as [[??]|];
      inversion EXT; subst; auto.
  Qed.
  Lemma get_fifos_empty k : get_fifos empty k = [].
  Proof. reflexivity. Qed.
  Lemma get_fifos_nonempty m : m <> empty -> exists k, get_fifos m k <> [].
  Proof.
    destruct m. intros. contradiction.
    intros _.
    specialize (get_nonempty m). intros (k & GET).
    exists k.
    unfold get_fifos.
    simpl. destruct (get' _ _); auto.
    destruct p. inversion 1.
  Qed.
  Lemma put_fifos_same f k v :
    get_fifos (put_fifos f k v) k = v.
  Proof.
    unfold get_fifos, put_fifos.
    destruct v.
    - now rewrite get_remove_same.
    - now rewrite get_put_same by auto.
  Qed.
  Lemma put_fifos_diff f k k' v : k ≠ k' →
    get_fifos (put_fifos f k v) k' = get_fifos f k'.
  Proof.
    unfold get_fifos, put_fifos.
    destruct v; intros.
    - now rewrite get_remove_diff by auto.
    - now rewrite get_put_diff by auto.
  Qed.
  Lemma get_put_fifos f k v : ∀ k',
    get_fifos (put_fifos f k v) k' =
    match eq_dec k k' with
    | left EQ => v
    | right NEQ => get_fifos f k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    now first [apply put_fifos_same | apply put_fifos_diff].
  Qed.
  Lemma cons_fifos_same f k v :
    get_fifos (cons_fifos f k v) k = v :: get_fifos f k.
  Proof.
    unfold get_fifos, cons_fifos.
    rewrite get_alter_same.
    destruct (get f k) as [[??]|]; auto.
  Qed.
  Lemma cons_fifos_diff f k k' v : k ≠ k' →
    get_fifos (cons_fifos f k v) k' = get_fifos f k'.
  Proof.
    unfold get_fifos, cons_fifos. intros.
    now rewrite get_alter_diff by auto.
  Qed.
  Lemma get_cons_fifos f k v : ∀ k',
    get_fifos (cons_fifos f k v) k' =
    match eq_dec k k' with
    | left EQ => v :: get_fifos f k'
    | right NEQ => get_fifos f k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    now first [apply cons_fifos_same | apply cons_fifos_diff].
  Qed.
  Lemma enq_fifos_same f k v :
    get_fifos (enq_fifos f k v) k = get_fifos f k ++ [v].
  Proof.
    unfold get_fifos, enq_fifos.
    rewrite get_alter_same.
    destruct (get f k) as [[??]|]; auto.
  Qed.
  Lemma enq_fifos_diff f k k' v : k ≠ k' →
    get_fifos (enq_fifos f k v) k' = get_fifos f k'.
  Proof.
    unfold get_fifos, enq_fifos. intros.
    now rewrite get_alter_diff by auto.
  Qed.
  Lemma get_enq_fifos f k v : ∀ k',
    get_fifos (enq_fifos f k v) k' =
    match eq_dec k k' with
    | left EQ => get_fifos f k' ++ [v]
    | right NEQ => get_fifos f k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    now first [apply enq_fifos_same | apply enq_fifos_diff].
  Qed.
  Lemma deq_fifos_none f k :
    deq_fifos f k = None ↔ get_fifos f k = [].
  Proof.
    unfold deq_fifos, get_fifos.
    destruct (get f k) as [[??]|]; intuition congruence.
  Qed.
  Lemma deq_fifos_same {f f' k v} :
    deq_fifos f k = Some (v, f') →
    get_fifos f k = v :: get_fifos f' k.
  Proof.
    unfold deq_fifos, get_fifos.
    destruct (get f k) as [[??]|]; inversion 1; subst.
    f_equal. destruct l; now
    first [rewrite get_remove_same | rewrite get_put_same].
  Qed.
  Lemma deq_fifos_diff {f f' k v} :
    deq_fifos f k = Some (v, f') →
    ∀ k', k ≠ k' → get_fifos f k' = get_fifos f' k'.
  Proof.
    intro DEQ. intros. revert DEQ.
    unfold deq_fifos, get_fifos.
    destruct (get f k) as [[??]|]; inversion 1; subst.
    destruct l;
    now first [rewrite get_remove_diff by auto |
      rewrite get_put_diff by auto].
  Qed.
  Lemma get_deq_fifos {f f' k v} :
    deq_fifos f k = Some (v, f') → ∀ k',
    get_fifos f k' =
    match eq_dec k k' with
    | left EQ => v :: get_fifos f' k'
    | right NEQ => get_fifos f' k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    first [eapply deq_fifos_same | eapply deq_fifos_diff]; eauto.
  Qed.
  Lemma deq_fifos_some {f f' k v} :
    get_fifos f k = v :: get_fifos f' k →
    (∀ k', k ≠ k' → get_fifos f k' = get_fifos f' k') →
    deq_fifos f k = Some (v, f').
  Proof.
    unfold deq_fifos, get_fifos.
    destruct (get f k) as [[hd tl]|] eqn:GET; [|congruence].
    intro EQ. apply cons_inj in EQ. des; subst.
    intro DIFF.
    f_equal. f_equal.
    destruct (get f' k) as [[hd tl]|] eqn:GET'.
    - apply gmap_ext. intro k'.
      destruct (eq_dec k k'); subst.
      rewrite get_put_same. auto.
      rewrite get_put_diff by auto. exploit DIFF; eauto.
      destruct (get f k') as [[??]|], (get f' k') as [[??]|];
      congruence.
    - apply gmap_ext. intro k'.
      destruct (eq_dec k k'); subst.
      rewrite get_remove_same. auto.
      rewrite get_remove_diff by auto. exploit DIFF; eauto.
      destruct (get f k') as [[??]|], (get f' k') as [[??]|];
      congruence.
  Qed.
  Lemma deq_fifos_some_cons {f f' k v} :
    deq_fifos f k = Some (v, f') ↔ f = cons_fifos f' k v.
  Proof.
    intuition subst.
    - apply fifos_ext. intros. destruct (eq_dec k k0); subst.
      now rewrite cons_fifos_same, (deq_fifos_same H0).
      now rewrite cons_fifos_diff, (deq_fifos_diff H0) by auto.
    - apply deq_fifos_some.
      now rewrite cons_fifos_same.
      intros; now rewrite cons_fifos_diff by auto.
  Qed.
  Lemma deq_fifos_enq_fifos {f k k' v} :
    deq_fifos (enq_fifos f k v) k' =
      match deq_fifos f k' with
      | Some (v', f') => Some (v', enq_fifos f' k v)
      | None => if eq_dec k k' then Some (v, f) else None
      end.
  Proof.
    destruct (deq_fifos f _) as [[v' f']|] eqn:DEQ.
    - apply deq_fifos_some.
      + destruct (eq_dec k k'); subst.
        repeat rewrite enq_fifos_same.
        erewrite deq_fifos_same; eauto. now rewrite app_comm_cons.
        repeat rewrite enq_fifos_diff by auto.
        now apply deq_fifos_same.
      + intros.
        destruct (eq_dec k k'0); subst.
        repeat rewrite enq_fifos_same.
        f_equal. eapply deq_fifos_diff; eauto.
        repeat rewrite enq_fifos_diff by auto.
        eapply deq_fifos_diff; eauto.
    - destruct (eq_dec _ _); subst.
      + apply deq_fifos_some.
        rewrite enq_fifos_same.
        rewrite deq_fifos_none in *. now rewrite DEQ.
        intros. now rewrite enq_fifos_diff by auto.
      + rewrite deq_fifos_none in *. now rewrite enq_fifos_diff by auto.
  Qed.
  Lemma enq_fifos_enq_fifos_diff {f k k' v v'} : k <> k' ->
    enq_fifos (enq_fifos f k v) k' v' =
    enq_fifos (enq_fifos f k' v') k v.
  Proof.
    intros. apply fifos_ext. intros k''.
    destruct (eq_dec k' k''); subst;
      repeat first [rewrite enq_fifos_same | rewrite enq_fifos_diff by auto];
    destruct (eq_dec k k''); subst;
      repeat first [rewrite enq_fifos_same | rewrite enq_fifos_diff by auto]; auto.
  Qed.
  Definition fifos_cons_list f k l :=
    fold_right (fun v acc => cons_fifos acc k v) f l
  .
  Lemma fifos_cons_list_spec l f k :
    ∀ k', get_fifos (fifos_cons_list f k l) k' =
      match eq_dec k k' with
      | left EQ => l ++ get_fifos f k'
      | right NEQ => get_fifos f k'
      end.
  Proof.
    revert f k. induction l; unfold fifos_cons_list; intros; simpl in *.
    - destruct (eq_dec _ _); subst; auto.
    - unfold fifos_cons_list in IHl.
      destruct (eq_dec k k'); subst.
      + now rewrite cons_fifos_same, IHl, eq_dec_refl.
      + rewrite cons_fifos_diff, IHl by auto.
        destruct (eq_dec _ _); subst; congruence.
  Qed.
  Definition fifos_app_list f k l :=
    fold_left (fun acc => enq_fifos acc k) l f
  .
  Lemma fifos_app_list_spec l f k :
    ∀ k', get_fifos (fifos_app_list f k l) k' =
      match eq_dec k k' with
      | left EQ => get_fifos f k' ++ l
      | right NEQ => get_fifos f k'
      end.
  Proof.
    revert f k. induction l; unfold fifos_app_list; intros; simpl in *.
    - destruct (eq_dec _ _); subst; auto. now rewrite app_nil_r.
    - unfold fifos_app_list in IHl. rewrite IHl.
      destruct (eq_dec k k'); subst.
      + rewrite enq_fifos_same, <- app_assoc. auto.
      + rewrite enq_fifos_diff by auto. auto.
  Qed.
  Definition fifos_app_l (f f' : fifos) :=
    fold (fun acc k v => fifos_cons_list acc k (fst v :: snd v)) f f'
  .
  Definition fifos_app (f f' : fifos) :=
    fold (fun acc k v => fifos_app_list acc k (fst v :: snd v)) f f'
  .
  Definition fifos_sz (f : fifos) :=
    fold (fun acc k v => acc + S (List.length (snd v))) 0 f
  .
  Lemma fifos_app_l_spec f f' :
    ∀ k, get_fifos (fifos_app_l f f') k =
      get_fifos f' k ++ get_fifos f k.
  Proof.
    unfold fifos_app_l. apply fold_spec.
    - intros. now rewrite get_fifos_empty.
    - intros. rewrite fifos_cons_list_spec.
      destruct (eq_dec i k); subst.
      + unfold get_fifos. rewrite get_put_same. destruct v. cbn [fst snd].
        f_equal. specialize (IHfold k). unfold get_fifos in IHfold.
        now rewrite IHfold, Hget.
      + unfold get_fifos. rewrite get_put_diff; auto. apply IHfold.
  Qed.
  Lemma fifos_app_spec f f' :
    ∀ k, get_fifos (fifos_app f f') k =
      get_fifos f k ++ get_fifos f' k.
  Proof.
    unfold fifos_app. apply fold_spec.
    - intros. rewrite get_fifos_empty. now rewrite app_nil_r.
    - intros. rewrite fifos_app_list_spec.
      destruct (eq_dec i k); subst.
      + unfold get_fifos. rewrite get_put_same. destruct v. cbn [fst snd].
        f_equal. specialize (IHfold k). unfold get_fifos in IHfold.
        rewrite IHfold. rewrite Hget, app_nil_r. auto.
      + unfold get_fifos. rewrite get_put_diff; auto. apply IHfold.
  Qed.
  Inductive fifos_ind_cons_aux : fifos → Prop :=
  | fifos_ind_cons_aux_empty : fifos_ind_cons_aux empty
  | fifos_ind_cons_aux_enq f (R : fifos_ind_cons_aux f) k v : fifos_ind_cons_aux (cons_fifos f k v)
  .
  Lemma fifos_ind_cons_aux_all f : fifos_ind_cons_aux f.
  Proof.
    assert (f = fifos_app_l empty f) as AUX.
    { apply fifos_ext. intros. now rewrite fifos_app_l_spec, get_fifos_empty, app_nil_r. }
    revert AUX. unfold fifos_app_l. apply fold_spec.
    { constructor. }
    clear f. intros. destruct v as (hd & tl).
    cbn [fst snd] in *.
    assert (get_fifos m i = []) as GET. { unfold get_fifos. now rewrite Hget. }
    clear Hget.
    assert (put m i (hd, tl) = put_fifos m i (hd :: tl)) as RR.
    { apply fifos_ext. intros. rewrite get_put_fifos.
      unfold get_fifos. destruct (eq_dec _ _); subst.
      now rewrite get_put_same.
      now rewrite get_put_diff by auto. }
    rewrite RR in *. clear RR.
    exploit IHfold.
    { apply fifos_ext. intros. apply (f_equal (fun f => get_fifos f k)) in AUX.
      rewrite get_put_fifos, fifos_cons_list_spec in AUX.
      destruct (eq_dec _ _); subst; auto.
      rewrite GET. revert AUX.
      generalize (get_fifos r k). generalize (hd :: tl) as l'.
      induction l'; simpl. intros; auto.
      intros. destruct l. auto.
      apply cons_inj in AUX. des; subst.
      exploit (IHl' (v :: l)); auto. }
    generalize (hd :: tl). induction l.
    - intros. assert (put_fifos m i [] = m) as ->; auto.
      apply fifos_ext. intros. rewrite get_put_fifos.
      destruct (eq_dec _ _); subst; auto.
    - intros. exploit IHl; eauto. intros.
      assert (put_fifos m i (a :: l) = cons_fifos (put_fifos m i l) i a) as ->.
      2: constructor; auto.
      apply fifos_ext. intros. rewrite get_put_fifos, get_cons_fifos.
      destruct (eq_dec _ _); subst.
      now rewrite put_fifos_same.
      now rewrite put_fifos_diff by auto.
  Qed.
  Lemma fifos_ind_cons P :
    P empty → (∀ f k v (IHfifos : P f), P (cons_fifos f k v)) →
    ∀ f, P f : Prop.
  Proof.
    intros. specialize (fifos_ind_cons_aux_all f). induction 1; auto.
  Qed.
  Inductive fifos_ind_aux : fifos → Prop :=
  | fifos_ind_aux_empty : fifos_ind_aux empty
  | fifos_ind_aux_enq f (R : fifos_ind_aux f) k v : fifos_ind_aux (enq_fifos f k v)
  .
  Lemma fifos_ind_aux_all f : fifos_ind_aux f.
  Proof.
    assert (f = fifos_app empty f) as AUX.
    { apply fifos_ext. intros. now rewrite fifos_app_spec, get_fifos_empty. }
    revert AUX. unfold fifos_app. apply fold_spec.
    { constructor. }
    clear f. intros. destruct v as (hd & tl).
    cbn [fst snd] in *.
    assert (get_fifos m i = []) as GET. { unfold get_fifos. now rewrite Hget. }
    clear Hget.
    assert (put m i (hd, tl) = put_fifos m i (hd :: tl)) as RR.
    { apply fifos_ext. intros. rewrite get_put_fifos.
      unfold get_fifos. destruct (eq_dec _ _); subst.
      now rewrite get_put_same.
      now rewrite get_put_diff by auto. }
    rewrite RR in *. clear RR.
    exploit IHfold.
    { apply fifos_ext. intros. apply (f_equal (fun f => get_fifos f k)) in AUX.
      rewrite get_put_fifos, fifos_app_list_spec in AUX.
      destruct (eq_dec _ _); subst; auto.
      rewrite GET. revert AUX.
      generalize (get_fifos r k). generalize (hd :: tl) as l'.
      induction l'; simpl. intros. rewrite app_nil_r in *. auto.
      intros. destruct l. auto. cbn [app] in AUX.
      apply cons_inj in AUX. des; subst.
      exploit (IHl' (l ++ [v])). rewrite <- app_assoc. auto.
      intro C. symmetry in C. apply app_eq_nil in C. des. discriminate. }
    generalize (hd :: tl). induction l using rev_ind.
    - intros. assert (put_fifos m i [] = m) as ->; auto.
      apply fifos_ext. intros. rewrite get_put_fifos.
      destruct (eq_dec _ _); subst; auto.
    - intros. exploit IHl; eauto. intros.
      assert (put_fifos m i (l ++ [x]) = enq_fifos (put_fifos m i l) i x) as ->.
      2: constructor; auto.
      apply fifos_ext. intros. rewrite get_put_fifos, get_enq_fifos.
      destruct (eq_dec _ _); subst.
      now rewrite put_fifos_same.
      now rewrite put_fifos_diff by auto.
  Qed.
  Lemma fifos_ind P :
    P empty → (∀ f k v (IHfifos : P f), P (enq_fifos f k v)) →
    ∀ f, P f : Prop.
  Proof.
    intros. specialize (fifos_ind_aux_all f). induction 1; auto.
  Qed.
  Inductive fifos_sz_cons_aux : fifos → nat → Prop :=
  | fifos_sz_cons_aux_empty : fifos_sz_cons_aux empty 0
  | fifos_sz_cons_aux_enq f n (R : fifos_sz_cons_aux f n) k v : fifos_sz_cons_aux (cons_fifos f k v) (S n)
  .
  Lemma fifos_sz_cons_aux_exists f : fifos_sz_cons_aux f (fifos_sz f).
  Proof.
    remember (fifos_sz f).
    assert (f = fifos_app_l empty f) as ->.
    { apply fifos_ext. intros. now rewrite fifos_app_l_spec, get_fifos_empty, app_nil_r. }
    subst. unfold fifos_app_l, fifos_sz.
    apply fold_parametricity. 2: constructor.
    intros. change (S (List.length (snd v))) with (List.length (fst v :: snd v)).
    generalize (fst v :: snd v).
    intro. revert a b i REL. clear.
    induction l; unfold fifos_cons_list; intros; simpl in *.
    - rewrite Nat.add_0_r. auto.
    - rewrite <- Nat.add_succ_comm. constructor. apply IHl; auto.
  Qed.
  Lemma fifos_sz_cons_aux_inv {f n} :
    fifos_sz_cons_aux f n ->
    ∀ f' k v, f = cons_fifos f' k v →
      ∃ n', n = S n' ∧ fifos_sz_cons_aux f' n'.
  Proof.
    induction 1 as [|f n AUX IHAUX k0 v0]; intros ??? ENQ.
    - apply (f_equal (fun x => get_fifos x k)) in ENQ.
      rewrite get_fifos_empty, cons_fifos_same in *. discriminate.
    - destruct (eq_dec k0 k); subst.
      + assert (f = f').
        { apply fifos_ext. intro k'.
          apply (f_equal (fun x => get_fifos x k')) in ENQ.
          repeat rewrite get_cons_fifos in *.
          destruct (eq_dec _ _); subst; auto.
          apply cons_inj in ENQ. des; auto. }
        subst. eauto.
      + assert (f = cons_fifos (put_fifos f' k0 (get_fifos f k0)) k v).
        { apply fifos_ext. intro k'.
          apply (f_equal (fun x => get_fifos x k')) in ENQ.
          repeat rewrite get_cons_fifos in *. rewrite get_put_fifos.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        exploit IHAUX; eauto. intros; des; subst. eexists; split; eauto.
        assert (f' = cons_fifos (put_fifos f' k0 (get_fifos f k0)) k0 v0) as ->.
        { apply fifos_ext. intro k'.
          apply (f_equal (fun x => get_fifos x k')) in ENQ.
          repeat rewrite get_cons_fifos in *. rewrite get_put_fifos.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        constructor; auto.
  Qed.
  Lemma fifos_sz_cons_aux_unique f n m :
    fifos_sz_cons_aux f n →
    fifos_sz_cons_aux f m →
    n = m.
  Proof.
    revert f m.
    induction n as [|n IH]; intros f m AUX1 AUX2.
    - inversion AUX1; subst. inversion AUX2; auto.
      apply (f_equal (fun x => get_fifos x k)) in H1.
      rewrite get_fifos_empty, cons_fifos_same in *. discriminate.
    - assert (f <> empty) as NE.
      { intros ->. inversion AUX1.
        apply (f_equal (fun x => get_fifos x k)) in H1.
        rewrite get_fifos_empty, cons_fifos_same in *. discriminate. }
      destruct (fifos_ind_cons_aux_all f). contradiction.
      eapply fifos_sz_cons_aux_inv in AUX1; eauto. des.
      inversion AUX1; subst; eauto.
      eapply fifos_sz_cons_aux_inv in AUX2; eauto. des; subst.
      f_equal; eauto.
  Qed.
  Lemma fifos_sz_cons_aux_spec f n :
    fifos_sz_cons_aux f n → fifos_sz f = n.
  Proof.
    intro AUX. symmetry.
    eapply fifos_sz_cons_aux_unique; eauto using fifos_sz_cons_aux_exists.
  Qed.
  Lemma fifos_sz_cons f k v :
    fifos_sz (cons_fifos f k v) = S (fifos_sz f).
  Proof.
    apply fifos_sz_cons_aux_spec.
    constructor.
    apply fifos_sz_cons_aux_exists.
  Qed.
  Inductive fifos_sz_aux : fifos → nat → Prop :=
  | fifos_sz_aux_empty : fifos_sz_aux empty 0
  | fifos_sz_aux_enq f n (R : fifos_sz_aux f n) k v : fifos_sz_aux (enq_fifos f k v) (S n)
  .
  Lemma fifos_sz_aux_exists f : fifos_sz_aux f (fifos_sz f).
  Proof.
    remember (fifos_sz f).
    assert (f = fifos_app empty f) as ->.
    { apply fifos_ext. intros. now rewrite fifos_app_spec, get_fifos_empty. }
    subst. unfold fifos_app, fifos_sz.
    apply fold_parametricity. 2: constructor.
    intros. change (S (List.length (snd v))) with (List.length (fst v :: snd v)).
    generalize (fst v :: snd v).
    intro. revert a b i REL. clear.
    induction l; unfold fifos_app_list; intros; simpl in *.
    - rewrite Nat.add_0_r. auto.
    - rewrite <- Nat.add_succ_comm. apply IHl. constructor; auto.
  Qed.
  Lemma fifos_sz_aux_inv {f n} :
    fifos_sz_aux f n ->
    ∀ f' k v, f = enq_fifos f' k v →
      ∃ n', n = S n' ∧ fifos_sz_aux f' n'.
  Proof.
    induction 1 as [|f n AUX IHAUX k0 v0]; intros ??? ENQ.
    - apply (f_equal (fun x => get_fifos x k)) in ENQ.
      rewrite get_fifos_empty, enq_fifos_same in *.
      symmetry in ENQ. apply app_eq_nil in ENQ. des; discriminate.
    - destruct (eq_dec k0 k); subst.
      + assert (f = f').
        { apply fifos_ext. intro k'.
          apply (f_equal (fun x => get_fifos x k')) in ENQ.
          repeat rewrite get_enq_fifos in *.
          destruct (eq_dec _ _); subst; auto.
          apply app_inj_tail in ENQ. des; auto. }
        subst. eauto.
      + assert (f = enq_fifos (put_fifos f' k0 (get_fifos f k0)) k v).
        { apply fifos_ext. intro k'.
          apply (f_equal (fun x => get_fifos x k')) in ENQ.
          repeat rewrite get_enq_fifos in *. rewrite get_put_fifos.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        exploit IHAUX; eauto. intros; des; subst. eexists; split; eauto.
        assert (f' = enq_fifos (put_fifos f' k0 (get_fifos f k0)) k0 v0) as ->.
        { apply fifos_ext. intro k'.
          apply (f_equal (fun x => get_fifos x k')) in ENQ.
          repeat rewrite get_enq_fifos in *. rewrite get_put_fifos.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        constructor; auto.
  Qed.
  Lemma fifos_sz_aux_unique f n m :
    fifos_sz_aux f n →
    fifos_sz_aux f m →
    n = m.
  Proof.
    revert f m.
    induction n as [|n IH]; intros f m AUX1 AUX2.
    - inversion AUX1; subst. inversion AUX2; auto.
      apply (f_equal (fun x => get_fifos x k)) in H1.
      rewrite get_fifos_empty, enq_fifos_same in *.
      apply app_eq_nil in H1. des; discriminate.
    - assert (f <> empty) as NE.
      { intros ->. inversion AUX1.
        apply (f_equal (fun x => get_fifos x k)) in H1.
        rewrite get_fifos_empty, enq_fifos_same in *.
        apply app_eq_nil in H1. des; discriminate. }
      destruct (fifos_ind_aux_all f). contradiction.
      eapply fifos_sz_aux_inv in AUX1; eauto. des.
      inversion AUX1; subst; eauto.
      eapply fifos_sz_aux_inv in AUX2; eauto. des; subst.
      f_equal; eauto.
  Qed.
  Lemma fifos_sz_aux_spec f n :
    fifos_sz_aux f n → fifos_sz f = n.
  Proof.
    intro AUX. symmetry.
    eapply fifos_sz_aux_unique; eauto using fifos_sz_aux_exists.
  Qed.
  Lemma fifos_sz_enq f k v :
    fifos_sz (enq_fifos f k v) = S (fifos_sz f).
  Proof.
    apply fifos_sz_aux_spec.
    constructor.
    apply fifos_sz_aux_exists.
  Qed.
End fifos.

Arguments fifos _ {_ _} _.

Section fifos_dep.
  Context `{Ok : Countable fifo_key} {V : fifo_key → Type}.
  Definition fifos_dep := gmap_dep fifo_key (fun k => V k * list (V k))%type.
  Definition get_fifos_dep f k : list (V k) :=
    match get_dep f k with
    | Some (hd, tl) => hd :: tl
    | None => []
    end.
  Definition put_fifos_dep f k l : fifos_dep :=
    match l with
    | [] => remove_dep f k
    | hd :: tl => put_dep f k (hd, tl)
    end.
  Definition cons_fifos_dep (f : fifos_dep) k v : fifos_dep :=
    alter_dep f k (fun x => Some
      match x with
      | Some (hd, tl) => (v, hd :: tl)
      | None => (v, [])
      end
    ).
  Definition enq_fifos_dep (f : fifos_dep) k v : fifos_dep :=
    alter_dep f k (fun x => Some
      match x with
      | Some (hd, tl) => (hd, tl ++ [v])
      | None => (v, [])
      end
    ).
  Definition deq_fifos_dep (f : fifos_dep) k : option (V k * fifos_dep) :=
    match get_dep f k with
    | Some (hd, tl) => Some (hd,
      match tl with [] => remove_dep f k | hd' :: tl' => put_dep f k (hd', tl') end)
    | None => None
    end.
  Lemma fifos_dep_ext x y (EXT : ∀ k, get_fifos_dep x k = get_fifos_dep y k) : x = y.
  Proof.
    apply gmap_dep_ext. intros. specialize (EXT k).
    unfold get_fifos_dep in *.
    destruct (get_dep x k) as [[??]|], (get_dep y k) as [[??]|];
      inversion EXT; subst; auto.
  Qed.
  Lemma get_fifos_dep_empty k : get_fifos_dep empty_dep k = [].
  Proof. reflexivity. Qed.
  Lemma get_fifos_dep_nonempty m : m <> empty_dep -> exists k, get_fifos_dep m k <> [].
  Proof.
    destruct m. intros. contradiction.
    intros _.
    specialize (get_dep_nonempty m). intros (k & GET).
    exists k.
    unfold get_fifos_dep.
    simpl. destruct (get'_dep _ _); auto.
    destruct p. inversion 1.
  Qed.
  Lemma put_fifos_dep_same f k v :
    get_fifos_dep (put_fifos_dep f k v) k = v.
  Proof.
    unfold get_fifos_dep, put_fifos_dep.
    destruct v.
    - now rewrite get_dep_remove_dep_same.
    - now rewrite get_dep_put_dep_same by auto.
  Qed.
  Lemma put_fifos_dep_diff f k k' v : k ≠ k' →
    get_fifos_dep (put_fifos_dep f k v) k' = get_fifos_dep f k'.
  Proof.
    unfold get_fifos_dep, put_fifos_dep.
    destruct v; intros.
    - now rewrite get_dep_remove_dep_diff by auto.
    - now rewrite get_dep_put_dep_diff by auto.
  Qed.
  Lemma get_put_fifos_dep f k v : ∀ k',
    get_fifos_dep (put_fifos_dep f k v) k' =
    match eq_dec k k' with
    | left EQ => rew [fun k => list (V k)] EQ in v
    | right NEQ => get_fifos_dep f k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    now first [apply put_fifos_dep_same | apply put_fifos_dep_diff].
  Qed.
  Lemma cons_fifos_dep_same f k v :
    get_fifos_dep (cons_fifos_dep f k v) k = v :: get_fifos_dep f k.
  Proof.
    unfold get_fifos_dep, cons_fifos_dep.
    rewrite get_dep_alter_dep_same.
    destruct (get_dep f k) as [[??]|]; auto.
  Qed.
  Lemma cons_fifos_dep_diff f k k' v : k ≠ k' →
    get_fifos_dep (cons_fifos_dep f k v) k' = get_fifos_dep f k'.
  Proof.
    unfold get_fifos_dep, cons_fifos_dep. intros.
    now rewrite get_dep_alter_dep_diff by auto.
  Qed.
  Lemma get_cons_fifos_dep f k v : ∀ k',
    get_fifos_dep (cons_fifos_dep f k v) k' =
    match eq_dec k k' with
    | left EQ => rew EQ in v :: get_fifos_dep f k'
    | right NEQ => get_fifos_dep f k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    now first [apply cons_fifos_dep_same | apply cons_fifos_dep_diff].
  Qed.
  Lemma enq_fifos_dep_same f k v :
    get_fifos_dep (enq_fifos_dep f k v) k = get_fifos_dep f k ++ [v].
  Proof.
    unfold get_fifos_dep, enq_fifos_dep.
    rewrite get_dep_alter_dep_same.
    destruct (get_dep f k) as [[??]|]; auto.
  Qed.
  Lemma enq_fifos_dep_diff f k k' v : k ≠ k' →
    get_fifos_dep (enq_fifos_dep f k v) k' = get_fifos_dep f k'.
  Proof.
    unfold get_fifos_dep, enq_fifos_dep. intros.
    now rewrite get_dep_alter_dep_diff by auto.
  Qed.
  Lemma get_enq_fifos_dep f k v : ∀ k',
    get_fifos_dep (enq_fifos_dep f k v) k' =
    match eq_dec k k' with
    | left EQ => get_fifos_dep f k' ++ [rew EQ in v]
    | right NEQ => get_fifos_dep f k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    now first [apply enq_fifos_dep_same | apply enq_fifos_dep_diff].
  Qed.
  Lemma deq_fifos_dep_none f k :
    deq_fifos_dep f k = None ↔ get_fifos_dep f k = [].
  Proof.
    unfold deq_fifos_dep, get_fifos_dep.
    destruct (get_dep f k) as [[??]|]; intuition congruence.
  Qed.
  Lemma deq_fifos_dep_same {f f' k v} :
    deq_fifos_dep f k = Some (v, f') →
    get_fifos_dep f k = v :: get_fifos_dep f' k.
  Proof.
    unfold deq_fifos_dep, get_fifos_dep.
    destruct (get_dep f k) as [[??]|]; inversion 1; subst.
    f_equal. destruct l; now
    first [rewrite get_dep_remove_dep_same | rewrite get_dep_put_dep_same].
  Qed.
  Lemma deq_fifos_dep_diff {f f' k v} :
    deq_fifos_dep f k = Some (v, f') →
    ∀ k', k ≠ k' → get_fifos_dep f k' = get_fifos_dep f' k'.
  Proof.
    intro DEQ. intros. revert DEQ.
    unfold deq_fifos_dep, get_fifos_dep.
    destruct (get_dep f k) as [[??]|]; inversion 1; subst.
    destruct l;
    now first [rewrite get_dep_remove_dep_diff by auto |
      rewrite get_dep_put_dep_diff by auto].
  Qed.
  Lemma get_deq_fifos_dep {f f' k v} :
    deq_fifos_dep f k = Some (v, f') → ∀ k',
    get_fifos_dep f k' =
    match eq_dec k k' with
    | left EQ => rew EQ in v :: get_fifos_dep f' k'
    | right NEQ => get_fifos_dep f' k'
    end.
  Proof.
    intros. destruct (eq_dec _ _); subst;
    first [eapply deq_fifos_dep_same | eapply deq_fifos_dep_diff]; eauto.
  Qed.
  Lemma deq_fifos_dep_some {f f' k v} :
    get_fifos_dep f k = v :: get_fifos_dep f' k →
    (∀ k', k ≠ k' → get_fifos_dep f k' = get_fifos_dep f' k') →
    deq_fifos_dep f k = Some (v, f').
  Proof.
    unfold deq_fifos_dep, get_fifos_dep.
    destruct (get_dep f k) as [[hd tl]|] eqn:GET; [|congruence].
    intro EQ. apply cons_inj in EQ. des; subst.
    intro DIFF.
    f_equal. f_equal.
    destruct (get_dep f' k) as [[hd tl]|] eqn:GET'.
    - apply gmap_dep_ext. intro k'.
      destruct (eq_dec k k'); subst.
      rewrite get_dep_put_dep_same. auto.
      rewrite get_dep_put_dep_diff by auto. exploit DIFF; eauto.
      destruct (get_dep f k') as [[??]|], (get_dep f' k') as [[??]|];
      congruence.
    - apply gmap_dep_ext. intro k'.
      destruct (eq_dec k k'); subst.
      rewrite get_dep_remove_dep_same. auto.
      rewrite get_dep_remove_dep_diff by auto. exploit DIFF; eauto.
      destruct (get_dep f k') as [[??]|], (get_dep f' k') as [[??]|];
      congruence.
  Qed.
  Lemma deq_fifos_dep_some_cons {f f' k v} :
    deq_fifos_dep f k = Some (v, f') ↔ f = cons_fifos_dep f' k v.
  Proof.
    intuition subst.
    - apply fifos_dep_ext. intros. destruct (eq_dec k k0); subst.
      now rewrite cons_fifos_dep_same, (deq_fifos_dep_same H0).
      now rewrite cons_fifos_dep_diff, (deq_fifos_dep_diff H0) by auto.
    - apply deq_fifos_dep_some.
      now rewrite cons_fifos_dep_same.
      intros; now rewrite cons_fifos_dep_diff by auto.
  Qed.
  Lemma deq_fifos_dep_enq_fifos_dep {f k k' v} :
    deq_fifos_dep (enq_fifos_dep f k v) k' =
      match deq_fifos_dep f k' with
      | Some (v', f') => Some (v', enq_fifos_dep f' k v)
      | None =>
        match eq_dec k k' with
        | left EQ => Some (rew EQ in v, f)
        | right NEQ => None
        end
      end.
  Proof.
    destruct (deq_fifos_dep f _) as [[v' f']|] eqn:DEQ.
    - apply deq_fifos_dep_some.
      + destruct (eq_dec k k'); subst.
        repeat rewrite enq_fifos_dep_same.
        erewrite deq_fifos_dep_same; eauto. now rewrite app_comm_cons.
        repeat rewrite enq_fifos_dep_diff by auto.
        now apply deq_fifos_dep_same.
      + intros.
        destruct (eq_dec k k'0); subst.
        repeat rewrite enq_fifos_dep_same.
        f_equal. eapply deq_fifos_dep_diff; eauto.
        repeat rewrite enq_fifos_dep_diff by auto.
        eapply deq_fifos_dep_diff; eauto.
    - destruct (eq_dec _ _); subst.
      + apply deq_fifos_dep_some.
        rewrite enq_fifos_dep_same.
        rewrite deq_fifos_dep_none in *. now rewrite DEQ.
        intros. now rewrite enq_fifos_dep_diff by auto.
      + rewrite deq_fifos_dep_none in *. now rewrite enq_fifos_dep_diff by auto.
  Qed.
  Lemma enq_fifos_dep_enq_fifos_dep_diff {f k k' v v'} : k <> k' ->
    enq_fifos_dep (enq_fifos_dep f k v) k' v' =
    enq_fifos_dep (enq_fifos_dep f k' v') k v.
  Proof.
    intros. apply fifos_dep_ext. intros k''.
    destruct (eq_dec k' k''); subst;
      repeat first [rewrite enq_fifos_dep_same | rewrite enq_fifos_dep_diff by auto];
    destruct (eq_dec k k''); subst;
      repeat first [rewrite enq_fifos_dep_same | rewrite enq_fifos_dep_diff by auto]; auto.
  Qed.
  Definition fifos_dep_cons_list f k l :=
    fold_right (fun v acc => cons_fifos_dep acc k v) f l
  .
  Lemma fifos_dep_cons_list_spec f k l :
    ∀ k', get_fifos_dep (fifos_dep_cons_list f k l) k' =
      match eq_dec k k' with
      | left EQ => rew [list ∘ V] EQ in l ++ get_fifos_dep f k'
      | right NEQ => get_fifos_dep f k'
      end.
  Proof.
    revert f. induction l; unfold fifos_dep_cons_list; intros; simpl in *.
    - destruct (eq_dec _ _); subst; auto.
    - unfold fifos_dep_cons_list in IHl.
      destruct (eq_dec k k'); subst.
      + now rewrite cons_fifos_dep_same, IHl, eq_dec_refl.
      + rewrite cons_fifos_dep_diff, IHl by auto.
        destruct (eq_dec _ _); subst; congruence.
  Qed.
  Definition fifos_dep_app_list f k l :=
    fold_left (fun acc => enq_fifos_dep acc k) l f
  .
  Lemma fifos_dep_app_list_spec f k l :
    ∀ k', get_fifos_dep (fifos_dep_app_list f k l) k' =
      match eq_dec k k' with
      | left EQ => get_fifos_dep f k' ++ rew [list ∘ V] EQ in l
      | right NEQ => get_fifos_dep f k'
      end.
  Proof.
    revert f. induction l; unfold fifos_app_list; intros; simpl in *.
    - destruct (eq_dec _ _); subst; auto. now rewrite app_nil_r.
    - unfold fifos_app_list in IHl. rewrite IHl.
      destruct (eq_dec k k'); subst.
      + rewrite enq_fifos_dep_same, <- app_assoc. auto.
      + rewrite enq_fifos_dep_diff by auto. auto.
  Qed.
  Definition fifos_dep_app_l (f f' : fifos_dep) :=
    fold_dep (fun acc k v => fifos_dep_cons_list acc k (fst v :: snd v)) f f'
  .
  Definition fifos_dep_app (f f' : fifos_dep) :=
    fold_dep (fun acc k v => fifos_dep_app_list acc k (fst v :: snd v)) f f'
  .
  Definition fifos_dep_sz (f : fifos_dep) :=
    fold_dep (fun acc k v => acc + S (List.length (snd v))) 0 f
  .
  Lemma fifos_dep_app_l_spec f f' :
    ∀ k, get_fifos_dep (fifos_dep_app_l f f') k =
      get_fifos_dep f' k ++ get_fifos_dep f k.
  Proof.
    unfold fifos_dep_app_l. apply fold_dep_spec.
    - intros. now rewrite get_fifos_dep_empty.
    - intros. rewrite fifos_dep_cons_list_spec.
      destruct (eq_dec i k); subst.
      + unfold get_fifos_dep. rewrite get_dep_put_dep_same. destruct v. cbn [fst snd].
        f_equal. specialize (IHfold k). unfold get_fifos_dep in IHfold.
        now rewrite IHfold, Hget.
      + unfold get_fifos_dep. rewrite get_dep_put_dep_diff; auto.
  Qed.
  Lemma fifos_dep_app_spec f f' :
    ∀ k, get_fifos_dep (fifos_dep_app f f') k =
      get_fifos_dep f k ++ get_fifos_dep f' k.
  Proof.
    unfold fifos_dep_app. apply fold_dep_spec.
    - intros. rewrite get_fifos_dep_empty. now rewrite app_nil_r.
    - intros. rewrite fifos_dep_app_list_spec.
      destruct (eq_dec i k); subst.
      + unfold get_fifos_dep. rewrite get_dep_put_dep_same. destruct v. cbn [fst snd].
        f_equal. specialize (IHfold k). unfold get_fifos_dep in IHfold.
        rewrite IHfold. rewrite Hget, app_nil_r. auto.
      + unfold get_fifos_dep. rewrite get_dep_put_dep_diff; auto.
  Qed.
  Inductive fifos_dep_ind_cons_aux : fifos_dep → Prop :=
  | fifos_dep_ind_cons_aux_empty : fifos_dep_ind_cons_aux empty_dep
  | fifos_dep_ind_cons_aux_enq f (R : fifos_dep_ind_cons_aux f) k v : fifos_dep_ind_cons_aux (cons_fifos_dep f k v)
  .
  Lemma fifos_dep_ind_cons_aux_all f : fifos_dep_ind_cons_aux f.
  Proof.
    assert (f = fifos_dep_app_l empty_dep f) as AUX.
    { apply fifos_dep_ext. intros. now rewrite fifos_dep_app_l_spec, get_fifos_dep_empty, app_nil_r. }
    revert AUX. unfold fifos_dep_app_l. apply fold_dep_spec.
    { constructor. }
    clear f. intros. destruct v as (hd & tl).
    cbn [fst snd] in *.
    assert (get_fifos_dep m i = []) as GET. { unfold get_fifos_dep. now rewrite Hget. }
    clear Hget.
    assert (put_dep m i (hd, tl) = put_fifos_dep m i (hd :: tl)) as RR.
    { apply fifos_dep_ext. intros. rewrite get_put_fifos_dep.
      unfold get_fifos_dep. destruct (eq_dec _ _); subst.
      now rewrite get_dep_put_dep_same.
      now rewrite get_dep_put_dep_diff by auto. }
    rewrite RR in *. clear RR.
    exploit IHfold.
    { apply fifos_dep_ext. intros. apply (f_equal (fun f => get_fifos_dep f k)) in AUX.
      rewrite get_put_fifos_dep, fifos_dep_cons_list_spec in AUX.
      destruct (eq_dec _ _); subst; auto.
      rewrite GET. revert AUX.
      generalize (get_fifos_dep r k). generalize (hd :: tl) as l'.
      induction l'; simpl. intros; auto.
      intros. destruct l. auto.
      apply cons_inj in AUX. des; subst.
      exploit (IHl' (v :: l)); auto. }
    generalize (hd :: tl). induction l.
    - intros. assert (put_fifos_dep m i [] = m) as ->; auto.
      apply fifos_dep_ext. intros. rewrite get_put_fifos_dep.
      destruct (eq_dec _ _); subst; auto.
    - intros. exploit IHl; eauto. intros.
      assert (put_fifos_dep m i (a :: l) = cons_fifos_dep (put_fifos_dep m i l) i a) as ->.
      2: constructor; auto.
      apply fifos_dep_ext. intros. rewrite get_put_fifos_dep, get_cons_fifos_dep.
      destruct (eq_dec _ _); subst.
      now rewrite put_fifos_dep_same.
      now rewrite put_fifos_dep_diff by auto.
  Qed.
  Lemma fifos_dep_ind_cons P :
    P empty_dep → (∀ f k v (IHfifos : P f), P (cons_fifos_dep f k v)) →
    ∀ f, P f : Prop.
  Proof.
    intros. specialize (fifos_dep_ind_cons_aux_all f). induction 1; auto.
  Qed.
  Inductive fifos_dep_ind_aux : fifos_dep → Prop :=
  | fifos_dep_ind_aux_empty : fifos_dep_ind_aux empty_dep
  | fifos_dep_ind_aux_enq f (R : fifos_dep_ind_aux f) k v : fifos_dep_ind_aux (enq_fifos_dep f k v)
  .
  Lemma fifos_dep_ind_aux_all f : fifos_dep_ind_aux f.
  Proof.
    assert (f = fifos_dep_app empty_dep f) as AUX.
    { apply fifos_dep_ext. intros. now rewrite fifos_dep_app_spec, get_fifos_dep_empty. }
    revert AUX. unfold fifos_dep_app. apply fold_dep_spec.
    { constructor. }
    clear f. intros. destruct v as (hd & tl).
    cbn [fst snd] in *.
    assert (get_fifos_dep m i = []) as GET. { unfold get_fifos_dep. now rewrite Hget. }
    clear Hget.
    assert (put_dep m i (hd, tl) = put_fifos_dep m i (hd :: tl)) as RR.
    { apply fifos_dep_ext. intros. rewrite get_put_fifos_dep.
      unfold get_fifos_dep. destruct (eq_dec _ _); subst.
      now rewrite get_dep_put_dep_same.
      now rewrite get_dep_put_dep_diff by auto. }
    rewrite RR in *. clear RR.
    exploit IHfold.
    { apply fifos_dep_ext. intros. apply (f_equal (fun f => get_fifos_dep f k)) in AUX.
      rewrite get_put_fifos_dep, fifos_dep_app_list_spec in AUX.
      destruct (eq_dec _ _); subst; auto.
      rewrite GET. revert AUX.
      generalize (get_fifos_dep r k). generalize (hd :: tl) as l'.
      induction l'; simpl. intros. rewrite app_nil_r in *. auto.
      intros. destruct l. auto. cbn [app] in AUX.
      apply cons_inj in AUX. des; subst.
      exploit (IHl' (l ++ [v])). rewrite <- app_assoc. auto.
      intro C. symmetry in C. apply app_eq_nil in C. des. discriminate. }
    generalize (hd :: tl). induction l using rev_ind.
    - intros. assert (put_fifos_dep m i [] = m) as ->; auto.
      apply fifos_dep_ext. intros. rewrite get_put_fifos_dep.
      destruct (eq_dec _ _); subst; auto.
    - intros. exploit IHl; eauto. intros.
      assert (put_fifos_dep m i (l ++ [x]) = enq_fifos_dep (put_fifos_dep m i l) i x) as ->.
      2: constructor; auto.
      apply fifos_dep_ext. intros. rewrite get_put_fifos_dep, get_enq_fifos_dep.
      destruct (eq_dec _ _); subst.
      now rewrite put_fifos_dep_same.
      now rewrite put_fifos_dep_diff by auto.
  Qed.
  Lemma fifos_dep_ind P :
    P empty_dep → (∀ f k v (IHfifos_dep : P f), P (enq_fifos_dep f k v)) →
    ∀ f, P f : Prop.
  Proof.
    intros. specialize (fifos_dep_ind_aux_all f). induction 1; auto.
  Qed.
  Inductive fifos_dep_sz_cons_aux : fifos_dep → nat → Prop :=
  | fifos_dep_sz_cons_aux_empty : fifos_dep_sz_cons_aux empty_dep 0
  | fifos_dep_sz_cons_aux_enq f n (R : fifos_dep_sz_cons_aux f n) k v : fifos_dep_sz_cons_aux (cons_fifos_dep f k v) (S n)
  .
  Lemma fifos_dep_sz_cons_aux_exists f : fifos_dep_sz_cons_aux f (fifos_dep_sz f).
  Proof.
    remember (fifos_dep_sz f).
    assert (f = fifos_dep_app_l empty_dep f) as ->.
    { apply fifos_dep_ext. intros. now rewrite fifos_dep_app_l_spec, get_fifos_dep_empty, app_nil_r. }
    subst. unfold fifos_dep_app_l, fifos_dep_sz.
    apply fold_dep_parametricity. 2: constructor.
    intros. change (S (List.length (snd v))) with (List.length (fst v :: snd v)).
    generalize (fst v :: snd v).
    intro. revert a b REL. clear.
    induction l; unfold fifos_dep_cons_list; intros; simpl in *.
    - rewrite Nat.add_0_r. auto.
    - rewrite <- Nat.add_succ_comm. constructor. apply IHl; auto.
  Qed.
  Lemma fifos_dep_sz_cons_aux_inv {f n} :
    fifos_dep_sz_cons_aux f n ->
    ∀ f' k v, f = cons_fifos_dep f' k v →
      ∃ n', n = S n' ∧ fifos_dep_sz_cons_aux f' n'.
  Proof.
    induction 1 as [|f n AUX IHAUX k0 v0]; intros ??? ENQ.
    - apply (f_equal (fun x => get_fifos_dep x k)) in ENQ.
      rewrite get_fifos_dep_empty, cons_fifos_dep_same in *. discriminate.
    - destruct (eq_dec k0 k); subst.
      + assert (f = f').
        { apply fifos_dep_ext. intro k'.
          apply (f_equal (fun x => get_fifos_dep x k')) in ENQ.
          repeat rewrite get_cons_fifos_dep in *.
          destruct (eq_dec _ _); subst; auto.
          apply cons_inj in ENQ. des; auto. }
        subst. eauto.
      + assert (f = cons_fifos_dep (put_fifos_dep f' k0 (get_fifos_dep f k0)) k v).
        { apply fifos_dep_ext. intro k'.
          apply (f_equal (fun x => get_fifos_dep x k')) in ENQ.
          repeat rewrite get_cons_fifos_dep in *. rewrite get_put_fifos_dep.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        exploit IHAUX; eauto. intros; des; subst. eexists; split; eauto.
        assert (f' = cons_fifos_dep (put_fifos_dep f' k0 (get_fifos_dep f k0)) k0 v0) as ->.
        { apply fifos_dep_ext. intro k'.
          apply (f_equal (fun x => get_fifos_dep x k')) in ENQ.
          repeat rewrite get_cons_fifos_dep in *. rewrite get_put_fifos_dep.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        constructor; auto.
  Qed.
  Lemma fifos_dep_sz_cons_aux_unique f n m :
    fifos_dep_sz_cons_aux f n →
    fifos_dep_sz_cons_aux f m →
    n = m.
  Proof.
    revert f m.
    induction n as [|n IH]; intros f m AUX1 AUX2.
    - inversion AUX1; subst. inversion AUX2; auto.
      apply (f_equal (fun x => get_fifos_dep x k)) in H1.
      rewrite get_fifos_dep_empty, cons_fifos_dep_same in *. discriminate.
    - assert (f <> empty_dep) as NE.
      { intros ->. inversion AUX1.
        apply (f_equal (fun x => get_fifos_dep x k)) in H1.
        rewrite get_fifos_dep_empty, cons_fifos_dep_same in *. discriminate. }
      destruct (fifos_dep_ind_cons_aux_all f). contradiction.
      eapply fifos_dep_sz_cons_aux_inv in AUX1; eauto. des.
      inversion AUX1; subst; eauto.
      eapply fifos_dep_sz_cons_aux_inv in AUX2; eauto. des; subst.
      f_equal; eauto.
  Qed.
  Lemma fifos_dep_sz_cons_aux_spec f n :
    fifos_dep_sz_cons_aux f n → fifos_dep_sz f = n.
  Proof.
    intro AUX. symmetry.
    eapply fifos_dep_sz_cons_aux_unique; eauto using fifos_dep_sz_cons_aux_exists.
  Qed.
  Lemma fifos_dep_sz_cons f k v :
    fifos_dep_sz (cons_fifos_dep f k v) = S (fifos_dep_sz f).
  Proof.
    apply fifos_dep_sz_cons_aux_spec.
    constructor.
    apply fifos_dep_sz_cons_aux_exists.
  Qed.
  Inductive fifos_dep_sz_aux : fifos_dep → nat → Prop :=
  | fifos_dep_sz_aux_empty : fifos_dep_sz_aux empty_dep 0
  | fifos_dep_sz_aux_enq f n (R : fifos_dep_sz_aux f n) k v : fifos_dep_sz_aux (enq_fifos_dep f k v) (S n)
  .
  Lemma fifos_dep_sz_aux_exists f : fifos_dep_sz_aux f (fifos_dep_sz f).
  Proof.
    remember (fifos_dep_sz f).
    assert (f = fifos_dep_app empty_dep f) as ->.
    { apply fifos_dep_ext. intros. now rewrite fifos_dep_app_spec, get_fifos_dep_empty. }
    subst. unfold fifos_dep_app, fifos_dep_sz.
    apply fold_dep_parametricity. 2: constructor.
    intros. change (S (List.length (snd v))) with (List.length (fst v :: snd v)).
    generalize (fst v :: snd v).
    intro. revert a b v REL. clear.
    induction l; unfold fifos_app_list; intros; simpl in *.
    - rewrite Nat.add_0_r. auto.
    - rewrite <- Nat.add_succ_comm. apply IHl; auto. constructor; auto.
  Qed.
  Lemma fifos_dep_sz_aux_inv {f n} :
    fifos_dep_sz_aux f n ->
    ∀ f' k v, f = enq_fifos_dep f' k v →
      ∃ n', n = S n' ∧ fifos_dep_sz_aux f' n'.
  Proof.
    induction 1 as [|f n AUX IHAUX k0 v0]; intros ??? ENQ.
    - apply (f_equal (fun x => get_fifos_dep x k)) in ENQ.
      rewrite get_fifos_dep_empty, enq_fifos_dep_same in *.
      symmetry in ENQ. apply app_eq_nil in ENQ. des; discriminate.
    - destruct (eq_dec k0 k); subst.
      + assert (f = f').
        { apply fifos_dep_ext. intro k'.
          apply (f_equal (fun x => get_fifos_dep x k')) in ENQ.
          repeat rewrite get_enq_fifos_dep in *.
          destruct (eq_dec _ _); subst; auto.
          apply app_inj_tail in ENQ. des; auto. }
        subst. eauto.
      + assert (f = enq_fifos_dep (put_fifos_dep f' k0 (get_fifos_dep f k0)) k v).
        { apply fifos_dep_ext. intro k'.
          apply (f_equal (fun x => get_fifos_dep x k')) in ENQ.
          repeat rewrite get_enq_fifos_dep in *. rewrite get_put_fifos_dep.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        exploit IHAUX; eauto. intros; des; subst. eexists; split; eauto.
        assert (f' = enq_fifos_dep (put_fifos_dep f' k0 (get_fifos_dep f k0)) k0 v0) as ->.
        { apply fifos_dep_ext. intro k'.
          apply (f_equal (fun x => get_fifos_dep x k')) in ENQ.
          repeat rewrite get_enq_fifos_dep in *. rewrite get_put_fifos_dep.
          destruct (eq_dec _ _); subst; auto.
          destruct (eq_dec _ _); subst; auto. contradiction. }
        constructor; auto.
  Qed.
  Lemma fifos_dep_sz_aux_unique f n m :
    fifos_dep_sz_aux f n →
    fifos_dep_sz_aux f m →
    n = m.
  Proof.
    revert f m.
    induction n as [|n IH]; intros f m AUX1 AUX2.
    - inversion AUX1; subst. inversion AUX2; auto.
      apply (f_equal (fun x => get_fifos_dep x k)) in H1.
      rewrite get_fifos_dep_empty, enq_fifos_dep_same in *.
      apply app_eq_nil in H1. des; discriminate.
    - assert (f <> empty_dep) as NE.
      { intros ->. inversion AUX1.
        apply (f_equal (fun x => get_fifos_dep x k)) in H1.
        rewrite get_fifos_dep_empty, enq_fifos_dep_same in *.
        apply app_eq_nil in H1. des; discriminate. }
      destruct (fifos_dep_ind_aux_all f). contradiction.
      eapply fifos_dep_sz_aux_inv in AUX1; eauto. des.
      inversion AUX1; subst; eauto.
      eapply fifos_dep_sz_aux_inv in AUX2; eauto. des; subst.
      f_equal; eauto.
  Qed.
  Lemma fifos_dep_sz_aux_spec f n :
    fifos_dep_sz_aux f n → fifos_dep_sz f = n.
  Proof.
    intro AUX. symmetry.
    eapply fifos_dep_sz_aux_unique; eauto using fifos_dep_sz_aux_exists.
  Qed.
  Lemma fifos_dep_sz_enq f k v :
    fifos_dep_sz (enq_fifos_dep f k v) = S (fifos_dep_sz f).
  Proof.
    apply fifos_dep_sz_aux_spec.
    constructor.
    apply fifos_dep_sz_aux_exists.
  Qed.
End fifos_dep.

Arguments fifos_dep _ {_ _} _.

Section fifos_map.
  Context `{Countable K} `{Countable K'}.

  Definition fifos_map {V W} (f : V → W) :
    fifos K V → fifos K W :=
    gmap_map (fun x => Some (f (fst x), map f (snd x)))
  .

  Lemma fifos_map_spec {V W} (f : V → W) m :
    ∀ k, get_fifos (fifos_map f m) k = map f (get_fifos m k).
  Proof.
    intros. unfold get_fifos, fifos_map.
    rewrite gmap_map_spec. destruct (get m k); auto.
    destruct p; auto.
  Qed.

  Definition fifos_filter_fst {V} (x : K) :
    fifos (K * K') V → fifos K' V :=
    gmap_filter_fst x
  .

  Lemma fifos_filter_fst_spec {V} (x : K) m :
    ∀ y, get_fifos (fifos_filter_fst (V := V) x m) y = get_fifos m (x, y).
  Proof.
    unfold get_fifos, fifos_filter_fst.
    intros. now rewrite gmap_filter_fst_spec.
  Qed.

  Definition fifos_filter_snd {V} (y : K') :
    fifos (K * K') V → fifos K V :=
    gmap_filter_snd y
  .

  Lemma fifos_filter_snd_spec {V} (y : K') m :
    ∀ x, get_fifos (fifos_filter_snd (V := V) y m) x = get_fifos m (x, y).
  Proof.
    unfold get_fifos, fifos_filter_snd.
    intros. now rewrite gmap_filter_snd_spec.
  Qed.

  Definition fifos_dep_filter_fst {V} (x : K) :
    fifos_dep (K * K') (V ∘ fst) → fifos K' (V x) :=
    gmap_filter_fst x ∘ gmap_dep_map (fun k =>
      match fst k as x' return (V x' * list (V x')) → option (V x * list (V x)) with
      | x' => fun v =>
        match eq_dec x' x with
        | left EQ => Some (rew [fun k => V k * list (V k)] EQ in v)
        | right NEQ => None
        end%type
      end)
  .

  Lemma fifos_dep_filter_fst_spec {V} (x : K) m :
    ∀ y,
      get_fifos (fifos_dep_filter_fst (V := V) x m) y =
      get_fifos_dep m (x, y).
  Proof.
    unfold get_fifos, fifos_dep_filter_fst, get_fifos_dep, compose.
    intros. rewrite gmap_filter_fst_spec, gmap_dep_map_spec.
    cbn [fst snd]. rewrite eq_dec_refl. cbn [eq_rect].
    destruct (get_dep _ _); auto.
  Qed.

  Lemma fifos_dep_filter_fst_enq {V} (x x' : K) m :
   ∀ y (v : V x'),
     fifos_dep_filter_fst x (enq_fifos_dep m (x', y) v) =
     match eq_dec x' x with
     | left EQ => enq_fifos (fifos_dep_filter_fst x m) y (rew EQ in v)
     | right NEQ => fifos_dep_filter_fst x m
     end.
  Proof.
    intros. apply fifos_ext.
    intros. destruct (eq_dec x' x); subst; cbn [eq_rect];
    rewrite fifos_dep_filter_fst_spec;
    try rewrite get_enq_fifos;
    rewrite get_enq_fifos_dep.
    destruct (eq_dec y k); subst; [rewrite eq_dec_refl|
    destruct (eq_dec _ _); [exfalso;
    match goal with H : _ |- _ => apply pair_inj in H; des; subst; contradiction end|
    ]]; rewrite fifos_dep_filter_fst_spec; reflexivity.
    destruct (eq_dec _ _); [|now rewrite fifos_dep_filter_fst_spec].
    exfalso. apply pair_inj in e; des; subst; auto.
  Qed.

  Lemma fifos_dep_filter_fst_deq {V} (x : K) m :
   ∀ y,
     deq_fifos (fifos_dep_filter_fst (V := V) x m) y =
     match deq_fifos_dep m (x, y) with
     | Some (v, tl) => Some (v, fifos_dep_filter_fst x tl)
     | None => None
     end.
  Proof.
    intros. destruct (deq_fifos_dep _ _) eqn:DEQ.
    - destruct p as [v tl].
      apply deq_fifos_some; intros;
      repeat rewrite fifos_dep_filter_fst_spec.
      now rewrite (deq_fifos_dep_same DEQ).
      rewrite (deq_fifos_dep_diff DEQ); auto.
      inversion 1; subst; auto.
    - apply deq_fifos_none.
      rewrite fifos_dep_filter_fst_spec.
      rewrite deq_fifos_dep_none in *. auto.
  Qed.

  Definition fifos_dep_filter_snd {V} (y : K') :
    fifos_dep (K * K') (V ∘ snd) → fifos K (V y) :=
    gmap_filter_snd y ∘ gmap_dep_map (fun k =>
      match snd k as y' return (V y' * list (V y')) → option (V y * list (V y)) with
      | y' => fun v =>
        match eq_dec y' y with
        | left EQ => Some (rew [fun k => V k * list (V k)] EQ in v)
        | right NEQ => None
        end%type
      end)
  .

  Lemma fifos_dep_filter_snd_spec {V} (y : K') m :
    ∀ x,
      get_fifos (fifos_dep_filter_snd (V := V) y m) x =
      get_fifos_dep m (x, y).
  Proof.
    unfold get_fifos, fifos_dep_filter_snd, get_fifos_dep, compose.
    intros. rewrite gmap_filter_snd_spec, gmap_dep_map_spec.
    cbn [fst snd]. rewrite eq_dec_refl. cbn [eq_rect].
    destruct (get_dep _ _); auto.
  Qed.

  Lemma fifos_dep_filter_snd_enq {V} (y y' : K') m :
   ∀ x (v : V y'),
     fifos_dep_filter_snd y (enq_fifos_dep m (x, y') v) =
     match eq_dec y' y with
     | left EQ => enq_fifos (fifos_dep_filter_snd y m) x (rew EQ in v)
     | right NEQ => fifos_dep_filter_snd y m
     end.
  Proof.
    intros. apply fifos_ext.
    intros. destruct (eq_dec y' y); subst; cbn [eq_rect];
    rewrite fifos_dep_filter_snd_spec;
    try rewrite get_enq_fifos;
    rewrite get_enq_fifos_dep.
    destruct (eq_dec x k); subst; [rewrite eq_dec_refl|
    destruct (eq_dec _ _); [exfalso;
    match goal with H : _ |- _ => apply pair_inj in H; des; subst; contradiction end|
    ]]; rewrite fifos_dep_filter_snd_spec; reflexivity.
    destruct (eq_dec _ _); [|now rewrite fifos_dep_filter_snd_spec].
    exfalso. apply pair_inj in e; des; subst; auto.
  Qed.

  Lemma fifos_dep_filter_snd_deq {V} (y : K') m :
   ∀ x,
     deq_fifos (fifos_dep_filter_snd (V := V) y m) x =
     match deq_fifos_dep m (x, y) with
     | Some (v, tl) => Some (v, fifos_dep_filter_snd y tl)
     | None => None
     end.
  Proof.
    intros. destruct (deq_fifos_dep _ _) eqn:DEQ.
    - destruct p as [v tl].
      apply deq_fifos_some; intros;
      repeat rewrite fifos_dep_filter_snd_spec.
      now rewrite (deq_fifos_dep_same DEQ).
      rewrite (deq_fifos_dep_diff DEQ); auto.
      inversion 1; subst; auto.
    - apply deq_fifos_none.
      rewrite fifos_dep_filter_snd_spec.
      rewrite deq_fifos_dep_none in *. auto.
  Qed.

  Definition fifos_dep_map_dep {V W} (f : ∀ k, V k → W k) :
    fifos_dep K V → fifos_dep K W :=
    gmap_dep_map_dep (fun k => fun x => Some (f k (fst x), map (f k) (snd x)))
  .

  Lemma fifos_dep_map_dep_spec {V W} (f : ∀ k, V k → W k) m :
    ∀ k, get_fifos_dep (fifos_dep_map_dep f m) k =
      map (f k) (get_fifos_dep m k).
  Proof.
    intros. unfold get_fifos_dep, fifos_dep_map_dep.
    rewrite gmap_dep_map_dep_spec. destruct (get_dep m k); auto.
    destruct p; auto.
  Qed.
End fifos_map.
