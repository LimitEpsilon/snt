From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import LinkDefs.

Section LinkFacts.
  Variable var : Type.
  Variable loc : Type.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Ltac link_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | _ => instantiate (1 := [])
    end.

  Lemma link_lc `{Eq loc} `{Eq var} (σ0 : nv var loc _) (w : wvl var loc _) :
    forall w' (LINK : σ0 ⋊ w ∋ w'), wvalue w.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    link_lc_tac; ii.
    all: match goal with
    | RR : _ = open_loc_vl 0 ?ν ?v |- value (open_loc_vl 0 ?ℓ ?v) =>
      assert (value (open_loc_vl 0 ν v)) by (rewrite <- RR; constructor; auto);
      replace (open_loc_vl 0 ℓ v) with (subst_loc_vl ℓ ν (open_loc_vl 0 ν v))
    end.
    all: try match goal with
    | V : value ?v |- value (subst_loc_vl _ _ ?v) =>
      assert (subst_loc_lc_vl _ _ _ v V) by eapply subst_loc_lc; auto
    | |- context [subst_loc_vl ?ℓ ?ν (open_loc_vl 0 ?ν ?v)] =>
      assert (open_loc_subst_loc_vl _ _ _ v) by eapply open_loc_subst_loc;
      rw; rewrite eqb_refl;
      f_equal; eapply subst_loc_fresh; auto
    end.
  Qed.

  Ltac linked_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | _ => instantiate (1 := [])
    end.

  Lemma linked_lc_wvl `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (Σ0 : env σ0) (w : wvl var loc _) :
    forall w' (LINK : σ0 ⋊ w ∋ w'), wvalue w'.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    linked_lc_tac; ii.
    - eapply read_env_lc in READ; auto.
      destruct w; inv READ; ss.
      assert (subst_intro_vl _ _ _ v) by eapply subst_intro.
      gensym_tac (L ++ floc_vl v) ℓ.
      rw; eauto.
      eapply subst_wvl_lc; eauto.
      econstructor; eauto.
    - eapply eval_lc in EVAL; eauto.
      repeat econstructor; eauto.
    - assert (close_open_loc_eq_vl _ _ _ v') by eapply close_open_loc_eq.
      rw.
      assert (open_loc_lc_vl _ _ _ v' VAL) by (eapply open_loc_lc; eauto).
      rw.
      eapply subst_loc_lc; auto.
  Qed.

  Lemma map_unroll {lang} `{Eq loc} φ (w : wvl var loc lang) :
    unroll (map_wvl φ w) = map_vl φ (unroll w).
  Proof.
    destruct w; ss.
    assert (map_open_wvl_vl _ _ _ v) by eapply map_open_wvl.
    rw; ss.
  Qed.

  Lemma subst_loc_unroll {lang} `{Eq loc}
    ℓ ν (w : wvl var loc lang) :
    unroll (subst_loc_wvl ν ℓ w) = subst_loc_vl ν ℓ (unroll w).
  Proof.
    destruct w; ss.
    match goal with
    | |- context [subst_loc_vl _ _ (open_wvl_vl _ _ ?v)] =>
      assert (open_wvl_subst_loc_vl _ _ _ v)
        by (eapply open_wvl_subst_loc; eauto);
      rw; ss
    end.
  Qed.

  Lemma subst_wvl_unroll {lang} `{Name loc}
    ℓ (u w : wvl var loc lang) (U : wvalue u) :
    unroll (subst_wvl_wvl u ℓ w) = subst_wvl_vl u ℓ (unroll w).
  Proof.
    destruct w; ss.
    match goal with
    | |- context [subst_wvl_vl _ _ (open_wvl_vl _ _ ?v)] =>
      assert (open_wvl_subst_wvl_vl _ _ _ v)
        by (eapply open_wvl_subst_wvl; eauto);
      rw; ss
    end.
  Qed.

  Lemma unroll_floc {lang} ℓ (w : wvl var loc lang) :
    In ℓ (floc_wvl w) <-> In ℓ (floc_vl (unroll w)).
  Proof.
    split; intro IN; destruct w; ss.
    - eapply open_wvl_inc_floc. auto.
    - eapply open_wvl_floc in IN. ss; des; auto.
  Qed.

  Lemma link_floc_dec `{Eq loc} `{Eq var}
    (σ0 : nv var loc _) (w w' : wvl var loc _) (LINK : σ0 ⋊ w ∋ w') :
    forall ℓ (IN : In ℓ (floc_wvl w')), In ℓ (floc_nv σ0) \/ In ℓ (floc_wvl w).
  Proof.
    induction LINK; ii; ss;
    repeat match goal with
    | _ => solve [auto]
    | _ => rewrite in_app_iff
    | EVAL : context [eval] |- _ => eapply eval_floc_dec in EVAL; eauto; ss
    | IN : In _ (floc_vl (unroll _)) |- _ => rewrite <- unroll_floc in IN
    | IN : In _ (?a ++ ?b) |- _ => rewrite in_app_iff in IN
    | IN : _ \/ _ |- _ => destruct IN as [IN | IN]
    | IN : In _ ?l, Hl : forall x, In x ?l -> _ |- _ => specialize (Hl _ IN)
    end.
    - eapply IHLINK.
      eapply read_env_floc; eauto.
    - eapply close_floc in IN.
      des; exploit IHLINK; eauto; intro IN'; des; auto.
      eapply open_floc in IN'; des; clarify; auto.
  Qed.

  Lemma link_map `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (w w' : wvl var loc _) (LINK : σ0 ⋊ w ∋ w') :
    forall φ (INJ : oto φ),
      map_nv φ σ0 ⋊ map_wvl φ w ∋ map_wvl φ w'.
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - rewrite <- map_unroll.
      apply read_env_map with (φ := φ) in READ.
      econstructor; eauto.
    - specialize (IHLINK1 φ INJ).
      specialize (IHLINK2 φ INJ).
      eapply link_CallEval; eauto.
      eapply eval_map with (φ := φ) in EVAL; eauto.
    - assert (map_close_vl _ _ _ v') by (eapply map_close; eauto).
      rw; eauto.
      econstructor; eauto;
      match goal with
      | |- ~ In _ _ =>
        intro IN; eapply map_floc in IN; eauto
      | _ =>
        specialize (IHLINK φ INJ);
        assert (map_open_loc_vl _ _ _ v) as RR by (eapply map_open_loc; eauto);
        rewrite RR in *; auto
      end.
  Qed.

  Lemma link_map_subst_loc `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (w w' : wvl var loc _) (LINK : σ0 ⋊ w ∋ w') :
    forall φ (INJ : oto φ) ν ℓ',
      subst_loc_nv ν ℓ' (map_nv φ σ0) ⋊
      subst_loc_wvl ν ℓ' (map_wvl φ w) ∋
      subst_loc_wvl ν ℓ' (map_wvl φ w').
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - rewrite <- map_unroll.
      rewrite <- subst_loc_unroll.
      apply read_env_map with (φ := φ) in READ.
      econstructor; eauto.
      apply read_env_subst; auto.
    - specialize (IHLINK1 φ INJ ν ℓ').
      specialize (IHLINK2 φ INJ ν ℓ').
      eapply link_CallEval; eauto.
      eapply eval_map_subst_loc with (ν := ν) (ℓ' := ℓ') in EVAL; eauto.
      assumption.
    - des_goal; eqb2eq loc; clarify;
      econstructor; eauto.
    - assert (map_close_vl _ _ _ v') as RR by (eapply map_close; auto).
      rewrite RR; eauto. clear RR.
      gensym_tac (ℓ' :: φ ℓ :: ν :: floc_nv (map_nv φ σ0) ++ floc_vl (map_vl φ v)) ℓ''.
      clear Heqℓ''.
      assert (~ In ℓ'' (floc_vl (map_vl φ v'))) as HINT.
      { intro. apply link_map with (φ := φ) in LINK; auto; ss.
        eapply link_floc_dec in LINK; eauto. des; ss.
        assert (map_open_loc_vl _ _ _ v) as RR by (eapply map_open_loc; eauto).
        rewrite RR in *. eapply open_floc in LINK. des; ss; clarify. }
      replace
        (close_vl 0 (φ ℓ) (map_vl φ v')) with
        (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v'))) by
      (eapply subst_loc_close_eq; auto).
      replace 
        (subst_loc_vl ν ℓ' (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v')))) with
        (close_vl 0 ℓ'' (subst_loc_vl ν ℓ' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v')))) by
      (eapply subst_loc_close; auto).
      econstructor; eauto.
      { intro IN. eapply floc_subst_loc in IN. des; auto. }
      { intro IN. eapply floc_subst_loc in IN. des; auto. }
      { set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
        exploit (IHLINK φ' _ ν).
        subst φ'. unfold compose, swap, id.
        ii; ss; des_ifs;
        repeat match goal with
        | _ => eqb2eq loc
        | H : φ _ = φ _ |- _ => apply INJ in H
        | _ => clarify
        end.
        instantiate (1 := ℓ').
        assert (map_open_loc_vl _ _ _ v) as RR by (eapply map_open_loc; eauto).
        rw. clear RR. replace (φ' ℓ) with ℓ''.
        assert (open_loc_subst_loc_vl _ _ _ (map_vl φ' v)) as RR by (eapply open_loc_subst_loc; eauto).
        rw. clear RR. replace (eqb ℓ' ℓ'') with false.
        replace (map_nv φ σ0) with (map_nv φ' σ0).
        replace (map_vl φ v) with (map_vl φ' v).
        replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v')) with (map_vl φ' v').
        auto.
        { assert (swap_is_subst_vl _ _ _ (map_vl φ v')) as RR by eapply swap_is_subst.
          specialize (RR id).
          exploit RR; eauto. unfold oto. auto.
          instantiate (1 := φ ℓ).
          replace (map_vl id (map_vl φ v')) with (map_vl φ v') by (symmetry; eapply map_id_is_id).
          unfold id at 2. unfold id at 2.
          intro. rrw.
          subst φ'. symmetry. eapply map_compose. }
        { eapply map_ext.
          ii. subst φ'. unfold compose, swap, id.
          des_ifs; eqb2eq loc; clarify.
          eapply floc_map in DOM; eauto. contradict.
          exploit INJ; eauto. ii; clarify. }
        { eapply map_ext.
          ii. subst φ'. unfold compose, swap, id.
          des_ifs; eqb2eq loc; clarify.
          eapply floc_map in DOM; eauto. contradict.
          exploit INJ; eauto. ii; clarify. }
        { symmetry. eqb2eq loc. auto. }
        { subst φ'. unfold compose, swap, id.
          rewrite eqb_refl. des_goal; eqb2eq loc; clarify. } }
  Qed.

  Lemma link_subst_loc `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (w w' : wvl var loc _) (LINK : σ0 ⋊ w ∋ w') :
    forall ν ℓ',
      subst_loc_nv ν ℓ' σ0 ⋊ subst_loc_wvl ν ℓ' w ∋ subst_loc_wvl ν ℓ' w'.
  Proof.
    intros.
    replace σ0 with (map_nv id σ0) by apply map_id_is_id.
    replace w with (map_wvl id w) by apply map_id_is_id.
    replace w' with (map_wvl id w') by apply map_id_is_id.
    eapply link_map_subst_loc; try intro; auto.
  Qed.

  Lemma link_map_subst_wvl `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (Σ0 : env σ0) (w w' : wvl var loc _) (LINK : σ0 ⋊ w ∋ w') :
    forall φ (INJ : oto φ) u u' (LINKu : map_nv φ σ0 ⋊ u ∋ u') ℓ' (nIN : ~ In ℓ' (floc_nv (map_nv φ σ0))),
      map_nv φ σ0 ⋊
      subst_wvl_wvl u ℓ' (map_wvl φ w) ∋
      subst_wvl_wvl u' ℓ' (map_wvl φ w').
  Proof.
    do 4 intros.
    eapply link_lc in LINKu as U.
    eapply linked_lc_wvl in LINKu as U';
    try eapply map_lc; eauto.
    revert_until LINK.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - assert (subst_wvl_fresh_nv _ _ _ (map_nv φ σ0)) by (eapply subst_wvl_fresh; eauto).
      rw; eauto. econstructor; eauto.
    - rewrite <- map_unroll.
      rewrite <- subst_wvl_unroll; auto.
      apply read_env_map with (φ := φ) in READ.
      econstructor; eauto.
      erewrite read_env_wvl; eauto; ss.
    - specialize (IHLINK1 φ INJ u u' LINKu ℓ' nIN U U').
      specialize (IHLINK2 φ INJ u u' LINKu ℓ' nIN U U').
      eapply link_CallEval; eauto.
      eapply eval_map_subst_wvl with (u := u') (ℓ' := ℓ') in EVAL; eauto.
      assumption.
    - des_goal; eqb2eq loc; clarify;
      try solve [econstructor; eauto].
    - assert (map_close_vl _ _ _ v') as RR by (eapply map_close; auto).
      rewrite RR; eauto. clear RR.
      gensym_tac (ℓ' :: φ ℓ :: floc_wvl u ++ floc_nv (map_nv φ σ0) ++ floc_vl (map_vl φ v)) ℓ''.
      clear Heqℓ''.
      assert (~ In ℓ'' (floc_vl (map_vl φ v'))) as HINT.
      { intro. apply link_map with (φ := φ) in LINK; auto; ss.
        eapply link_floc_dec in LINK; eauto. des; ss.
        assert (map_open_loc_vl _ _ _ v) as RR by (eapply map_open_loc; eauto).
        rewrite RR in *. eapply open_floc in LINK. des; ss; clarify. }
      assert (~ In ℓ'' (floc_wvl u')) as HINT'.
      { intro. eapply link_floc_dec in LINKu; eauto. des; ss. }
      replace
        (close_vl 0 (φ ℓ) (map_vl φ v')) with
        (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v'))) by
      (eapply subst_loc_close_eq; auto).
      replace 
        (subst_wvl_vl u' ℓ' (close_vl 0 ℓ'' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v')))) with
        (close_vl 0 ℓ'' (subst_wvl_vl u' ℓ' (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v')))) by
      (eapply subst_wvl_close; auto).
      econstructor; eauto.
      { intro IN. eapply floc_subst_wvl in IN. des; auto. }
      { set (compose loc (swap id ℓ'' (φ ℓ)) φ) as φ'.
        assert (map_nv φ σ0 = map_nv φ' σ0) as HINT''.
        { eapply map_ext.
          ii. subst φ'. unfold compose, swap, id.
          des_ifs; eqb2eq loc; clarify.
          eapply floc_map in DOM; eauto. contradict.
          exploit INJ; eauto. ii; clarify. }
        exploit (IHLINK φ' _ u u'); eauto; try instantiate (1 := ℓ').
        subst φ'. unfold compose, swap, id.
        ii; ss; des_ifs;
        repeat match goal with
        | _ => eqb2eq loc
        | H : φ _ = φ _ |- _ => apply INJ in H
        | _ => clarify
        end.
        all: rrw; auto.
        assert (map_open_loc_vl _ _ _ v) as RR by (eapply map_open_loc; eauto).
        rw. clear RR. replace (φ' ℓ) with ℓ''.
        assert (open_loc_subst_wvl_vl _ _ _ (map_vl φ' v)) as RR by (eapply open_loc_subst_wvl; eauto).
        rw; eauto. clear RR.
        replace (map_vl φ v) with (map_vl φ' v).
        replace (subst_loc_vl ℓ'' (φ ℓ) (map_vl φ v')) with (map_vl φ' v').
        auto.
        { assert (swap_is_subst_vl _ _ _ (map_vl φ v')) as RR by eapply swap_is_subst.
          specialize (RR id).
          exploit RR; eauto. unfold oto. auto.
          instantiate (1 := φ ℓ).
          replace (map_vl id (map_vl φ v')) with (map_vl φ v') by (symmetry; eapply map_id_is_id).
          unfold id at 2. unfold id at 2.
          intro. rrw.
          subst φ'. symmetry. eapply map_compose. }
        { eapply map_ext.
          ii. subst φ'. unfold compose, swap, id.
          des_ifs; eqb2eq loc; clarify.
          eapply floc_map in DOM; eauto. contradict.
          exploit INJ; eauto. ii; clarify. }
        { subst φ'. unfold compose, swap, id.
          rewrite eqb_refl. des_goal; eqb2eq loc; clarify. } }
  Qed.

  Lemma link_subst_wvl `{Name loc} `{Eq var}
    (σ0 : nv var loc _) (Σ0 : env σ0) (w w' : wvl var loc _) (LINK : σ0 ⋊ w ∋ w') :
    forall u u' (LINKu : σ0 ⋊ u ∋ u') ℓ' (nIN : ~ In ℓ' (floc_nv σ0)),
      σ0 ⋊ subst_wvl_wvl u ℓ' w ∋ subst_wvl_wvl u' ℓ' w'.
  Proof.
    intros.
    assert (map_nv id σ0 = σ0) as RR by apply map_id_is_id.
    rewrite <- RR.
    replace w with (map_wvl id w) by apply map_id_is_id.
    replace w' with (map_wvl id w') by apply map_id_is_id.
    eapply link_map_subst_wvl; try rewrite RR; try intro; eauto.
  Qed.

  Lemma link_vl `{Eq loc} `{Eq var} (σ0 : nv var loc _) (v : vl var loc _) w (LINK : σ0 ⋊ v ∋ w) :
    match w with
    | wvl_v _ => True
    | _ => False
    end.
  Proof.
    inv LINK; clarify.
  Qed.

  Lemma link_read `{Name loc} `{Eq var} (σ0 : nv var loc _) (Σ0 : env σ0) :
    forall (σ : nv var loc _) x (w w' σ' : wvl var loc _)
      (LINK : σ0 ⋊ σ ∋ σ')
      (READ : read_env σ x = Env_wvl w),
    match σ' with
    | wvl_v (vl_exp σ') =>
      read_env σ' x = Env_wvl w' -> (σ0 ⋊ unroll w ∋ unroll w')
    | _ => False
    end.
  Proof.
    induction σ; ii; ss; repeat des_goal; inv LINK; clarify.
    - intros. repeat econstructor; eauto.
    - intros. ss; clarify. econstructor.
      instantiate (1 := nv_ev E').
      eapply link_holeEvent; auto. ss.
    - ss; des_ifs; eqb2eq var.
      ii. exploit IHσ; eauto.
    - ss; des_ifs; eqb2eq var; clarify.
      + ii; clarify;
        match goal with
        | |- context [unroll ?w] =>
          destruct w; ss
        end.
        * eapply link_vl in LINKw as HINT.
          destruct w'; clarify.
        * inv LINKw; ss.
          assert (subst_intro_vl _ _ _ (close_vl 0 ℓ v')) by eapply subst_intro.
          rw. instantiate (1 := ℓ).
          assert (close_open_loc_eq_vl _ _ _ v') by eapply close_open_loc_eq.
          rw.
          assert (subst_id_vl _ _ _ (open_loc_vl 0 ℓ v')) by eapply subst_id.
          rw.
          assert (subst_intro_vl _ _ _ v) by eapply subst_intro.
          rw. instantiate (1 := ℓ).
          repeat match goal with
          | |- context [wvl_v (subst_wvl_vl ?a ?b ?c)] =>
            replace (wvl_v (subst_wvl_vl a b c)) with
              (subst_wvl_wvl a b (wvl_v c)) by reflexivity
          end.
          eapply link_subst_wvl; eauto.
          eapply linked_lc_wvl in LINKv as V'; eauto. inv V'.
          assert (open_loc_lc_vl _ _ _ v' VAL) by (eapply open_loc_lc; eauto).
          rw. auto.
          econstructor; eauto.
          auto.
          intro IN. eapply close_floc in IN. des; clarify.
      + exploit IHσ; eauto.
  Qed.
End LinkFacts.
