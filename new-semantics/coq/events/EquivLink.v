From Basics Require Import Basics.
From With_events Require Import Defs.
From With_events Require Import Syntax.
From With_events Require Import SubstFacts.
From With_events Require Import EnvSemantics.
From With_events Require Import EquivSemantics.
From With_events Require Import LinkDefs.
From With_events Require Import LinkFacts.

Section EquivLink.
  Context {var lbl loc : Type}.

  #[local] Coercion vl_ev : vnt >-> vl.
  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  (* local coercions were for this definition *)
  (* definition of Linking *)
  Inductive link' `{Eq var} `{Eq lbl} `{Eq loc} (σ0 : nv var (@ltm var lbl) loc val) :
    wvl var (@ltm var lbl) loc (@val var lbl) -> wvl var (@ltm var lbl) loc (@val var lbl) -> Prop :=
  | link_Init'
  : link' σ0 Init σ0
  | link_Read' E x (σ : nv _ _ _ _) w
    (LINKσ : link' σ0 (nv_ev E) σ)
    (READ : read_env σ x = Env_wvl w)
  : link' σ0 (Read E x) (unroll w)
  | link_CallEval' (E : vnt _ _ _ _) x t σ (v v' v'' : vl _ _ _ _)
    (LINKE : link' σ0 E (vl_clos (v_fn x t) σ))
    (LINKv : link' σ0 v v')
    (EVAL : nv_bval x v' σ ⊢ t ⇓ v'')
  : link' σ0 (Call E v) v''
  | link_CallEvent' (E E' : vnt _ _ _ _) (v v' : vl _ _ _ _)
    (LINKE : link' σ0 E E')
    (LINKv : link' σ0 v v')
  : link' σ0 (Call E v) (Call E' v')
  | link_mt'
  : link' σ0 nv_mt nv_mt
  | link_holeEnv' (E : vnt _ _ _ _) (σ : nv _ _ _ _)
    (LINKE : link' σ0 E σ)
  : link' σ0 (nv_ev E) σ
  | link_holeEvent' (E E' : vnt _ _ _ _)
    (LINKE : link' σ0 E E')
  : link' σ0 (nv_ev E) (nv_ev E')
  | link_floc' x ℓ (σ σ' : nv _ _ _ _)
    (LINKσ : link' σ0 σ σ')
  : link' σ0 (nv_floc x ℓ σ) (nv_floc x ℓ σ')
  | link_bval' x w w' (σ σ' : nv _ _ _ _)
    (LINKw : link' σ0 w w')
    (LINKσ : link' σ0 σ σ')
  : link' σ0 (nv_bval x w σ) (nv_bval x w' σ')
  | link_clos' e (σ σ' : nv _ _ _ _)
    (LINKσ : link' σ0 σ σ')
  : link' σ0 (vl_clos e σ) (vl_clos e σ')
  | link_rec' p (v v' : vl _ _ _ _) L
    (LINKv : forall ℓ (nIN : ~ In ℓ L),
      link' σ0 (open_loc_vl 0 (ℓ, p) v) (open_loc_vl 0 (ℓ, p) v'))
  : link' σ0 (wvl_recv p v) (wvl_recv p v')
  | link_nat' n
  : link' σ0 (vl_nat n) (vl_nat n)
  | link_succNat' (E : vnt _ _ _ _) n
    (LINKE : link' σ0 E (vl_nat n))
  : link' σ0 (Succ E) (vl_nat (S n))
  | link_succEvent' (E E' : vnt _ _ _ _)
    (LINKE : link' σ0 E E')
  : link' σ0 (Succ E) (Succ E')
  | link_predNat' (E : vnt _ _ _ _) n
    (LINKE : link' σ0 E (vl_nat (S n)))
  : link' σ0 (Pred E) (vl_nat n)
  | link_predEvent' (E E' : vnt _ _ _ _)
    (LINKE : link' σ0 E E')
  : link' σ0 (Pred E) (predE E')
  .

  #[local] Lemma equiv_link_l `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc val) (Σ0 : env σ0) w w' (LINK : link σ0 w w') :
    forall φ (INJ : oto φ),
      link' (map_nv φ σ0) (map_wvl φ w) (map_wvl φ w').
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - erewrite <- map_unroll; eauto.
      econstructor; eauto.
      eapply read_env_map; eauto.
    - econstructor; eauto.
      erewrite <- equiv_semantics; eauto.
      eapply eval_map in EVAL; eauto; ss.
      eapply link_lc in LINK1 as EE.
      eapply linked_lc in LINK1 as Σ; eauto.
      inv EE. inv VAL. inv Σ. inv VAL.
      eapply link_lc in LINK2 as V.
      eapply linked_lc in LINK2 as V'; eauto.
      inv V. inv V'.
      repeat constructor; eapply map_lc; eauto.
    - des_goal; ss; econstructor; eauto.
    - econstructor; eauto.
      instantiate (1 := φ ℓ :: floc_nv (map_nv φ σ0) ++ floc_vl (map_vl φ v) ++ floc_vl (map_vl φ v')).
      intros ℓ' nIN. split_nIn.
      assert (map_close_vl v') by eapply map_close. rw; eauto.
      assert (close_open_loc_eq_vl (map_vl φ v')) by eapply close_open_loc_eq. rw.
      assert (value (map_vl φ v')) as V'.
      { eapply map_lc; eauto. eapply linked_lc in LINK; eauto. inv LINK; auto. }
      assert (open_loc_lc_vl (map_vl φ v') V') by (eapply open_loc_lc; eauto). rw.
      set (swap id ℓ' (φ ℓ) <*> φ) as φ'.
      replace (map_nv φ σ0) with (map_nv φ' σ0).
      replace (subst_loc_vl (ℓ', p) (φ ℓ, p) (map_vl φ v')) with (map_vl φ' v').
      exploit (IHLINK φ').
      + subst φ'. unfold compose, swap, id.
        ii; ss; des_ifs;
        repeat match goal with
        | _ => eqb2eq loc
        | H : φ _ = φ _ |- _ => apply INJ in H
        | _ => clarify
        end.
      + assert (map_open_loc_vl v) by eapply map_open_loc. rw.
        replace (φ' ℓ) with ℓ'.
        replace (map_vl φ v) with (map_vl φ' v). auto.
        * eapply map_ext.
          ii. subst φ'. unfold compose, swap, id.
          des_ifs; eqb2eq loc; clarify.
          eapply floc_map in DOM; eauto. contradict.
          exploit INJ; eauto. ii; clarify.
        * subst φ'. unfold compose, swap, id.
          des_ifs; eqb2eq loc; clarify.
      + assert (swap_is_subst_vl (map_vl φ v')) as RR by eapply swap_is_subst.
        specialize (RR id).
        exploit RR; eauto. unfold oto. auto.
        instantiate (1 := p). instantiate (1 := φ ℓ).
        * intros p' IN.
          apply link_map with (φ := φ) in LINK; eauto.
          eapply link_flloc_dec in LINK; eauto. ss; des; des_ifs.
          apply (in_map fst) in LINK; ss.
          assert (trans_floc_nv (map_nv φ σ0)) as RR' by apply trans_floc.
          rewrite <- RR' in LINK. eapply map_floc in LINK; eauto. clarify.
          assert (map_open_loc_vl v) as RR' by apply map_open_loc.
          rewrite RR' in LINK.
          eapply open_loc_flloc in LINK. des; clarify.
          apply (in_map fst) in LINK; ss.
          assert (trans_floc_vl (map_vl φ v)) as RR'' by apply trans_floc.
          rewrite <- RR'' in LINK.
          eapply map_floc in LINK; eauto. clarify.
        * replace (map_vl id (map_vl φ v')) with (map_vl φ v') by (symmetry; eapply map_id_is_id).
          unfold id at 2. unfold id at 2.
          intro. rrw.
          subst φ'. symmetry. eapply map_compose.
      + eapply map_ext.
        ii. subst φ'. unfold compose, swap, id.
        des_ifs; eqb2eq loc; clarify.
        eapply floc_map in DOM; eauto. contradict.
        exploit INJ; eauto. ii; clarify.
    - rewrite predE_map. econstructor; auto.
  Qed.

  #[local] Lemma equiv_link_r `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) w w' (LINK : link' σ0 w w') :
    link σ0 w w'.
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - econstructor; eauto.
      erewrite equiv_semantics; eauto.
      econstructor; eauto.
      eapply linked_lc in IHLINK2; eauto.
      eapply linked_lc in IHLINK1; eauto.
      inv IHLINK1. inv VAL. auto.
    - gensym_tac (floc_nv σ0 ++ floc_vl v ++ floc_vl v' ++ L) ℓ.
      assert (close_vl 0 (ℓ, p) (open_loc_vl 0 (ℓ, p) v') = v') as RR.
      { assert (open_loc_close_vl v') by eapply open_loc_close.
        rw. eapply close_fresh; eauto. }
      rewrite <- RR.
      eapply link_rec; eauto.
  Qed.

  Lemma equiv_link `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) w w' :
    link σ0 w w' <-> link' σ0 w w'.
  Proof.
    split; intro LINK.
    - replace σ0 with (map_nv id σ0) by eapply map_id_is_id.
      replace w with (map_wvl id w) by eapply map_id_is_id.
      replace w' with (map_wvl id w') by eapply map_id_is_id.
      eapply equiv_link_l; eauto.
      ii; ss.
    - eapply equiv_link_r; eauto.
  Qed.

  Ltac Link_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | L : list _ |- _ => instantiate (1 := L)
    end.

  Lemma link_lc' `{Eq var} `{Eq lbl} `{Eq loc} (σ0 : nv var (@ltm var lbl) loc _) (w : wvl var _ loc _) :
    forall w' (LINK : link' σ0 w w'), wvalue w.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    Link_lc_tac; ii.
    match goal with
    | H : forall _, _ |- _ => exploit H; eauto
    end.
    intro W. inv W. auto.
  Qed.
  
  Ltac Linked_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | H : event (_ _) |- _ => inv H
    | L : list _ |- _ => instantiate (1 := L)
    end.

  Lemma linked_lc' `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) (w : wvl var _ loc _) :
    forall w' (LINK : link' σ0 w w'), wvalue w'.
  Proof.
    ii. induction LINK;
    repeat econstructor; des;
    Linked_lc_tac; ii.
    - eapply read_env_lc in READ; auto.
      destruct w; inv READ; ss.
      assert (subst_intro_vl v) by eapply subst_intro.
      gensym_tac (L ++ floc_vl v) ℓ.
      rw; eauto.
      eapply subst_wvl_lc; eauto.
      econstructor; eauto.
    - eapply eval_lc' in EVAL; eauto.
      repeat econstructor; eauto.
    - match goal with
      | H : forall _, _ |- _ => exploit H; eauto
      end.
      intro W. inv W. auto.
  Qed.

  Lemma link_subst_loc' `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (w w' : wvl var _ loc _) (LINK : link' σ0 w w') :
    forall ν ℓ',
      link' (subst_loc_nv ν ℓ' σ0) (subst_loc_wvl ν ℓ' w) (subst_loc_wvl ν ℓ' w').
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - rewrite <- subst_loc_unroll.
      econstructor; eauto.
      erewrite read_env_subst_loc; eauto. ss.
    - specialize (IHLINK1 ν ℓ').
      specialize (IHLINK2 ν ℓ').
      eapply link_CallEval'; eauto.
      apply eval_subst_loc' with (ν := ν) (ℓ' := ℓ') in EVAL; eauto.
    - des_goal; repeat des_hyp; eqb2eq loc; clarify;
      econstructor; eauto.
    - econstructor; eauto.
      instantiate (1 := fst ℓ' :: L).
      intros. split_nIn.
      match goal with
      | H : forall _, _ |- _ => exploit H; eauto
      end.
      instantiate (1 := ℓ'). instantiate (1 := ν).
      assert (open_loc_subst_loc_vl v) by eapply open_loc_subst_loc. rw.
      assert (open_loc_subst_loc_vl v') by eapply open_loc_subst_loc. rw.
      des_goal; ss; repeat des_hyp; eqb2eq loc; clarify.
    - rewrite predE_subst_loc in *.
      econstructor; eauto.
  Qed.

  Lemma link_subst_wvl' `{Eq var} `{Eq lbl} `{Name loc}
    (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) (w w' : wvl var _ loc _) (LINK : link' σ0 w w') :
    forall u u' (LINKu : link' σ0 u u') ℓ' p' (nIN : ~ In ℓ' (floc_nv σ0)),
      link' σ0 (subst_wvl_wvl u (ℓ', p') w) (subst_wvl_wvl u' (ℓ', p') w').
  Proof.
    induction LINK; ii; ss;
    try solve [econstructor; eauto].
    - assert (subst_wvl_fresh_nv σ0) by eapply subst_wvl_fresh. rw; eauto.
      econstructor; eauto.
    - rewrite <- subst_wvl_unroll; eauto.
      econstructor; eauto.
      erewrite read_env_subst_wvl; eauto. ss.
      eapply linked_lc' in LINKu; eauto.
    - specialize (IHLINK1 u u' LINKu ℓ' p' nIN).
      specialize (IHLINK2 u u' LINKu ℓ' p' nIN).
      eapply link_CallEval'; eauto.
      apply eval_subst_wvl' with (u := u') (ℓ' := (ℓ', p')) in EVAL; eauto.
      eapply linked_lc' in LINKu; eauto.
    - des_goal; repeat des_hyp; eqb2eq loc; clarify;
      econstructor; eauto.
    - econstructor; eauto.
      instantiate (1 := ℓ' :: floc_wvl u ++ floc_wvl u' ++ L).
      intros. split_nIn.
      match goal with
      | H : forall _, _ |- _ => exploit H; eauto
      end.
      assert (open_loc_subst_wvl_vl v) by (eapply open_loc_subst_wvl; eauto). rw; eauto.
      assert (open_loc_subst_wvl_vl v') by (eapply open_loc_subst_wvl; eauto). rw; eauto.
      all: try solve [ii; des_ifs; clarify].
      eapply linked_lc' in LINKu; eauto.
      eapply link_lc' in LINKu; eauto.
    - rewrite predE_subst_wvl. econstructor; eauto.
  Qed.

  Lemma link_vl' `{Eq var} `{Eq lbl} `{Eq loc}
    (σ0 : nv var (@ltm var lbl) loc _) (v : vl var _ loc _) w (LINK : link' σ0 v w) :
    match w with
    | wvl_v _ => True
    | _ => False
    end.
  Proof.
    inv LINK; clarify.
  Qed.

  Lemma link_read' `{Eq var} `{Eq lbl} `{Name loc} (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) :
    forall (σ : nv var _ loc _) (σ' : wvl var _ loc _) (LINK : link' σ0 σ σ'),
    match σ' with
    | wvl_v (vl_exp σ') =>
      forall x w' (READ : read_env σ' x = Env_wvl w'),
        exists w, read_env σ x = Env_wvl w /\ (link' σ0 (unroll w) (unroll w'))
    | _ => False
    end.
  Proof.
    induction σ; ii; ss;
    repeat des_goal; inv LINK; clarify; ii.
    - exists (Read E x).
      split; eauto. ss.
      econstructor; eauto.
      econstructor; eauto.
    - exists (Read E x).
      split; auto.
      econstructor; eauto.
      eapply link_holeEvent'; eauto.
    - ss; des_ifs; eqb2eq var; clarify.
      exploit IHσ; eauto.
    - ss; des_ifs; eqb2eq var; clarify.
      + exists w. split; auto.
        destruct w; ss.
        * eapply link_vl' in LINKw as HINT.
          des_hyp; clarify.
        * inv LINKw; ss.
          gensym_tac (L ++ floc_nv σ0 ++ floc_vl v' ++ floc_vl v) ℓ.
          assert (subst_intro_vl v') by eapply subst_intro.
          rw; eauto.
          assert (subst_intro_vl v) by eapply subst_intro.
          rw; eauto.
          repeat match goal with
          | |- context [wvl_v (subst_wvl_vl ?a ?b ?c)] =>
            replace (wvl_v (subst_wvl_vl a b c)) with
              (subst_wvl_wvl a b (wvl_v c)) by reflexivity
          end.
          eapply link_subst_wvl'; eauto.
          econstructor; eauto.
      + exploit IHσ; eauto.
  Qed.

  Lemma link_predENat' `{Eq var} `{Eq lbl} `{Name loc} (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) :
    forall (E : vnt _ _ _ _) n,
      link' σ0 E (vl_nat (S n)) -> link' σ0 (predE E) (vl_nat n).
  Proof.
    intros E n LINK; destruct E; simpl in *;
    try solve [inv LINK; auto | eapply link_predNat'; auto].
  Qed.

  Lemma link_predEEvent' `{Eq var} `{Eq lbl} `{Name loc} (σ0 : nv var (@ltm var lbl) loc _) (Σ0 : env σ0) :
    forall (E E' : vnt _ _ _ _),
      link' σ0 E E' -> link' σ0 (predE E) (predE E').
  Proof.
    intros E n LINK; destruct E; simpl in *;
    try solve [inv LINK; auto | eapply link_predEvent'; auto].
  Qed.
End EquivLink.

Notation " σ '⋊' w '∋' v " := (link' σ w v)
  (at level 100, w at next level, v at next level, right associativity).

