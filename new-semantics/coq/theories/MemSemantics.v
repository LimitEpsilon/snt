From Basics Require Import Basics.
From LN Require Import Defs.
From LN Require Import Syntax.
From LN Require Import SubstFacts.
From LN Require Import EquivFacts.
From LN Require Import EnvSemantics.

Fixpoint read_menv {var loc} `{Eq var} (σ : menv var loc) (x : var) :=
  match σ with
  | [] => None
  | (x', ℓ) :: σ' =>
    if eqb x x' then Some ℓ else read_menv σ' x
  end.

Inductive meval {var loc} `{Eq var} `{Eq loc} (σ : menv var loc) (m : memory var loc val) (L : list loc) :
  (@tm var) -> (mvalue var loc (@val var)) -> (memory var loc (@val var)) -> list loc -> Prop :=
| mev_id x ℓ v
  (READσ : read_menv σ x = Some ℓ)
  (READm : m ℓ = Some v)
: meval σ m L (tm_var x) v m L
| mev_fn x t
: meval σ m L (tm_lam x t) (mvalue_clos (v_fn x t) σ) m L
| mev_app t1 t2 x t σ1 m1 L1 v2 m2 L2 ℓ v m' L'
  (FN : meval σ m L t1 (mvalue_clos (v_fn x t) σ1) m1 L1)
  (ARG : meval σ m1 L1 t2 v2 m2 L2)
  (DOMm : m2 ℓ = None)
  (DOML : ~ In ℓ L2)
  (BODY : meval ((x, ℓ) :: σ1) (ℓ !-> v2 ; m2) L2 t v m' L')
: meval σ m L (tm_app t1 t2) v m' L'
| mev_link t1 t2 σ1 m1 L1 v m' L'
  (MOD : meval σ m L t1 (mvalue_exp σ1) m1 L1)
  (IMP : meval σ1 m1 L1 t2 v m' L')
: meval σ m L (tm_link t1 t2) v m' L'
| mev_mt
: meval σ m L tm_mt (mvalue_exp []) m L
| mev_bind x t1 t2 ℓ v1 m1 L1 σ2 m' L'
  (DOM : m ℓ = None)
  (FRESH : ~ In ℓ L)
  (BIND : meval ((x, ℓ) :: σ) m (ℓ :: L) t1 v1 m1 L1)
  (MOD : meval ((x, ℓ) :: σ) (ℓ !-> v1 ; m1) L1 t2 (mvalue_exp σ2) m' L')
: meval σ m L (tm_bind x t1 t2) (mvalue_exp ((x, ℓ) :: σ2)) m' L'
.

Fixpoint distinct {T} (l : list T) :=
  match l with
  | [] => True
  | hd :: tl => ~ In hd tl /\ distinct tl
  end.

Fixpoint delete {T} `{Eq T} (l : list T) (t : T) :=
  match l with
  | [] => []
  | hd :: tl =>
    if eqb t hd then delete tl t else hd :: (delete tl t)
  end.

Fixpoint diff {T} `{Eq T} (a b : list T) :=
  match b with
  | [] => a
  | hd :: tl => diff (delete a hd) tl
  end.

Lemma delete_in {T} `{Eq T} (l : list T) :
  forall x ℓ,
    In ℓ (delete l x) <-> In ℓ l /\ ℓ <> x.
Proof.
  induction l; ii; ss. tauto.
  des_ifs; eqb2eq T; ss; clarify.
  firstorder. contradict.
  firstorder. clarify. auto.
Qed.

Lemma delete_distinct {T} `{Eq T} (l : list T) :
  forall x (DIST : distinct l), distinct (delete l x).
Proof.
  induction l; ii; ss. des.
  des_ifs; eqb2eq T; clarify; ss; eauto.
  split; eauto.
  ii. rewrite delete_in in *. des; clarify.
Qed. 

Lemma delete_free {T} `{Eq T} (l : list T) :
  forall x (nIN : ~ In x l),
    delete l x = l.
Proof.
  induction l; ii; ss.
  split_nIn. des_ifs; eqb2eq T; clarify.
  rw; eauto.
Qed.

Lemma delete_len {T} `{Eq T} (l : list T) :
  forall x (DIST : distinct l),
    length l - 1 <= length (delete l x).
Proof.
  induction l; ii; ss.
  des; des_ifs; eqb2eq T; clarify.
  rewrite delete_free; eauto. nia.
  s. exploit IHl; eauto. instantiate (1 := x).
  nia.
Qed.

Lemma diff_in {T} `{Eq T} (b : list T) :
  forall a x,
    In x (diff a b) <-> In x a /\ ~ In x b.
Proof.
  induction b; ii; ss. tauto.
  rw. rewrite delete_in. firstorder.
Qed.

Lemma diff_len {T} `{Eq T} (b : list T) :
  forall a (DIST : distinct a) (LE : length b <= length a),
    length a - length b <= length (diff a b).
Proof.
  induction b; ii; ss. nia.
  eapply delete_len with (x := a) in DIST as LEN.
  exploit (IHb (delete a0 a)).
  apply delete_distinct.
  all: first [nia | auto].
Qed.

Lemma list_spill {T} `{Eq T} :
  forall (a b : list T) (LEN : length a < length b)
    (DISb : distinct b),
  exists x, In x b /\ ~ In x a.
Proof.
  ii. remember (diff b a) as l.
  exploit (diff_len a b DISb). nia.
  rrw. destruct l; ii; ss. nia.
  exists t. apply diff_in. rrw. s. auto.
Qed.

Lemma map_distinct {loc} `{Eq loc} (l : list loc) :
  forall (DIST : distinct l) (f : loc -> loc) (INJ : forall ℓ ν (fEQ : f ℓ = f ν), ℓ = ν),
    distinct (map f l).
Proof.
  induction l; ii; ss.
  des. split; eauto.
  red. intros IN. clear DIST0 IHl.
  ginduction l; ii; ss; split_nIn; des; clarify.
  apply INJ in IN. clarify.
  exploit IHl; eauto.
Qed.

Lemma map_in {loc} `{Eq loc} (l : list loc) :
  forall y (f : loc -> loc) (INJ : forall ℓ ν (fEQ : f ℓ = f ν), ℓ = ν) (IN : In y (map f l)),
    exists x, In x l /\ f x = y.
Proof.
  induction l; ii; ss; des; clarify; eauto.
  exploit IHl; eauto. ii; des; eauto.
Qed.

Fixpoint genlist {loc} `{Name loc} L n :=
  match n with
  | 0 => []
  | S n' =>
    let L' := genlist L n' in
    let ℓ := gensym (L' ++ L) in
    ℓ :: L'
  end.

Lemma genlist_length {loc} `{Name loc} n :
  forall L, length (genlist L n) = n.
Proof.
  induction n; ii; ss. rw. eauto.
Qed.

Lemma genlist_distinct {loc} `{Name loc} n :
  forall L, distinct (genlist L n).
Proof.
  induction n; ii; ss. split; auto.
  ii. exploit gensym_spec; eauto.
  instantiate (1 := genlist L n ++ L).
  rewrite in_app_iff. auto.
Qed.

Lemma genlist_avoid {loc} `{Name loc} n :
  forall L x (IN : In x (genlist L n)), ~ In x L.
Proof.
  induction n; ii; ss. des; eauto.
  exploit gensym_spec; eauto.
  instantiate (1 := genlist L n ++ L). rw.
  rewrite in_app_iff; auto.
  exploit IHn; eauto.
Qed.

Lemma avoid_dom_ran {loc} `{Name loc} L :
  forall L' (f : loc -> loc) (INJ : forall ℓ ν (fEQ : f ℓ = f ν), ℓ = ν),
    exists x, ~ In x L /\ ~ In (f x) L'.
Proof.
  ii. remember (genlist L (1 + length L')) as l.
  exploit (list_spill L' (map f l)).
  rewrite map_length. rw. rewrite genlist_length. auto.
  apply map_distinct; auto. rw. apply genlist_distinct.
  ii; des. exploit map_in; eauto.
  rw. intros (x' & IN' & EQ').
  apply genlist_avoid in IN'.
  exists x'. rw. eauto.
Qed.

Definition fin {A B} (f : A -> option B) :=
  exists dom, forall x (fDOM : ~ In x dom), f x = None.

Definition bot {A B} : A -> option B := fun x => None.

Definition Equiv {var loc} `{Eq var} `{Eq loc} (w : wvl var loc (@val var)) W m L :=
  equiv w bot W m /\ (forall ℓ (IN : In ℓ (floc_wvl w)), In ℓ L).

#[local] Coercion vl_exp : nv >-> vl.
#[local] Coercion wvl_v : vl >-> wvl.

Lemma fin_pres {var loc} `{Eq var} `{Eq loc} (σ : menv var loc) m L t v' m' L'
  (EVAL : meval σ m L t v' m' L') :
  forall (FIN : fin m), fin m'.
Proof.
  induction EVAL; ii; ss; try_all; auto.
  all: match goal with
  | H : fin _ -> fin ?m |- fin (?ℓ !-> _ ; ?m) =>
    exploit H; eauto; intros (dom & FIN');
    red; exists (ℓ :: dom); ii; split_nIn;
    unfold update; des_ifs; eqb2eq loc; clarify
  end.
  all:auto.
Qed.

Lemma L_inc {var loc} `{Eq var} `{Eq loc} (σ : menv var loc) m L t v' m' L'
  (EVAL : meval σ m L t v' m' L') :
  forall ℓ (IN : In ℓ L), In ℓ L'.
Proof.
  induction EVAL; ii; ss; eauto.
Qed.

Lemma m_pres {var loc} `{Eq var} `{Eq loc} (σ : menv var loc) m L t v' m' L'
  (EVAL : meval σ m L t v' m' L') :
  forall ℓ (INℓ : In ℓ L), m' ℓ = m ℓ.
Proof.
  induction EVAL; ii; ss; repeat rw; eauto.
  all: first[eapply (@L_inc var loc); eauto |
    unfold update; des_ifs; eqb2eq loc; clarify].
  all: first[solve [s; auto] |
    eapply (@L_inc var loc); eauto |
    eapply (@L_inc var loc) in EVAL1; eauto].
  eapply (@L_inc var loc) in EVAL2; eauto. clarify.
  repeat rw; eauto.
Qed.

Lemma m_inc {var loc} `{Eq var} `{Eq loc} (σ : menv var loc) m L t v' m' L'
  (EVAL : meval σ m L t v' m' L') :
  forall ℓ (DOM : m ℓ <> None), m' ℓ = m ℓ.
Proof.
  induction EVAL; ii; ss; repeat rw; eauto;
  unfold update; des_ifs; eqb2eq loc;
  repeat rw; eauto; clarify.
  exfalso.
  exploit IHEVAL1; eauto. ii.
  exploit IHEVAL2; eauto. rw. auto.
  rewrite DOMm. rw. auto.
Qed.

Lemma equiv_read_env {var loc} `{Eq var} `{Name loc} (σ : nv var loc (@val var)) :
  forall σ' m x v
    (EQUIV : equiv σ bot (mvalue_exp σ') m)
    (READ : read_env σ x = Env_wvl v),
  exists ℓ v',
    read_menv σ' x = Some ℓ /\
    m ℓ = Some v' /\
    equiv v bot v' m.
Proof.
  induction σ; ii; ss; des_ifs; eqb2eq var; clarify;
  inv EQUIV; ss; clarify.
  - exploit IHσ; eauto. ii; des.
    repeat eexists; eauto; des_ifs; eqb2eq var; clarify.
  - exists ℓ'. exists v'. rewrite eqb_refl. eauto.
  - exploit IHσ; eauto. ii; des.
    repeat eexists; eauto; des_ifs; eqb2eq var; clarify.
Qed.

Lemma equiv_read_menv {var loc} `{Eq var} `{Name loc} (σ' : menv var loc) :
  forall (σ : nv var loc (@val var)) m x ℓ v'
    (EQUIV : equiv σ bot (mvalue_exp σ') m)
    (READσ : read_menv σ' x = Some ℓ)
    (READm : m ℓ = Some v'),
  exists v,
    read_env σ x = Env_wvl v /\
    equiv v bot v' m.
Proof.
  induction σ'; ii; ss; des_ifs; eqb2eq var; clarify;
  inv EQUIV; ss; clarify.
  - exists w. rewrite eqb_refl. eauto.
  - exploit IHσ'; eauto. ii; des.
    repeat eexists; eauto; des_ifs; eqb2eq var; clarify.
  - exploit IHσ'; eauto. ii; des.
    repeat eexists; eauto; des_ifs; eqb2eq var; clarify.
Qed.

Lemma equiv_l {var loc} `{Eq var} `{Name loc} (σ : nv var loc val) t v (EVAL : eval σ t v) :
  forall φ σ' m L (FIN : fin m)
    (INJ : forall ℓ ν (fEQ : φ ℓ = φ ν), ℓ = ν)
    (EQUIV : Equiv (map_nv φ σ) (mvalue_exp σ') m L),
    exists v' m' L',
      (meval σ' m L t v' m' L') /\
      (Equiv (map_vl φ v) v' m' L').
Proof.
  induction EVAL; ii; ss.
  - exploit (@read_env_map var loc); eauto; s.
    instantiate (1 := φ). ii.
    exploit (@equiv_read_env var loc); eauto.
    apply EQUIV. ii. des.
    exists v'. exists m. exists L.
    split. econstructor; eauto.
    split. eauto. ii; ss.
    exploit (@read_env_floc var loc); eauto.
    ii; ss. apply EQUIV. ss.
  - exploit (@read_env_map var loc); eauto; s.
    instantiate (1 := φ). intros RR.
    exploit (@equiv_read_env var loc); eauto.
    apply EQUIV. intros (ℓ & v' & READσ' & READm & EQUIV').
    exists v'. exists m. exists L.
    assert (map_open_wvl_vl _ _ _ v) by apply map_open_wvl.
    split. econstructor; eauto.
    destruct EQUIV as (EQUIV & FLOC). rw. s.
    split. inversion EQUIV'; clarify.
    assert (subst_intro_vl _ _ _ (map_vl φ v)) by apply subst_intro.
    gensym_tac (L0 ++ floc_vl (map_vl φ v)) ν.
    rw; eauto. eapply equiv_f_ext.
    instantiate (1 := ((ν !-> ℓ' ; bot) !! ν)).
    eapply (reduce_f_bloc _ _ _ (open_loc_vl 0 ν (map_vl φ v))); eauto.
    unfold update. rewrite eqb_refl. auto.
    eapply equiv_f_ext; eauto.
    all:try solve [ii; ss; unfold update, remove; des_ifs; eqb2eq loc; clarify].
    ii. apply FLOC.
    assert (In ℓ0 (floc_wvl (wvl_recv (map_vl φ v))) \/ In ℓ0 (floc_wvl (map_vl φ v))).
    eapply open_wvl_floc; eauto.
    des; ss.
    all:exploit (@read_env_floc var loc); eauto.
  - repeat eexists; try econstructor; eauto; apply EQUIV.
  - exploit IHEVAL1; eauto.
    intros (v1' & m1' & L1' & EVAL1' & EQUIV1).
    assert (Equiv (map_nv φ σ) (mvalue_exp σ') m1' L1') as EQUIV'.
    split.
    eapply equiv_m_ext. apply EQUIV.
    eapply m_inc; eauto. ii.
    destruct EQUIV as (A & B).
    eapply equiv_floc_free in A; eauto.
    exploit B; eauto.
    ii. exploit (@m_pres var loc); eauto. rw. eauto.
    ii. exploit (@L_inc var loc). try_all.
    instantiate (1 := ℓ). try_all. all:eauto.
    assert (fin m1') as FIN1 by (eapply fin_pres; eauto).
    exploit IHEVAL2; eauto.
    intros (v2' & m2' & L2' & EVAL2' & EQUIV2).
    destruct EQUIV1 as (EQUIV0 & DOML1).
    inv EQUIV0. ss.
    eapply fin_pres in EVAL2' as dom2; eauto.
    destruct dom2 as (dom2 & DOM2).
    gensym_tac (dom2 ++ L2') ν. clear Heqν.
    exploit (IHEVAL3 φ ((x, ν) :: σ'0) (ν !-> v2' ; m2') L2').
    exists (ν :: dom2).
    ii; ss; split_nIn; unfold update; des_ifs; eqb2eq loc; clarify; eauto.
    eauto. split.
    econstructor. instantiate (1 := v2'). unfold update. rewrite eqb_refl. auto.
    {
      eapply equiv_m_ext. apply EQUIV2.
      - ii. unfold update; des_ifs; eqb2eq loc; clarify. contradict.
      - ii. destruct EQUIV2 as (EQUIV2 & DOML2).
        eapply eval_map in EVAL2; eauto.
        eapply eval_floc_dec in EVAL2; eauto.
        destruct EQUIV as (EQUIV & DOML).
        eapply equiv_floc_free in EQUIV; eauto. rrw. clear EQUIV.
        unfold update; des_ifs; eqb2eq loc; clarify. contradict.
        eapply m_pres in EVAL1' as M1; eauto.
        eapply m_pres in EVAL2' as M2; eauto. rewrite M2. eauto.
        eapply EQUIV'. auto.
    }
    {
      eapply equiv_m_ext. apply EQUIV1.
      - ii. eapply m_inc in EVAL2'; eauto. rewrite <- EVAL2' in *.
        unfold update; des_ifs; eqb2eq loc; clarify. contradict.
      - ii. eapply L_inc in EVAL2' as LINC; eauto.
        eapply eval_map in EVAL1; eauto.
        eapply eval_floc_dec in EVAL1; eauto.
        destruct EQUIV as (EQUIV & DOML).
        eapply equiv_floc_free in EQUIV; eauto. rrw. clear EQUIV.
        unfold update; des_ifs; eqb2eq loc; clarify.
        eapply m_pres in EVAL1' as M1; eauto.
        eapply m_pres in EVAL2' as M2; eauto. rewrite M2. eauto.
    }
    {
      ii; ss. rewrite in_app_iff in *.
      des. try_all. auto.
      eapply L_inc in EVAL2'; eauto.
    }
    intros (v' & m' & L' & EVAL' & EQUIV'').
    exists v'. exists m'. exists L'.
    split. econstructor; eauto. eauto.
  - exploit IHEVAL1; eauto.
    intros (v1' & m1 & L1 & EVAL1' & EQUIV1).
    eapply fin_pres in EVAL1' as FIN1; eauto.
    destruct EQUIV1 as (EQUIV0 & DOML1).
    destruct v1'; try solve [inv EQUIV0].
    exploit (IHEVAL2 φ σ0 m1 L1); eauto. split; auto.
    intros (v2' & m2 & L2 & EVAL2' & EQUIV2).
    exists v2'. exists m2. exists L2.
    split. econstructor; eauto. eauto.
  - exists (mvalue_exp []). exists m. exists L.
    split; econstructor; eauto. econstructor.
    ii; ss.
  - destruct FIN as (dom & FIN).
    exploit (avoid_dom_ran (floc_nv σ) (L ++ dom)); eauto.
    intros (ν & FREEσ & FREEdom). split_nIn.
    assert (~ In (φ ν) (floc_nv (map_nv φ σ))) as FREEφσ.
    { red. intros contra. eapply map_floc in contra; eauto. }
    exploit (IHEVAL1 (swap φ ℓ ν) ((x, φ ν) :: σ') m (φ ν :: L)); eauto.
    eexists; eauto.
    unfold swap. ii.
    repeat (des_hyp; eqb2eq loc; clarify); eauto;
    exploit INJ; eauto; ii; clarify.
    unfold swap at 1. rewrite eqb_refl.
    assert (map_ext_nv _ _ _ σ) by eapply map_ext.
    rw. instantiate (1 := φ).
    destruct EQUIV. split. eapply equiv_floc; eauto.
    ii; ss; des; clarify; eauto.
    ii. unfold swap. des_ifs; eqb2eq loc; clarify.
    intros (v1' & m1 & L1 & EVAL1' & EQUIV1).
    assert (forall ℓ' (FRESH' : ~ In ℓ' (floc_vl (map_vl (swap φ ℓ ν) v1))),
      equiv (open_loc_vl 0 ℓ' (close_vl 0 (φ ℓ) (map_vl φ v1))) (ℓ' !-> φ ν ; bot) v1' (φ ν !-> v1' ; m1)) as HINT.
    {
      ii.
      replace (open_loc_vl 0 ℓ' (close_vl 0 (φ ℓ) (map_vl φ v1))) with
        (subst_loc_vl ℓ' (φ ν) (open_loc_vl 0 (φ ν) (close_vl 0 (φ ℓ) (map_vl φ v1)))).
      all:cycle 1.
      assert (open_loc_subst_loc_vl _ _ _ (close_vl 0 (φ ℓ) (map_vl φ v1))) by apply open_loc_subst_loc.
      rw. rewrite eqb_refl.
      assert (subst_loc_fresh_vl _ _ _ (close_vl 0 (φ ℓ) (map_vl φ v1))) by apply subst_loc_fresh.
      rw; eauto.
      red. intros IN.
      assert (close_floc_vl _ _ _ (map_vl φ v1)) as HINT by apply close_floc.
      apply HINT in IN. destruct IN as (IN & IN').
      eapply eval_map in EVAL1; eauto.
      eapply eval_floc_dec in EVAL1; eauto.
      ss. des; clarify; auto.
      replace (open_loc_vl 0 (φ ν) (close_vl 0 (φ ℓ) (map_vl φ v1))) with
        (subst_loc_vl (φ ν) (φ ℓ) (map_vl φ v1)).
      all:cycle 1.
      assert (close_open_loc_eq_vl _ _ _ (map_vl φ v1)) by apply close_open_loc_eq.
      rw. f_equal; auto.
      assert (value (map_vl φ v1)) as VAL.
      eapply eval_map in EVAL1; eauto.
      eapply eval_lc; eauto. s.
      econstructor; eauto.
      destruct EQUIV. eapply equiv_lc_nv; eauto.
      assert (open_loc_lc_vl _ _ _ (map_vl φ v1) VAL) by (apply open_loc_lc; auto).
      auto.
      replace (subst_loc_vl (φ ν) (φ ℓ) (map_vl φ v1)) with
        (map_vl (swap φ ℓ ν) v1).
      all:cycle 1.
      assert (map_ext_vl _ _ _ v1) as RR by apply map_ext.
      erewrite RR. instantiate (1 := swap φ ν ℓ).
      case_eqb ℓ ν.
      erewrite RR. instantiate (1 := φ).
      assert (subst_id_vl _ _ _ (map_vl φ v1)) by apply subst_id.
      rw. eauto.
      ii. unfold swap; des_ifs; eqb2eq loc; clarify.
      assert (swap_is_subst_vl _ _ _ v1) by apply swap_is_subst.
      rw; eauto.
      red. intros IN. eapply eval_floc_dec in EVAL1; eauto.
      ss. des; clarify.
      ii. unfold swap; des_ifs; eqb2eq loc; clarify.
      eapply equiv_f_ext.
      instantiate (1 := swap (φ ν !-> φ ν ; bot) ℓ' (φ ν)).
      all:cycle 1.
      ii. unfold swap, update; des_ifs; repeat eqb2eq loc; clarify.
      replace (wvl_v (subst_loc_vl ℓ' (φ ν) (map_vl (swap φ ℓ ν) v1))) with
        (subst_loc_wvl ℓ' (φ ν) (map_vl (swap φ ℓ ν) v1)) by reflexivity.
      eapply equiv_loc_subst.
      eapply extend_m_floc; eauto. try_all.
      eapply m_pres with (ℓ := φ ν) in EVAL1'; ss; try rw; auto.
      s. auto. unfold update. rewrite eqb_refl. ii; clarify.
    }
    assert (equiv (wvl_recv (close_vl 0 (φ ℓ) (map_vl φ v1))) bot v1' (φ ν !-> v1'; m1)) as EQUIV'.
    { econstructor; eauto. unfold update. rewrite eqb_refl. auto. }
    assert (fin (φ ν !-> v1' ; m1)) as FIN1.
    {
      eapply fin_pres in EVAL1'; eauto.
      destruct EVAL1' as (dom1 & DOM1).
      exists (φ ν :: dom1).
      ii; split_nIn; unfold update; des_ifs; eqb2eq loc; clarify; auto.
      eexists; eauto.
    }
    exploit (IHEVAL2 φ ((x, φ ν) :: σ') (φ ν !-> v1'; m1) L1); eauto.
    split.
    econstructor; eauto. unfold update. rewrite eqb_refl. eauto.
    assert (map_close_vl _ _ _ v1) by apply map_close.
    rw; eauto.
    eapply equiv_m_ext; try apply EQUIV.
    { ii. eapply m_inc in EVAL1'; eauto. rrw. unfold update; des_ifs; eqb2eq loc; clarify. contradict. }
    { ii; ss. unfold update; des_ifs; eqb2eq loc; clarify. destruct EQUIV as (EQUIV & DOM').
      eapply equiv_floc_free in EQUIV; eauto. rrw. eapply m_pres in EVAL1'; eauto. ss. eauto. }
    { ii; ss. rewrite in_app_iff in IN. des.
      { assert (map_close_vl _ _ _ v1) as RR by apply map_close. rewrite RR in IN; eauto.
        eapply close_floc in IN. des. eapply eval_map in EVAL1; eauto; ss.
        eapply eval_floc_dec in EVAL1; eauto. ss. des; clarify.
        eapply L_inc in EVAL1'; eauto. ss. destruct EQUIV. eauto. }
      { eapply L_inc in EVAL1'; eauto. ss. destruct EQUIV. eauto. } }
    intros (v2' & m2 & L2 & EVAL2' & EQUIV2 & DOML2).
    destruct v2' as [σ2' | σ2']; try solve [inv EQUIV2].
    exists (mvalue_exp ((x, φ ν) :: σ2')). exists m2. exists L2.
    split. econstructor; eauto.
    assert (map_close_vl _ _ _ v1) by apply map_close.
    rw; eauto.
    split. econstructor. instantiate (1 := v1').
    eapply m_inc in EVAL2'; eauto.
    2: instantiate (1 := φ ν).
    unfold update in EVAL2'. rewrite eqb_refl in EVAL2'. auto.
    unfold update. rewrite eqb_refl. ii; clarify.
    eapply equiv_m_ext; eauto.
    ii. eapply m_inc in EVAL2'; eauto.
    { ii; ss. eapply close_floc in FREEw. des. 
      eapply eval_map in EVAL1; eauto.
      eapply eval_floc_dec in EVAL1; eauto.
      ss; des; clarify.
      destruct EQUIV as (EQUIV & DOML).
      eapply equiv_floc_free in EQUIV; eauto.
      eapply DOML in EVAL1.
      eapply m_pres in EVAL1' as P1; try instantiate (1 := ℓ0); ss; auto.
      eapply m_pres in EVAL2' as P2; try instantiate (1 := ℓ0); ss; auto.
      unfold update in P2. des_hyp; eqb2eq loc; clarify.
      repeat rw. auto.
      eapply L_inc in EVAL1'; eauto. ss. auto. }
    auto.
    { ii; ss. rewrite in_app_iff in IN. des.
      { eapply close_floc in IN. des. 
        eapply eval_map in EVAL1; eauto.
        eapply eval_floc_dec in EVAL1; eauto.
        ss; des; clarify.
        destruct EQUIV as (EQUIV & DOML).
        eapply DOML in EVAL1.
        eapply L_inc in EVAL1'; try instantiate (1 := ℓ0); ss; auto.
        eapply L_inc in EVAL2'; eauto. }
      { eauto. } }
Qed.

Lemma equiv_r {var loc} `{Eq var} `{Name loc} (σ' : menv var loc) m L t v' m' L' (EVAL : meval σ' m L t v' m' L') :
  forall σ (EQUIV : Equiv (vl_exp σ) (mvalue_exp σ') m L),
    exists v, (eval σ t v) /\ (Equiv v v' m' L').
Proof.
  induction EVAL.
  - ii. exploit (@equiv_read_menv var loc); try apply EQUIV; eauto.
    intros (v' & READσ' & EQUIV').
    destruct v' as [v' | v']. (* normal id, recid *)
    + exists v'. split. econstructor; eauto.
      split; eauto. ii. eapply read_env_floc in READσ'; eauto.
      eapply EQUIV; eauto.
    + exists (open_wvl_vl 0 (wvl_recv v') v').
      split. apply ev_rec. auto.
      split. inversion EQUIV'.
      gensym_tac (floc_vl v' ++ L0) ν.
      assert (subst_intro_vl _ _ _ v') by apply subst_intro.
      rw; eauto.
      eapply equiv_f_ext.
      instantiate (1 := (ν !-> ℓ' ; bot) !! ν).
      exploit EQUIV0; eauto. ii.
      exploit reduce_f_bloc; eauto.
      unfold update. rewrite eqb_refl. auto.
      eapply equiv_f_ext. instantiate (1 := bot). auto.
      all: try (ii; unfold remove, update; des_ifs; eqb2eq loc; clarify).
      ii; ss. eapply open_wvl_floc in IN. ss.
      des; eapply EQUIV; eapply read_env_floc in READσ'; eauto.
  - ii. exists (vl_clos (v_fn x t) σ0).
    split. econstructor; eauto.
    split. econstructor. apply EQUIV.
    ii; ss; apply EQUIV; auto.
  - ii. exploit IHEVAL1; eauto.
    intros (v1' & EVAL1' & EQUIV1).
    exploit (IHEVAL2 σ0); eauto.
    split.
    eapply equiv_m_ext. instantiate (1 := m). apply EQUIV.
    ii. eapply m_inc in EVAL1; eauto.
    ii. destruct EQUIV as (EQUIV & DOML').
    eapply equiv_floc_free in EQUIV; eauto.
    eapply m_pres in EVAL1; eauto. repeat rw; eauto.
    ii. eapply L_inc in EVAL1; eauto. apply EQUIV; auto.
    intros (v2' & EVAL2' & EQUIV2).
    destruct EQUIV1 as (EQUIV0 & DOML1).
    destruct v1' as [ |e σ']; inv EQUIV0.
    exploit (IHEVAL3 (nv_bval x v2' σ')).
    destruct EQUIV2 as (EQUIV2 & DOML2).
    split. econstructor.
    unfold update. rewrite eqb_refl. eauto.
    eapply equiv_m_ext; eauto.
    ii. unfold update. des_ifs; eqb2eq loc; clarify.
    ii. eapply equiv_floc_free in EQUIV2; eauto.
    unfold update. des_ifs; eqb2eq loc; clarify. contradict.
    eapply equiv_m_ext; eauto.
    ii. eapply m_inc in EVAL2; eauto.
    unfold update. des_ifs; eqb2eq loc; clarify.
    rewrite EVAL2 in *. contradict.
    ii. eapply equiv_floc_free in EQUIV1; eauto. rrw.
    eapply m_pres in EVAL2 as P; eauto. rrw.
    unfold update. des_ifs; eqb2eq loc; clarify.
    exploit DOML1; eauto. intros IN.
    eapply L_inc in EVAL2; eauto. clarify.
    ii; ss. rewrite in_app_iff in IN.
    des. eauto. exploit DOML1; eauto. ii.
    eapply L_inc in EVAL2; eauto.
    intros (v' & EVAL' & EQUIV').
    exists v'. split. econstructor; eauto. auto.
  - ii. exploit IHEVAL1; eauto.
    intros (v1' & EVAL1' & EQUIV1 & DOML1).
    destruct v1' as [σ1' | ]; try solve [inv EQUIV1].
    exploit IHEVAL2; eauto.
    instantiate (1 := σ1'). split; eauto.
    intros (v2' & EVAL2' & EQUIV2).
    exists v2'. split. econstructor; eauto. eauto.
  - ii. exists nv_mt.
    split; repeat econstructor; eauto.
    ii; ss.
  - intros σ'. intros (EQUIV & DOML).
    exploit (IHEVAL1 (nv_floc x ℓ σ')).
    split. apply equiv_floc; eauto.
    ii; ss; des; eauto.
    intros (v1' & EVAL1' & EQUIV1 & DOML1).
    assert (equiv (wvl_recv (close_vl 0 ℓ v1')) bot v1 (ℓ !-> v1; m1)) as HINT.
    {
      econstructor. unfold update. rewrite eqb_refl. eauto.
      instantiate (1 := L1).
      ii. assert (close_open_loc_eq_vl _ _ _ v1') by apply close_open_loc_eq.
      rw. apply eval_lc in EVAL1'; eauto.
      assert (open_loc_lc_vl _ _ _ v1' EVAL1') by (apply open_loc_lc; auto).
      rw. eapply equiv_f_ext.
      instantiate (1 := swap (ℓ !-> ℓ ; bot) ℓ0 ℓ).
      replace (wvl_v (subst_loc_vl ℓ0 ℓ v1')) with (subst_loc_wvl ℓ0 ℓ v1') by reflexivity.
      apply equiv_loc_subst.
      apply extend_m_floc; eauto.
      eapply m_pres in EVAL1; ss; eauto. rw. auto.
      ii. exploit DOML1; eauto.
      unfold update. rewrite eqb_refl. ii; ss.
      ii. unfold swap, update.
      des_ifs; clarify; repeat eqb2eq loc; clarify.
      econstructor. eapply equiv_lc_wvl in EQUIV. inv EQUIV. inv VAL. auto.
    }
    exploit (IHEVAL2 (nv_bval x (wvl_recv (close_vl 0 ℓ v1')) σ')).
    split. econstructor; eauto.
    unfold update. rewrite eqb_refl. eauto.
    eapply equiv_m_ext; eauto.
    ii. unfold update. des_ifs; eqb2eq loc; clarify.
    eapply m_inc in EVAL1; eauto.
    ii; ss. unfold update. des_ifs; eqb2eq loc; clarify.
    contradict.
    eapply m_pres in EVAL1; ss; eauto. rw.
    eapply equiv_floc_free in EQUIV; eauto.
    ii; ss. rewrite in_app_iff in IN.
    des. apply close_floc in IN. des. auto.
    exploit DOML; eauto. ii. eapply L_inc in EVAL1; eauto; ss; eauto.
    intros (v2' & EVAL2' & EQUIV2 & DOML2).
    destruct v2' as [σ2' | ]; try solve [inv EQUIV2].
    exists (nv_bval x (wvl_recv (close_vl 0 ℓ v1')) σ2').
    split. econstructor; eauto.
    split.
    econstructor; eauto. instantiate (1 := v1).
    eapply m_inc in EVAL2; eauto.
    2: instantiate (1 := ℓ).
    unfold update in EVAL2. rewrite eqb_refl in EVAL2; eauto.
    unfold update. rewrite eqb_refl. ss.
    eapply equiv_m_ext; eauto.
    ii. eapply m_inc in EVAL2; eauto.
    ii; ss. eapply close_floc in FREEw. des.
    eapply m_pres in EVAL2; eauto.
    unfold update in EVAL2. des_hyp; eqb2eq loc; clarify.
    rw. eapply equiv_floc_free in EQUIV1; eauto.
    ii; ss. rewrite in_app_iff in IN.
    des. apply close_floc in IN. des.
    exploit DOML1; eauto. ii.
    eapply L_inc in EVAL2; eauto.
    eauto.
Qed.

Theorem equiv_semantics {var loc} `{Eq var} `{Name loc}
  (σ : nv var loc val) 
  (σ' : menv var loc) m (FIN : fin m) L t
  (EQUIV : Equiv σ (mvalue_exp σ') m L) :
  (forall v (EVAL : eval σ t v),
    exists v' m' L', meval σ' m L t v' m' L' /\ Equiv v v' m' L') /\
  (forall v' m' L' (EVAL : meval σ' m L t v' m' L'),
    exists v, eval σ t v /\ Equiv (wvl_v v) v' m' L').
Proof.
  split.
  - ii. exploit (@equiv_l var loc); eauto.
    instantiate (1 := id). ii; ss.
    instantiate (1 := L). instantiate (1 := σ').
    assert (map_id_is_id_nv _ _ _ σ) by apply map_id_is_id.
    rw. eauto.
    ii; des.
    assert (map_id_is_id_vl _ _ _ v) as RR by apply map_id_is_id.
    rewrite RR in *. eauto.
  - ii. exploit (@equiv_r var loc); eauto.
Qed.
