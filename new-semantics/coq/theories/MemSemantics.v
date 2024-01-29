From Basics Require Import Basics.
From LN Require Import Defs.
From LN Require Import Syntax.
From LN Require Import SubstFacts.
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

Lemma equiv_l {var loc} `{Eq var} `{Name loc} (σ : nv var loc val) t v (EVAL : eval σ t v) :
  forall φ σ' m L
    (INJ : forall x y (fEQ : φ x = φ y), x = y)
    (EQUIV : Equiv (map_nv φ σ) (mvalue_exp σ') m L) (FIN : fin m),
    exists v' m' L',
      (meval σ' m L t v' m' (L' ++ L)) /\
      (Equiv (map_vl φ v) v' m' (L' ++ L)) /\
      (fin m') /\
      (forall ℓ (INℓ : In ℓ L), m' ℓ = m ℓ) /\
      (forall ℓ (DOM : m ℓ <> None), m' ℓ = m ℓ).
Proof.
  induction EVAL; ii; ss.
Admitted.

 
