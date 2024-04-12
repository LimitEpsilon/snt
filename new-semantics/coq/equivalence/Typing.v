From Basics Require Import Basics.
From Without_events Require Import Defs.
From Without_events Require Import Syntax.
From Without_events Require Import SubstFacts.
From Without_events Require Import EnvSemantics.
From Equations Require Import Equations.

Inductive tyenv {var} :=
  | Nil
  | TBind (x : var) (A : ty) (Γ : tyenv)

with ty {var} :=
  | Env (Γ : tyenv)
  | Fun (A : ty) (S : list var) (B : ty)
.

Scheme tyenv_ind_mut := Induction for tyenv Sort Prop
with ty_ind_mut := Induction for ty Sort Prop.

Combined Scheme type_ind from tyenv_ind_mut, ty_ind_mut.

Arguments tyenv : clear implicits.
Arguments ty : clear implicits.

Fixpoint tyenv_size {var} (Γ : tyenv var) :=
  match Γ with
  | Nil => 1
  | TBind _ A Γ' => 1 + ty_size A + tyenv_size Γ'
  end

with ty_size {var} (A : ty var) :=
  match A with
  | Env Γ => 1 + tyenv_size Γ
  | Fun A _ B => 1 + ty_size A + ty_size B
  end.

Lemma size_positive {var} :
  (forall (Γ : tyenv var), tyenv_size Γ > 0) /\
  (forall (A : ty var), ty_size A > 0).
Proof.
  apply type_ind; intros; simpl in *; nia.
Qed.

Lemma tyenv_size_positive {var} (Γ : tyenv var) : tyenv_size Γ > 0.
Proof. apply size_positive. Qed.

Lemma ty_size_positive {var} (A : ty var) : ty_size A > 0.
Proof. apply size_positive. Qed.

Variant case : Set :=
  env_case | val_case | wal_case | expr_case.

Definition ty_case var c :=
  match c with env_case => tyenv var | _ => ty var end.

Definition vl_case var loc c : Type :=
  match c with 
  | env_case => nv var loc (@val var)
  | val_case => vl var loc (@val var)
  | wal_case => wvl var loc (@val var)
  | expr_case => @tm var * nv var loc (@val var) * list var 
  end.

Definition mut_measure {var} (c : case) (A : ty_case var c) : nat :=
  let (f, x) := match c as c' 
    return (ty_case var c' -> nat) * ty_case var c with
  | env_case => (tyenv_size, A)
  | val_case => (ty_size, A)
  | wal_case => (ty_size, A)
  | expr_case => (ty_size, A)
  end in
  match c with
  | env_case => f x
  | val_case => f x
  | wal_case => 1 + f x
  | expr_case => 1 + f x
  end.

Ltac step :=
  match goal with
  | _ => nia
  | _ => progress unfold mut_measure
  | _ => progress ss
  | _ => intro
  | _ => des_goal
  | _ => des_hyp
  | H : Some _ = None |- _ => inversion H
  | H : None = Some _ |- _ => inversion H
  | H : Some ?A = Some ?B |- _ =>
    inversion H; subst; clear H
  | |- ?L < ?R =>
    match R with
    | context [ty_size ?A] =>
      lazymatch L with
      | context [ty_size A] => fail
      | _ => 
        lazymatch goal with
        | _ : ty_size A > 0 |- _ => fail
        | _ => specialize (ty_size_positive A)
        end
      end
    | context [tyenv_size ?Γ] =>
      lazymatch L with
      | context [tyenv_size Γ] => fail
      | _ =>
        lazymatch goal with
        | _ : tyenv_size Γ > 0 |- _ => fail
        | _ => specialize (tyenv_size_positive Γ)
        end
      end
    end
  end.

Ltac t := repeat step.

Equations type_interp {var loc} `{Eq var} `{Eq loc}
  (c : case) (t : ty_case var c) (v : vl_case var loc c) : Prop by wf (mut_measure c t) := {
  type_interp env_case Nil nv_mt := True;
  type_interp env_case (TBind x A Γ) (nv_bval x' w σ) :=
    x = x' /\
    type_interp wal_case A w /\
    type_interp env_case Γ σ;
  type_interp env_case (TBind x A Γ) (nv_floc x' ℓ σ) :=
    x = x' /\
    forall w,
      type_interp wal_case A w ->
      type_interp env_case Γ (subst_wvl_nv w ℓ σ);
  type_interp env_case _ _ := False;
  type_interp val_case (Env Γ) (vl_exp σ) :=
    type_interp env_case Γ σ;
  type_interp val_case (Fun A L B) (vl_clos (v_fn x e) σ) :=
    forall w,
      type_interp wal_case A w ->
      type_interp expr_case B (e, nv_bval x w σ, L);
  type_interp val_case _ _ := False;
  type_interp wal_case A (wvl_v v) :=
    type_interp val_case A v;
  type_interp wal_case A (wvl_recv v) :=
    forall v',
      type_interp val_case A v' ->
      type_interp val_case A (open_wvl_vl 0 (wvl_v v') v);
  type_interp expr_case A (e, σ, L) :=
    forall v,
      eval σ e v ->
      type_interp val_case A v
}.

Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.
Next Obligation. t. Qed.

(*
Inductive typing (Γ : tyenv) : tm -> ty -> Prop :=
  | TVar x A (READ : read Γ x = Some A)
  : typing Γ (Var x) A

  | TLam x e A B
  (FN : typing (TBind x A Γ) e B)
  : typing Γ (Lam x e) (Fun A B)

  | TApp e1 e2 A B C
  (FN : typing Γ e1 (Fun A C))
  (ARG : typing Γ e2 B)
  (SUB : subtype A B)
  : typing Γ (App e1 e2) C

  | TLink e1 e2 Γ' A
  (MOD : typing Γ e1 (Env Γ'))
  (EXPR : typing Γ' e2 A)
  : typing Γ (Link e1 e2) A

  | TEmpty
  : typing Γ Empty (Env Nil)

  | TVal x e1 e2 A Γ'
  (VAL : typing Γ e1 A)
  (MOD : typing (TBind x A Γ) e2 (Env Γ'))
  : typing Γ (Val x e1 e2) (Env (TBind x A Γ'))
.

#[local] Hint Constructors typing : core.


Lemma simp_interp_env Γ v :
  type_interp val_case (Env Γ) v =
  match v with
  | Ctx σ => type_interp val_case (Env Γ) v
  | _ => False
  end. 
Proof. destruct Γ; ii; simp type_interp; repeat des_goal; eauto. Qed.

Lemma remove_read Γ x x' :
  read (remove Γ x) x' =
    match String.eqb x' x with
    | true => None
    | false => read Γ x'
    end.
Proof.
  ginduction Γ; ii; ss; repeat des_goal;
  repeat rewrite eqb_eq in *; 
  repeat rewrite eqb_neq in *;
  clarify;
  solve [rw; rewrite eqb_refl; ss
    | rewrite <- eqb_neq in *; repeat rw; ss].
Qed.

Lemma remove_comm Γ x x' :
  remove (remove Γ x) x' = remove (remove Γ x') x.
Proof.
  induction Γ; ss; repeat des_goal; ss; rw; eauto.
Qed.

Lemma env_extend_aux Γ σ σ'
  (READ : forall x (DOM : read Γ x <> None),
    fetch σ' x = fetch σ x)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ))
  n (IND : tyenv_size Γ <= n) :
  type_interp val_case (Env Γ) (Ctx σ').
Proof.
  ginduction n; ii; ss.
  pose proof (tyenv_size_positive Γ); nia.
  destruct Γ; ss.
  simp type_interp in *.
  des_hyp; des; clarify.
  repeat rw. split. eauto.
  apply (IHn (remove Γ x) σ σ'); eauto.
  - ii. rewrite remove_read in DOM. apply READ.
    des_hyp; eauto.
  - pose proof (ty_size_positive A).
    pose proof (remove_size_dec Γ x). nia.
  - rewrite eqb_refl. ii. clarify.
Qed.

Lemma env_extend Γ σ σ'
  (READ : forall x (DOM : read Γ x <> None),
    fetch σ' x = fetch σ x)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ)) :
  type_interp val_case (Env Γ) (Ctx σ').
Proof. eapply env_extend_aux; eauto. Qed.

Lemma sep_env_aux Γ σ x n (IND : tyenv_size Γ <= n) :
  match read Γ x, fetch σ x with
  | Some _, None => False
  | Some A, Some v => type_interp val_case A v
  | _, _ => True
  end /\ type_interp val_case (Env (remove Γ x)) (Ctx σ) ->
  type_interp val_case (Env Γ) (Ctx σ).
Proof.
  ginduction n; ii;
  destruct Γ; ss; repeat des_hyp; des; 
  pose proof (tyenv_size_positive Γ); try nia;
  clarify.
  - rewrite eqb_eq in *; clarify.
    simp type_interp in *. rw. eauto.
  - simp type_interp in *.
    des_goal; des; clarify.
    split; eauto.
    apply (IHn _ _ x).
    pose proof (ty_size_positive A).
    pose proof (remove_size_dec Γ x0). nia.
    rewrite remove_read. rewrite remove_comm.
    repeat rw. eauto.
  - simp type_interp in *.
    des_goal; des; clarify.
    split; eauto.
    apply (IHn _ _ x).
    pose proof (ty_size_positive A).
    pose proof (remove_size_dec Γ x0). nia.
    rewrite remove_read. rewrite remove_comm.
    repeat rw. eauto.
Qed.

Lemma sep_env Γ σ x :
  match read Γ x, fetch σ x with
  | Some _, None => False
  | Some A, Some v => type_interp val_case A v
  | _, _ => True
  end /\ type_interp val_case (Env (remove Γ x)) (Ctx σ) ->
  type_interp val_case (Env Γ) (Ctx σ).
Proof. eapply sep_env_aux. eauto. Qed.

Lemma env_sep_aux Γ σ x n (IND : tyenv_size Γ <= n) :
  type_interp val_case (Env Γ) (Ctx σ) ->
  type_interp val_case (Env (remove Γ x)) (Ctx σ).
Proof.
  ginduction n; ii; ss. pose proof (tyenv_size_positive Γ). nia.
  destruct Γ; ss. pose proof (ty_size_positive A).
  des_goal.
  - rewrite eqb_eq in *. clarify.
    simp type_interp in H. apply H.
  - simp type_interp in *.
    des_hyp; des; clarify.
    split; eauto.
    rewrite remove_comm. apply IHn; eauto.
    pose proof (remove_size_dec Γ x0). nia.
Qed.

Lemma env_sep Γ σ x :
  type_interp val_case (Env Γ) (Ctx σ) ->
  type_interp val_case (Env (remove Γ x)) (Ctx σ).
Proof. eapply env_sep_aux; eauto. Qed.

Lemma read_subtype Γ Γ'
  (READ : forall x A, read Γ x = Some A ->
    exists A', read Γ' x = Some A' /\ subtype A A') :
  subtype (Env Γ) (Env Γ').
Proof.
  ginduction Γ'.
  - ii; ss. destruct Γ; ss.
    specialize (READ x A).
    rewrite eqb_refl in *.
    exploit READ; eauto.
    ii; des; clarify.
  - ii. rewrite simp_subtype_env. split.
    + apply IHΓ'. ii.
      rewrite remove_read in *. des_hyp.
      exploit READ; eauto.
      ii; des; ss. des_hyp; clarify. eauto.
    + des_goal; eauto.
      exploit READ; eauto.
      ii; des; ss. rewrite eqb_refl in *.
      clarify.
Qed.

Lemma subtype_read Γ Γ'
  (SUB : subtype (Env Γ) (Env Γ')) :
  forall x A, read Γ x = Some A ->
    exists A', read Γ' x = Some A' /\ subtype A A'.
Proof.
  ginduction Γ'; ii; ss.
  - destruct Γ; ss.
  - rewrite simp_subtype_env in SUB.
    des_goal. rewrite eqb_eq in *. clarify.
    exists A. rewrite H in *. des; eauto.
    eapply IHΓ'. des; eauto.
    rewrite remove_read. rw. eauto.
Qed.

Lemma subtype_remove Γ Γ' x (SUB : subtype (Env Γ) (Env Γ')) :
  subtype (Env (remove Γ x)) (Env (remove Γ' x)).
Proof.
  apply read_subtype. ii.
  specialize (subtype_read Γ Γ' SUB x0 A).
  rewrite remove_read in *. des_hyp.
  eauto.
Qed.

Lemma subtype_refl_aux A n (IND : ty_size A <= n) :
  subtype A A.
Proof.
  ginduction n; ii. pose proof (ty_size_positive A). nia.
  destruct A; ss.
  - apply read_subtype. intros x A READ.
    exists A. split; eauto.
    apply IHn.
    specialize (read_size_dec Γ x A READ). nia.
  - simp subtype. split; apply IHn; nia.
Qed.

Theorem subtype_refl A : subtype A A.
Proof. eapply subtype_refl_aux; eauto. Qed.

Lemma subtype_trans_aux A B C
  (SUBa : subtype A B)
  (SUBb : subtype B C) 
  n (IND : ty_size A + ty_size B + ty_size C <= n) :
  subtype A C.
Proof.
  ginduction n; ii. pose proof (ty_size_positive B). nia.
  destruct B; destruct A;
  try solve [destruct Γ; ss].
  - destruct C; try solve [destruct Γ; ss].
    apply read_subtype.
    ii. exploit (subtype_read Γ0); eauto.
    intros (A' & READ & SUB).
    pose proof (subtype_read Γ Γ1 SUBb x A' READ) as (A'' & READ' & SUB').
    exists A''.
    split; eauto.
    apply (IHn A A' A''); eauto.
    specialize (read_size_dec Γ0 x A H).
    specialize (read_size_dec Γ x A' READ).
    specialize (read_size_dec Γ1 x A'' READ').
    ss. nia.
  - destruct C; try solve [destruct Γ; ss].
    rewrite simp_subtype_fun in *.
    ss; des; split; eapply IHn; eauto; nia.
Qed.

Theorem subtype_trans A B C :
  subtype A B -> subtype B C -> subtype A C.
Proof. ii. eapply subtype_trans_aux; eauto. Qed.

(* A ≥ B => V[A] ⊇ V[B] *)
Lemma subtype_subset_aux A B (SUB : subtype A B)
  n (IND : ty_size A + ty_size B <= n) :
  forall v (GOOD : type_interp val_case B v),
    type_interp val_case A v.
Proof.
  ginduction n; ii; ss.
  pose proof (ty_size_positive A). nia.
  destruct B; destruct A; try destruct Γ; ss.
  - destruct Γ0; ss.
  - rewrite simp_subtype_env in SUB.
    simp type_interp in *; repeat des_hyp; des; clarify.
    + apply (sep_env _ _ x). repeat rw.
      split. eapply IHn; eauto.
      exploit (read_size_dec _ x t); eauto.
      specialize (tyenv_size_positive Γ). nia.
      specialize (remove_size_dec Γ x).
      specialize (remove_size Γ0 x). rw.
      specialize (ty_size_positive A). ii.
      eapply (IHn _ (Env (remove Γ x))); eauto.
      pose proof (remove_size (remove Γ0 x) x) as RR.
      rewrite remove_read in *. rewrite eqb_refl in *.
      rewrite <- RR.
      apply subtype_remove. eauto.
      s. nia.
    + apply (sep_env _ _ x). repeat rw.
      split; eauto.
      specialize (remove_size Γ0 x). rw. intros RR.
      rewrite RR in *.
      eapply (IHn _ (Env (remove Γ x))); eauto.
      rewrite <- RR. apply subtype_remove. eauto.
      pose proof (ty_size_positive A).
      pose proof (remove_size_dec Γ x). s. nia.
  - simp subtype in SUB. simp type_interp in *.
    des_hyp; clarify. ii.
    exploit (GOOD v').
    eapply IHn; eauto. apply SUB.
    pose proof (ty_size_positive A2). nia.
    ii. simp type_interp in *. des.
    exists v. split; eauto.
    eapply IHn; eauto.
    pose proof (ty_size_positive A1). nia.
Qed.

Lemma subtype_subset A B (SUB : subtype A B) :
  forall v (GOOD : type_interp val_case B v),
    type_interp val_case A v.
Proof. eapply subtype_subset_aux; eauto. Qed.

Lemma var_compatible_aux Γ x A σ n
  (IND : tyenv_size Γ <= n)
  (READ : read Γ x = Some A)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ)) :
  exists v, type_interp val_case A v /\ fetch σ x = Some v.
Proof.
  ginduction n; intros; destruct Γ; ss.
  - specialize (tyenv_size_positive Γ). nia.
  - simp type_interp in GOOD.
    repeat des_hyp; des; clarify.
    rewrite eqb_eq in *. clarify. exists v. eauto.
    match goal with
    | _ : context [remove ?Γ ?x] |- _ =>
      eapply (IHn (remove Γ x))
    end; eauto.
    t. pose proof (ty_size_positive A0). nia.
    rewrite remove_read. repeat rw. eauto.
Qed.

Lemma var_compatible Γ x A σ
  (READ : read Γ x = Some A)
  (GOOD : type_interp val_case (Env Γ) (Ctx σ)) :
  exists v, type_interp val_case A v /\ fetch σ x = Some v.
Proof. eapply var_compatible_aux; eauto. Qed.

Lemma env_bind_compatible Γ A x v σ
  (Genv : type_interp val_case (Env Γ) (Ctx σ))
  (Gval : type_interp val_case A v) :
  type_interp val_case (Env (TBind x A Γ)) (Ctx (VBind x v σ)).
Proof.
  simp type_interp.
  s. rewrite eqb_refl. split; eauto.
  eapply (env_extend (remove Γ x) σ).
  ii. rewrite remove_read in DOM.
  s. des_hyp; clarify.
  apply env_sep. eauto.
Qed.

Theorem type_safety Γ e A (TYPE : typing Γ e A) :
  forall σ (GOOD : type_interp val_case (Env Γ) (Ctx σ)),
    type_interp expr_case A (e, σ).
Proof.
  induction TYPE; ii; simp type_interp in *.
  - exploit var_compatible; eauto. ii; des.
    eexists; split; eauto.
  - eexists; split; eauto.
    simp type_interp. ii.
    apply IHTYPE.
    apply env_bind_compatible; eauto.
  - exploit IHTYPE1; eauto. intros SEMTY1.
    simp type_interp in SEMTY1.
    destruct SEMTY1 as (v & SEMTY1 & EVAL1).
    simp type_interp in SEMTY1. des_hyp; clarify.
    exploit IHTYPE2; eauto. intros SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v & SEMTY2 & EVAL2).
    eapply subtype_subset in SEMTY2; eauto.
    eapply SEMTY1 in SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v' & SEMTY2 & EVAL3).
    exists v'. eauto.
  - exploit IHTYPE1; eauto. intros SEMTY1.
    simp type_interp in SEMTY1.
    destruct SEMTY1 as (v & SEMTY1 & EVAL1).
    rewrite simp_interp_env in SEMTY1. des_hyp; clarify.
    exploit IHTYPE2; eauto. intros SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v & SEMTY2 & EVAL2).
    exists v. eauto.
  - eexists; split; eauto. simp type_interp. eauto.
  - exploit IHTYPE1; eauto. intros SEMTY1.
    simp type_interp in SEMTY1.
    destruct SEMTY1 as (v & SEMTY1 & EVAL1).
    exploit (IHTYPE2 (VBind x v σ)).
    apply env_bind_compatible; eauto.
    intros SEMTY2.
    simp type_interp in SEMTY2.
    destruct SEMTY2 as (v' & SEMTY2 & EVAL2).
    rewrite simp_interp_env in SEMTY2. des_ifs.
    eexists; split; eauto using env_bind_compatible.
Qed.

Corollary termination e A (TYPE : typing Nil e A) :
  forall σ, exists v, eval (e, σ) v.
Proof.
  ii. exploit (type_safety _ _ _ _ σ); ii; eauto.
  all:simp type_interp in *; des; eauto.
Qed.
*)
