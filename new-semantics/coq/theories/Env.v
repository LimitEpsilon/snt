From Basics Require Import Basics.
Section PreDefs.
  Variable var : Set.
  Variable loc : Type.
  Variable lang : Type.

  (* pre-values *)
  Inductive wvl :=
  | wvl_v (v : vl) (* v *)
  | wvl_recv (v : vl) (* μ.v *)

  with nv :=
  | nv_mt (* • *)
  | nv_bloc (x : var) (n : nat) (σ : nv) (* bound location *)
  | nv_floc (x : var) (ℓ : loc) (σ : nv) (* free location *)
  | nv_bval (x : var) (w : wvl) (σ : nv) (* bound value *)

  with vl :=
  | vl_exp (σ : nv)
  | vl_clos (e : lang) (σ : nv)
  .

  Scheme wvl_ind_mut := Induction for wvl Sort Prop
  with nv_ind_mut := Induction for nv Sort Prop
  with vl_ind_mut := Induction for vl Sort Prop.

  Combined Scheme pre_val_ind from wvl_ind_mut, nv_ind_mut, vl_ind_mut.
End PreDefs.

Arguments pre_val_ind var loc lang Pw Pσ Pv 
  IHwvl_v IHwvl_recv
  IHnv_mt IHnv_bloc IHnv_floc IHnv_bloc
  IHvl_exp IHvl_clos : rename.

Arguments wvl_v {var loc lang}.
Arguments wvl_recv {var loc lang}.
Arguments nv_mt {var loc lang}.
Arguments nv_bloc {var loc lang}.
Arguments nv_floc {var loc lang}.
Arguments nv_bval {var loc lang}.
Arguments vl_exp {var loc lang}.
Arguments vl_clos {var loc lang}.

(* mutual fixpoints must be defined outside of Section to be simpl'd *)
(* https://github.com/coq/coq/issues/3488 *)

(* open the bound location i with ℓ *)
Fixpoint open_loc_wvl {var loc lang} (i : nat) (ℓ : loc) (w : wvl var loc lang) :=
match w with
| wvl_v v => wvl_v (open_loc_vl i ℓ v)
| wvl_recv v => wvl_recv (open_loc_vl (S i) ℓ v)
end

with open_loc_nv {var loc lang} (i : nat) (ℓ : loc) (σ : nv var loc lang) :=
match σ with
| nv_mt => nv_mt
| nv_bloc x n σ' =>
  if i =? n
  then nv_floc x ℓ (open_loc_nv i ℓ σ')
  else nv_bloc x n (open_loc_nv i ℓ σ')
| nv_floc x ℓ' σ' =>
  nv_floc x ℓ' (open_loc_nv i ℓ σ')
| nv_bval x w σ' =>
  nv_bval x (open_loc_wvl i ℓ w) (open_loc_nv i ℓ σ')
end

with open_loc_vl {var loc lang} (i : nat) (ℓ : loc) (v : vl var loc lang) :=
match v with
| vl_exp σ => vl_exp (open_loc_nv i ℓ σ)
| vl_clos e σ => vl_clos e (open_loc_nv i ℓ σ)
end.

(* close the free location ℓ with the binding depth i *)
Fixpoint close_wvl {var loc lang} `{Eq loc} (i : nat) (ℓ : loc) (w : wvl var loc lang) :=
match w with
| wvl_v v => wvl_v (close_vl i ℓ v)
| wvl_recv v => wvl_recv (close_vl (S i) ℓ v)
end

with close_nv {var loc lang} `{Eq loc} (i : nat) (ℓ : loc) (σ : nv var loc lang) :=
match σ with
| nv_mt => nv_mt
| nv_bloc x n σ' =>
  nv_bloc x n (close_nv i ℓ σ')
| nv_floc x ℓ' σ' =>
  if eqb ℓ ℓ'
  then nv_bloc x i (close_nv i ℓ σ')
  else nv_floc x ℓ' (close_nv i ℓ σ')
| nv_bval x w σ' =>
  nv_bval x (close_wvl i ℓ w) (close_nv i ℓ σ')
end

with close_vl {var loc lang} `{Eq loc} (i : nat) (ℓ : loc) (v : vl var loc lang) :=
match v with
| vl_exp σ => vl_exp (close_nv i ℓ σ)
| vl_clos e σ => vl_clos e (close_nv i ℓ σ)
end.

(* open the bound location i with u *)
Fixpoint open_wvl_wvl {var loc lang} (i : nat) (u : wvl var loc lang) (w : wvl var loc lang) :=
match w with
| wvl_v v => wvl_v (open_wvl_vl i u v)
| wvl_recv v => wvl_recv (open_wvl_vl (S i) u v)
end

with open_wvl_nv {var loc lang} (i : nat) (u : wvl var loc lang) (σ : nv var loc lang) :=
match σ with
| nv_mt => nv_mt
| nv_bloc x n σ' =>
  if i =? n
  then nv_bval x u (open_wvl_nv i u σ')
  else nv_bloc x n (open_wvl_nv i u σ')
| nv_floc x ℓ' σ' =>
  nv_floc x ℓ' (open_wvl_nv i u σ')
| nv_bval x w σ' =>
  nv_bval x (open_wvl_wvl i u w) (open_wvl_nv i u σ')
end

with open_wvl_vl {var loc lang} (i : nat) (u : wvl var loc lang) (v : vl var loc lang) :=
match v with
| vl_exp σ => vl_exp (open_wvl_nv i u σ)
| vl_clos e σ => vl_clos e (open_wvl_nv i u σ)
end.

(* substitute the free location ℓ for ℓ' *)
Fixpoint subst_loc_wvl {var loc lang} `{Eq loc} (ν ℓ : loc) (w : wvl var loc lang) :=
match w with
| wvl_v v => wvl_v (subst_loc_vl ν ℓ v)
| wvl_recv v => wvl_recv (subst_loc_vl ν ℓ v)
end

with subst_loc_nv {var loc lang} `{Eq loc} (ν ℓ : loc) (σ : nv var loc lang) :=
match σ with
| nv_mt => nv_mt
| nv_bloc x n σ' =>
  nv_bloc x n (subst_loc_nv ν ℓ σ')
| nv_floc x ℓ' σ' =>
  if eqb ℓ ℓ'
  then nv_floc x ν (subst_loc_nv ν ℓ σ')
  else nv_floc x ℓ' (subst_loc_nv ν ℓ σ')
| nv_bval x w σ' =>
  nv_bval x (subst_loc_wvl ν ℓ w) (subst_loc_nv ν ℓ σ')
end

with subst_loc_vl {var loc lang} `{Eq loc} (ν ℓ : loc) (v : vl var loc lang) :=
match v with
| vl_exp σ => vl_exp (subst_loc_nv ν ℓ σ)
| vl_clos e σ => vl_clos e (subst_loc_nv ν ℓ σ)
end.

(* substitute the free location ℓ for u *)
Fixpoint subst_wvl_wvl {var loc lang} `{Eq loc} (u : wvl var loc lang) (ℓ : loc) (w : wvl var loc lang) :=
match w with
| wvl_v v => wvl_v (subst_wvl_vl u ℓ v)
| wvl_recv v => wvl_recv (subst_wvl_vl u ℓ v)
end

with subst_wvl_nv {var loc lang} `{Eq loc} (u : wvl var loc lang) (ℓ : loc) (σ : nv var loc lang) :=
match σ with
| nv_mt => nv_mt
| nv_bloc x n σ' =>
  nv_bloc x n (subst_wvl_nv u ℓ σ')
| nv_floc x ℓ' σ' =>
  if eqb ℓ ℓ'
  then nv_bval x u (subst_wvl_nv u ℓ σ')
  else nv_floc x ℓ' (subst_wvl_nv u ℓ σ')
| nv_bval x w σ' =>
  nv_bval x (subst_wvl_wvl u ℓ w) (subst_wvl_nv u ℓ σ')
end

with subst_wvl_vl {var loc lang} `{Eq loc} (u : wvl var loc lang) (ℓ : loc) (v : vl var loc lang) :=
match v with
| vl_exp σ => vl_exp (subst_wvl_nv u ℓ σ)
| vl_clos e σ => vl_clos e (subst_wvl_nv u ℓ σ)
end.

(* free locations *)
Fixpoint floc_wvl {var loc lang} (w : wvl var loc lang) :=
match w with
| wvl_v v | wvl_recv v => floc_vl v
end

with floc_nv {var loc lang} (σ : nv var loc lang) :=
match σ with
| nv_mt => []
| nv_bloc _ _ σ' => floc_nv σ'
| nv_floc _ ℓ σ' => ℓ :: floc_nv σ'
| nv_bval _ w σ' => floc_wvl w ++ floc_nv σ'
end

with floc_vl {var loc lang} (v : vl var loc lang) :=
match v with
| vl_exp σ | vl_clos _ σ => floc_nv σ
end.

Section LCDefs.
  Variable var : Set.
  Variable loc : Type.
  Variable lang : Type.
  (* locally closed predicates *)
  Inductive wvalue : wvl var loc lang -> Prop :=
  | wvalue_v v (VAL : value v) : wvalue (wvl_v v)
  | wvalue_recv L v
    (VAL : forall ℓ, ~ In ℓ L -> value (open_loc_vl 0 ℓ v))
  : wvalue (wvl_recv v)

  with env : nv var loc lang -> Prop :=
  | env_mt : env nv_mt
  | env_floc x ℓ σ (ENV : env σ) : env (nv_floc x ℓ σ)
  | env_bval x w σ (WVALUE : wvalue w) (ENV : env σ) : env (nv_bval x w σ)

  with value : vl var loc lang -> Prop :=
  | value_exp σ (ENV : env σ) : value (vl_exp σ)
  | value_clos e σ (ENV : env σ) : value (vl_clos e σ)
  .

  Scheme wvalue_ind_mut := Induction for wvalue Sort Prop
  with env_ind_mut := Induction for env Sort Prop
  with value_ind_mut := Induction for value Sort Prop.

  Combined Scheme val_ind from wvalue_ind_mut, env_ind_mut, value_ind_mut.
End LCDefs.

Arguments val_ind var loc lang Pw Pσ Pv 
  IHwvalue_v IHwvalue_recv
  IHenv_mt IHenv_floc IHenv_bloc
  IHvalue_exp IHvalue_clos : rename.

Arguments wvalue {var loc lang}.
Arguments wvalue_v {var loc lang}.
Arguments wvalue_recv {var loc lang}.
Arguments env {var loc lang}.
Arguments env_mt {var loc lang}.
Arguments env_floc {var loc lang}.
Arguments env_bval {var loc lang}.
Arguments value {var loc lang}.
Arguments value_exp {var loc lang}.
Arguments value_clos {var loc lang}.

Definition update {loc T} `{Eq loc} (f : loc -> option T) ℓ ℓ' ℓ_param :=
  if eqb ℓ ℓ_param then Some ℓ' else f ℓ_param.

Notation "ℓ '!->' ℓℓ ';' f" := (update f ℓ ℓℓ)
  (at level 100, ℓℓ at next level, right associativity).

Lemma update_ext {loc T} `{Eq loc} L (f f' : loc -> option T) ℓ ℓ' :
  (forall x, In x L -> f x = f' x) ->
  (forall x, x = ℓ \/ In x L -> (ℓ !-> ℓ' ; f) x = (ℓ !-> ℓ' ; f') x).
Proof. ii; unfold update; des_goal; repeat rw; eauto. eqb2eq loc; des; clarify. Qed.

Lemma update_switch {loc T} `{Eq loc} (f : loc -> option T) ℓ ℓ' ν ν' x :
  ℓ <> ν ->
  (ℓ !-> ℓ' ; ν !-> ν' ; f) x = (ν !-> ν' ; ℓ !-> ℓ' ; f) x.
Proof.
  ii. unfold update.
  des_ifs; eqb2eq loc; clarify.
Qed.

Definition remove {loc T} `{Eq loc} (m : loc -> option T) ℓ ℓ_param :=
  if eqb ℓ ℓ_param then None else m ℓ_param.

Notation "m '!!' ℓ" := (remove m ℓ)
  (at level 100, ℓ at next level, right associativity).

Lemma remove_switch {loc T} `{Eq loc} (m : loc -> option T) ℓ ℓ' x :
  ((m !! ℓ) !! ℓ') x = ((m !! ℓ') !! ℓ) x.
Proof.
  ii. unfold remove. des_ifs.
Qed.

Section EquivDefs.
  Variable var : Set.
  Variable loc : Type.
  Variable lang : Type.

  #[local] Coercion vl_exp : nv >-> vl.
  #[local] Coercion wvl_v : vl >-> wvl.

  Definition menv := list (var * loc).
  Variant mvalue :=
  | mvalue_exp (σ : menv)
  | mvalue_clos (e : lang) (σ : menv)
  .
  #[local] Coercion mvalue_exp : menv >-> mvalue.

  Definition memory := loc -> option mvalue.

  (* local coercions were for this definition *)
  (* definition of equivalence *)
  Inductive equiv `{Eq loc} : wvl var loc lang -> (loc -> option loc) -> mvalue -> memory -> Prop :=
  | equiv_mt f m
  : equiv nv_mt f ([] : menv) m
  | equiv_bloc x ℓ (σ : nv var loc lang) f (σ' : menv) ℓ' m
    (SPECf : f ℓ = Some ℓ')
    (BOUND : m ℓ' <> None)
    (EQUIV : equiv σ f σ' m)
  : equiv (nv_floc x ℓ σ) f ((x, ℓ') :: σ' : menv) m
  | equiv_floc x ℓ (σ : nv var loc lang) f (σ' : menv) m
    (SPECf : f ℓ = None)
    (FREE : m ℓ = None)
    (EQUIV : equiv σ f σ' m)
  : equiv (nv_floc x ℓ σ) f ((x, ℓ) :: σ' : menv) m
  | equiv_bval x w (σ : nv var loc lang) f ℓ' v' (σ' : menv) m
    (BOUND : m ℓ' = Some v')
    (EQUIVw : equiv w f v' m)
    (EQUIVσ : equiv σ f σ' m)
  : equiv (nv_bval x w σ) f ((x, ℓ') :: σ' : menv) m
  | equiv_recv (L : list loc) v f v' ℓ' m
    (BOUND : m ℓ' = Some v')
    (EQUIV : forall ℓ (FREE : ~ In ℓ L),
      equiv (wvl_v (open_loc_vl 0 ℓ v)) (ℓ !-> ℓ' ; f) v' m)
  : equiv (wvl_recv v) f v' m
  | equiv_clos e (σ : nv var loc lang) f (σ' : menv) m
    (EQUIV : equiv σ f σ' m)
  : equiv (vl_clos e σ) f (mvalue_clos e σ') m
  .
End EquivDefs.

Arguments equiv {var loc lang _}.
Arguments equiv_mt {var loc lang}.
Arguments equiv_bloc {var loc lang}.
Arguments equiv_floc {var loc lang}.
Arguments equiv_bval {var loc lang}.
Arguments equiv_recv {var loc lang}.
Arguments equiv_clos {var loc lang}.

Section SubstFacts.
  Variable var : Set.
  Variable loc : Type.
  Variable lang : Type.

  Definition open_floc_wvl (w : wvl var loc lang) :=
    forall i ℓ x, In x (floc_wvl (open_loc_wvl i ℓ w)) -> x = ℓ \/ In x (floc_wvl w).

  Definition open_floc_nv (σ : nv var loc lang) :=
    forall i ℓ x, In x (floc_nv (open_loc_nv i ℓ σ)) -> x = ℓ \/ In x (floc_nv σ).

  Definition open_floc_vl (v : vl var loc lang) :=
    forall i ℓ x, In x (floc_vl (open_loc_vl i ℓ v)) -> x = ℓ \/ In x (floc_vl v).

  Lemma open_floc :
    (forall w, open_floc_wvl w) /\
    (forall σ, open_floc_nv σ) /\
    (forall v, open_floc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all:try solve [exploit H; eauto].
    all: repeat des_hyp;
      repeat first [eqb2eq loc | eqb2eq nat];
      clarify; des; eauto.
    exploit H; eauto; ii; des; auto.
    rewrite in_app_iff in *; des.
    exploit H; eauto; ii; des; auto.
    exploit H0; eauto; ii; des; auto.
  Qed.

  Definition open_inc_floc_wvl (w : wvl var loc lang) :=
    forall i ℓ x, In x (floc_wvl w) -> In x (floc_wvl (open_loc_wvl i ℓ w)).

  Definition open_inc_floc_nv (σ : nv var loc lang) :=
    forall i ℓ x, In x (floc_nv σ) -> In x (floc_nv (open_loc_nv i ℓ σ)).

  Definition open_inc_floc_vl (v : vl var loc lang) :=
    forall i ℓ x, In x (floc_vl v) -> In x (floc_vl (open_loc_vl i ℓ v)).

  Lemma open_inc_floc :
    (forall w, open_inc_floc_wvl w) /\
    (forall σ, open_inc_floc_nv σ) /\
    (forall v, open_inc_floc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all:try solve [auto].
    all: repeat des_goal;
      repeat first [eqb2eq loc | eqb2eq nat];
      clarify; des; eauto.
    rewrite in_app_iff in *; des; eauto.
  Qed.

  Definition subst_intro_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_wvl w)),
      open_wvl_wvl i u w =
      subst_wvl_wvl u ℓ (open_loc_wvl i ℓ w)
  .

  Definition subst_intro_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_nv σ)),
      open_wvl_nv i u σ =
      subst_wvl_nv u ℓ (open_loc_nv i ℓ σ)
  .

  Definition subst_intro_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ u (FRESH : ~ In ℓ (floc_vl v)),
      open_wvl_vl i u v =
      subst_wvl_vl u ℓ (open_loc_vl i ℓ v)
  .

  Lemma subst_intro `{Eq loc} :
    (forall w, subst_intro_wvl w) /\
    (forall σ, subst_intro_nv σ) /\
    (forall v, subst_intro_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all:try (cbn; f_equal; solve [auto]).
    - des_goal.
      + eqb2eq nat. subst.
        rewrite eqb_refl. f_equal. auto.
      + f_equal. auto.
    - des_goal.
      + eqb2eq loc. contradict.
      + f_equal. auto.
    - f_equal.
      all: try_all;
        ii; apply FRESH; ss; rewrite in_app_iff; auto.
  Qed.

  Definition open_loc_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ, close_wvl i ℓ (open_loc_wvl i ℓ w) = close_wvl i ℓ w.

  Definition open_loc_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ, close_nv i ℓ (open_loc_nv i ℓ σ) = close_nv i ℓ σ.

  Definition open_loc_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ, close_vl i ℓ (open_loc_vl i ℓ v) = close_vl i ℓ v.

  Lemma open_loc_close `{Eq loc} :
    (forall w, open_loc_close_wvl w) /\
    (forall σ, open_loc_close_nv σ) /\
    (forall v, open_loc_close_vl v).
  Proof.
    apply pre_val_ind; ii; ss; repeat des_goal; repeat rw; eauto.
    all:rewrite eqb_refl in *; eqb2eq nat; clarify.
  Qed.

  Definition close_fresh_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_wvl w)),
      close_wvl i ℓ w = w.

  Definition close_fresh_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_nv σ)),
      close_nv i ℓ σ = σ.

  Definition close_fresh_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ (FRESH : ~ In ℓ (floc_vl v)),
      close_vl i ℓ v = v.

  Lemma close_fresh `{Eq loc} :
    (forall w, close_fresh_wvl w) /\
    (forall σ, close_fresh_nv σ) /\
    (forall v, close_fresh_vl v).
  Proof.
    apply pre_val_ind; ii; ss;
    try match goal with
    | H : ~ In ?ℓ (?l ++ ?l') |- _ =>
      rewrite in_app_iff in H;
      assert (~ In ℓ l /\ ~ In ℓ l') as (FRESH' & FRESH'') by tauto
    | _ : ~ (?A \/ ?B) |- _ =>
      assert (~ A /\ ~ B) as (FRESH' & FRESH'') by tauto;
      rewrite eqb_comm; eq2eqb loc; des_goal; clarify
    end.
    all: repeat match goal with
    | RR : close_fresh_wvl _ |- _ => erewrite RR; eauto
    | RR : close_fresh_nv _ |- _ => erewrite RR; eauto
    | RR : close_fresh_vl _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition close_open_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_wvl i u (close_wvl j ℓ w) = close_wvl j ℓ (open_wvl_wvl i u w).

  Definition close_open_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_nv i u (close_nv j ℓ σ) = close_nv j ℓ (open_wvl_nv i u σ).

  Definition close_open_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i j ℓ u
      (NEQ : i <> j)
      (FRESH : ~ In ℓ (floc_wvl u)),
    open_wvl_vl i u (close_vl j ℓ v) = close_vl j ℓ (open_wvl_vl i u v).

  Lemma close_open_wvl `{Eq loc} :
    (forall w, close_open_wvl_wvl w) /\
    (forall σ, close_open_wvl_nv σ) /\
    (forall v, close_open_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: try match goal with
    | _ : ~ In ?ℓ (floc_wvl ?u) |- context [close_wvl _ ?ℓ ?u] =>
      assert (close_fresh_wvl u) as RR by apply close_fresh;
      rewrite RR; eauto
    end.
    all: repeat match goal with
    | RR : close_open_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : close_open_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : close_open_wvl_vl _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition close_open_loc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_wvl i ν (close_wvl j ℓ w) = close_wvl j ℓ (open_loc_wvl i ν w).

  Definition close_open_loc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_nv i ν (close_nv j ℓ σ) = close_nv j ℓ (open_loc_nv i ν σ).

  Definition close_open_loc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i j ℓ ν
      (NEQ : i <> j)
      (FRESH : ℓ <> ν),
    open_loc_vl i ν (close_vl j ℓ v) = close_vl j ℓ (open_loc_vl i ν v).

  Lemma close_open_loc `{Eq loc} :
    (forall w, close_open_loc_wvl w) /\
    (forall σ, close_open_loc_nv σ) /\
    (forall v, close_open_loc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : close_open_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_nv _ |- _ => erewrite RR; eauto
    | RR : close_open_loc_vl _ |- _ => erewrite RR; eauto
    end.
  Qed.

  Definition open_wvl_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall i u, open_wvl_wvl i u w = w.

  Definition open_wvl_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall i u, open_wvl_nv i u σ = σ.

  Definition open_wvl_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall i u, open_wvl_vl i u v = v.

  Lemma open_wvl_lc `{Name loc} :
    (forall w W, open_wvl_lc_wvl w W) /\
    (forall σ Σ, open_wvl_lc_nv σ Σ) /\
    (forall v V, open_wvl_lc_vl v V).
  Proof.
    apply val_ind; ii; ss; repeat rw; eauto.
    remember (gensym (L ++ (floc_wvl u) ++ (floc_vl v))) as ℓ.
    replace v with (close_vl 0 ℓ (open_loc_vl 0 ℓ v)) at 1.
    assert (close_open_wvl_vl (open_loc_vl 0 ℓ v)) as RR by apply close_open_wvl.
    erewrite RR; eauto.
    match goal with RR : forall _, ~ In _ _ -> _ |- _ => rewrite RR; f_equal end.
    all: try match goal with
    | |- _ = _ =>
      assert (open_loc_close_vl v) by apply open_loc_close; rw;
      assert (close_fresh_vl v) by apply close_fresh; rw; auto
    end.
    all: match goal with
    | _ : context [gensym ?l] |- _ =>
      ii; exploit (gensym_spec l); auto;
      rewrite <- Heqℓ; repeat rewrite in_app_iff; auto
    end.
  Qed.

  Definition open_loc_lc_wvl `{Eq loc} (w : wvl var loc lang) (W : wvalue w) :=
    forall i ℓ, open_loc_wvl i ℓ w = w.

  Definition open_loc_lc_nv `{Eq loc} (σ : nv var loc lang) (Σ : env σ) :=
    forall i ℓ, open_loc_nv i ℓ σ = σ.

  Definition open_loc_lc_vl `{Eq loc} (v : vl var loc lang) (V : value v) :=
    forall i ℓ, open_loc_vl i ℓ v = v.

  Lemma open_loc_lc `{Name loc} :
    (forall w W, open_loc_lc_wvl w W) /\
    (forall σ Σ, open_loc_lc_nv σ Σ) /\
    (forall v V, open_loc_lc_vl v V).
  Proof.
    apply val_ind; ii; ss; repeat rw; eauto.
    remember (gensym (ℓ :: L ++ (floc_vl v))) as ν.
    replace v with (close_vl 0 ν (open_loc_vl 0 ν v)) at 1.
    assert (close_open_loc_vl (open_loc_vl 0 ν v)) as RR by apply close_open_loc.
    erewrite RR; eauto.
    match goal with RR : forall _, ~ In _ _ -> _ |- _ => rewrite RR; f_equal end.
    all: try match goal with
    | |- _ = _ =>
      assert (open_loc_close_vl v) by apply open_loc_close; rw;
      assert (close_fresh_vl v) by apply close_fresh; rw; auto
    end.
    all: match goal with
    | _ : context [gensym ?l] |- _ =>
      ii; exploit (gensym_spec l); auto;
      rewrite <- Heqν; ss; repeat rewrite in_app_iff; auto
    end.
  Qed.

  Definition open_wvl_subst_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_wvl u ℓ (open_wvl_wvl i u' w) =
      open_wvl_wvl i (subst_wvl_wvl u ℓ u') (subst_wvl_wvl u ℓ w)
  .

  Definition open_wvl_subst_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_nv u ℓ (open_wvl_nv i u' σ) =
      open_wvl_nv i (subst_wvl_wvl u ℓ u') (subst_wvl_nv u ℓ σ)
  .

  Definition open_wvl_subst_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ u' u (U : wvalue u),
      subst_wvl_vl u ℓ (open_wvl_vl i u' v) =
      open_wvl_vl i (subst_wvl_wvl u ℓ u') (subst_wvl_vl u ℓ v)
  .

  Lemma open_wvl_subst_wvl `{Name loc} :
    (forall w, open_wvl_subst_wvl_wvl w) /\
    (forall σ, open_wvl_subst_wvl_nv σ) /\
    (forall v, open_wvl_subst_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_wvl_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_wvl_subst_wvl_vl _ |- _ => erewrite RR; eauto
    end.
    assert (open_wvl_lc_wvl u U) by eapply open_wvl_lc.
    rw. eauto.
  Qed.

  Definition open_loc_subst_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_wvl u ℓ (open_loc_wvl i ν w) =
      open_loc_wvl i ν (subst_wvl_wvl u ℓ w)
  .

  Definition open_loc_subst_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_nv u ℓ (open_loc_nv i ν σ) =
      open_loc_nv i ν (subst_wvl_nv u ℓ σ)
  .

  Definition open_loc_subst_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν u (U : wvalue u) (NEQ : ℓ <> ν),
      subst_wvl_vl u ℓ (open_loc_vl i ν v) =
      open_loc_vl i ν (subst_wvl_vl u ℓ v)
  .

  Lemma open_loc_subst_wvl `{Name loc} :
    (forall w, open_loc_subst_wvl_wvl w) /\
    (forall σ, open_loc_subst_wvl_nv σ) /\
    (forall v, open_loc_subst_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_loc_subst_wvl_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_wvl_vl _ |- _ => erewrite RR; eauto
    end.
    assert (open_loc_lc_wvl u U) by apply open_loc_lc.
    rw. eauto.
  Qed.

  Definition open_loc_subst_loc_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_wvl ν ℓ (open_loc_wvl i ℓ' w) =
      open_loc_wvl i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_wvl ν ℓ w)
  .

  Definition open_loc_subst_loc_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_nv ν ℓ (open_loc_nv i ℓ' σ) =
      open_loc_nv i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_nv ν ℓ σ)
  .

  Definition open_loc_subst_loc_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ℓ' ν,
      subst_loc_vl ν ℓ (open_loc_vl i ℓ' v) =
      open_loc_vl i (if eqb ℓ ℓ' then ν else ℓ') (subst_loc_vl ν ℓ v)
  .

  Lemma open_loc_subst_loc `{Eq loc} :
    (forall w, open_loc_subst_loc_wvl w) /\
    (forall σ, open_loc_subst_loc_nv σ) /\
    (forall v, open_loc_subst_loc_vl v).
  Proof.
    apply pre_val_ind; ii; ss.
    all: repeat first [
      des_goal; eqb2eq loc; clarify|
      des_goal; eqb2eq nat; clarify].
    all: repeat match goal with
    | RR : open_loc_subst_loc_wvl _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_nv _ |- _ => erewrite RR; eauto
    | RR : open_loc_subst_loc_vl _ |- _ => erewrite RR; eauto
    end.
    all: repeat first [
      rewrite eqb_refl; auto |
      des_goal; eqb2eq loc; clarify].
  Qed.

  Definition subst_wvl_close_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_wvl i ℓ (subst_wvl_wvl u ν w) =
    subst_wvl_wvl u ν (close_wvl i ℓ w).

  Definition subst_wvl_close_nv `{Eq loc} (σ : nv var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_nv i ℓ (subst_wvl_nv u ν σ) =
    subst_wvl_nv u ν (close_nv i ℓ σ).

  Definition subst_wvl_close_vl `{Eq loc} (v : vl var loc lang) :=
    forall i ℓ ν u
      (NEQ : ℓ <> ν)
      (FRESH : ~ In ℓ (floc_wvl u)),
    close_vl i ℓ (subst_wvl_vl u ν v) =
    subst_wvl_vl u ν (close_vl i ℓ v).

  Ltac subst_wvl_close_tac :=
    repeat match goal with
    | H : subst_wvl_close_wvl _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_nv _ |- _ => rewrite H; eauto
    | H : subst_wvl_close_vl _ |- _ => rewrite H; eauto
    end.

  Lemma subst_wvl_close `{Eq loc} :
    (forall w, subst_wvl_close_wvl w) /\
    (forall σ, subst_wvl_close_nv σ) /\
    (forall v, subst_wvl_close_vl v).
  Proof.
    apply pre_val_ind; ii; ss; subst_wvl_close_tac.
    repeat des_goal; repeat eqb2eq loc; clarify;
    subst_wvl_close_tac.
    assert (close_fresh_wvl u) by apply close_fresh.
    rw; eauto.
  Qed.

  Definition floc_subst_wvl_wvl `{Eq loc} (w : wvl var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_wvl (subst_wvl_wvl u ℓ w))),
    (x <> ℓ /\ In x (floc_wvl w)) \/ In x (floc_wvl u).

  Definition floc_subst_wvl_nv `{Eq loc} (σ : nv var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_nv (subst_wvl_nv u ℓ σ))),
    (x <> ℓ /\ In x (floc_nv σ)) \/ In x (floc_wvl u).

  Definition floc_subst_wvl_vl `{Eq loc} (v : vl var loc lang) :=
    forall ℓ u x
      (IN : In x (floc_vl (subst_wvl_vl u ℓ v))),
    (x <> ℓ /\ In x (floc_vl v)) \/ In x (floc_wvl u).

  Lemma floc_subst_wvl `{Eq loc} :
    (forall w, floc_subst_wvl_wvl w) /\
    (forall σ, floc_subst_wvl_nv σ) /\
    (forall v, floc_subst_wvl_vl v).
  Proof.
    apply pre_val_ind; ii; ss;
    try solve [exploit H0; eauto].
    all: repeat des_hyp; repeat rewrite in_app_iff in *; des;
    repeat eqb2eq loc; subst; try solve [auto];
    match goal with
    | H : floc_subst_wvl_nv _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_wvl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    | H : floc_subst_wvl_vl _ |- _ => solve [exploit H; eauto; ii; des; auto]
    end.
  Qed.
End SubstFacts.

Section EquivFacts.
  Variable var : Set.
  Variable loc : Type.
  Variable lang : Type.

  Ltac equiv_lc_tac := 
    repeat match goal with
    | _ => solve [auto]
    | H : wvalue (_ _) |- _ => inv H
    | H : env (_ _) |- _ => inv H
    | H : value (_ _) |- _ => inv H
    | L : list loc, H : forall _, ~ In _ _ -> _ |- _ =>
      instantiate (1 := L); ii; exploit H; eauto; ii
    end.

  Lemma equiv_lc_wvl `{Eq loc} (w : wvl var loc lang) :
    forall f v' m (EQUIV : equiv w f v' m),
      wvalue w.
  Proof.
    ii. induction EQUIV;
    repeat econstructor;
    equiv_lc_tac.
  Qed.

  Lemma equiv_lc_nv `{Eq loc} :
    forall (σ : nv var loc lang) f v' m
      (EQUIV : equiv (wvl_v (vl_exp σ)) f v' m),
    env σ.
  Proof. ii. eapply equiv_lc_wvl in EQUIV. equiv_lc_tac. Qed.

  Lemma equiv_lc_vl `{Eq loc} :
    forall (v : vl var loc lang) f v' m
      (EQUIV : equiv (wvl_v v) f v' m),
    value v.
  Proof. ii. eapply equiv_lc_wvl in EQUIV. equiv_lc_tac. Qed.

  Lemma equiv_floc_free `{Name loc} (w : wvl var loc lang) f v' m (EQUIV : equiv w f v' m) :
    forall ℓ (FREEw : In ℓ (floc_wvl w)) (FREEf : f ℓ = None),
    m ℓ = None.
  Proof.
    induction EQUIV; ii; ss; des; clarify; eauto.
    - rewrite in_app_iff in *; des; eauto.
    - gensym_tac (L ++ floc_vl v) ν.
      exploit EQUIV; eauto. ii.
      exploit H1; eauto.
      apply open_inc_floc; eauto.
      unfold update. des_goal; eqb2eq loc; clarify.
  Qed.

  (* safe for future worlds that preserve free locations *)
  Lemma equiv_m_ext `{Eq loc} (w : wvl var loc lang) f v' m (EQUIV : equiv w f v' m) :
    forall m'
      (EXT : forall ℓ, m ℓ <> None -> m' ℓ = m ℓ)
      (AVOID : forall ℓ (FREEw : In ℓ (floc_wvl w)) (FREEf : f ℓ = None), m' ℓ = None),
    equiv w f v' m'.
  Proof.
    induction EQUIV; ii; ss.
    - econstructor.
    - econstructor; eauto.
      ii. exploit EXT; eauto. rw. eauto.
    - eapply equiv_floc; eauto.
    - econstructor.
      instantiate (1 := v').
      erewrite EXT; ii; clarify.
      eapply IHEQUIV1; eauto.
      ii. apply AVOID; eauto. rewrite in_app_iff; eauto.
      eapply IHEQUIV2; eauto.
      ii. apply AVOID; eauto. rewrite in_app_iff; eauto.
    - econstructor; eauto.
      instantiate (1 := ℓ').
      rewrite EXT; ii; clarify.
      instantiate (1 := L).
      ii. exploit H0; eauto.
      ii. eapply open_floc in FREEw.
      des; clarify.
      unfold update in FREEf. rewrite eqb_refl in FREEf. clarify.
      unfold update in FREEf. des_hyp; eqb2eq loc; clarify.
      apply AVOID; eauto.
    - econstructor; eauto.
  Qed.

  Lemma equiv_f_ext `{Eq loc} (w : wvl var loc lang) f v' m (EQUIV : equiv w f v' m) :
    forall f'
      (EXT : forall ℓ (DOM : In ℓ (floc_wvl w)), f ℓ = f' ℓ),
    equiv w f' v' m.
  Proof.
    induction EQUIV; ii.
    - econstructor.
    - econstructor; eauto.
      erewrite <- EXT; eauto. s. eauto.
      eapply IHEQUIV.
      ii. apply EXT; ss; eauto.
    - eapply equiv_floc; eauto.
      erewrite <- EXT; eauto. s. eauto.
      eapply IHEQUIV.
      ii. apply EXT; ss; eauto.
    - econstructor; eauto.
      eapply IHEQUIV1. ii. apply EXT; ss; rewrite in_app_iff; eauto.
      eapply IHEQUIV2. ii. apply EXT; ss; rewrite in_app_iff; eauto.
    - econstructor; eauto.
      instantiate (1 := L ++ floc_vl v). ss.
      ii. eapply H0; rewrite in_app_iff in *; split_nIn; eauto.
      ii. apply open_floc in DOM.
      des; clarify; unfold update;
      try solve [rewrite eqb_refl; eauto | des_goal; eqb2eq loc; auto].
    - econstructor; eauto.
  Qed.

  Lemma extend_m_floc `{Eq loc} (w : wvl var loc lang) f v' m (EQUIV : equiv w f v' m) :
    forall ℓ u' (FREEm : m ℓ = None) (FREEf : f ℓ = None),
      equiv w (ℓ !-> ℓ ; f) v' (ℓ !-> u' ; m).
  Proof.
    induction EQUIV; ii; ss.
    - econstructor.
    - econstructor.
      all: solve [unfold update; des_goal; eqb2eq loc; clarify | eauto].
    - case_eqb ℓ ℓ0.
      + eapply equiv_bloc.
        all: solve [unfold update; rewrite eqb_refl; ii; clarify | eauto].
      + eapply equiv_floc.
        all: solve [unfold update; des_goal; eqb2eq loc; clarify | eauto].
    - econstructor.
      instantiate (1 := v').
      unfold update. des_goal; eqb2eq loc; clarify.
      all:eauto.
    - econstructor. instantiate (1 := ℓ').
      unfold update. des_goal; eqb2eq loc; clarify.
      instantiate (1 := ℓ :: L).
      ii. ss. split_nIn.
      exploit H0; eauto.
      unfold update. des_goal; eqb2eq loc; clarify.
      instantiate (1 := u').
      ii.
      eapply equiv_f_ext; eauto.
      ii. erewrite update_switch; eauto.
    - econstructor; eauto.
  Qed.
End EquivFacts.

