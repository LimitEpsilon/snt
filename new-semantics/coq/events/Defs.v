From Basics Require Import Basics.
From With_events Require Import Syntax.

Section PreDefs.
  Context {var lbl loc lang : Type}.

  (* pre-values *)
  Inductive wvl :=
  | wvl_v (v : vl) (* v *)
  | wvl_recv (p : lbl) (v : vl) (* μ.v *)

  with nv :=
  | nv_mt (* • *)
  | nv_ev (E : vnt) (* [E] *)
  | nv_bloc (x : var) (n : nat) (σ : nv) (* bound location *)
  | nv_floc (x : var) (ℓ : loc * lbl) (σ : nv) (* free location *)
  | nv_bval (x : var) (w : wvl) (σ : nv) (* bound value *)

  with vl :=
  | vl_ev (E : vnt)
  | vl_exp (σ : nv)
  | vl_clos (e : lang) (σ : nv)
  | vl_nat (n : nat)

  with vnt :=
  | Init
  | Read (E : vnt) (x : var)
  | Call (E : vnt) (v : vl)
  | Succ (E : vnt)
  | Pred (E : vnt)
  .

  Scheme wvl_ind_mut := Induction for wvl Sort Prop
  with nv_ind_mut := Induction for nv Sort Prop
  with vl_ind_mut := Induction for vl Sort Prop
  with vnt_ind_mut := Induction for vnt Sort Prop.

  Combined Scheme pre_val_ind from wvl_ind_mut, nv_ind_mut, vl_ind_mut, vnt_ind_mut.
End PreDefs.

Arguments wvl : clear implicits.
Arguments nv : clear implicits.
Arguments vl : clear implicits.
Arguments vnt : clear implicits.

Definition predE {var lbl loc lang} (E : vnt var lbl loc lang) :=
  match E with
  | Init | Read _ _ | Call _ _ | Pred _ => Pred E
  | Succ E => E
  end.

(* mutual fixpoints must be defined outside of Section to be simpl'd *)
(* https://github.com/coq/coq/issues/3488 *)

(* open the bound location i with ℓ *)
Fixpoint open_loc_wvl {var lbl loc lang} (i : nat) (ℓ : loc * lbl) (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v => wvl_v (open_loc_vl i ℓ v)
  | wvl_recv p v => wvl_recv p (open_loc_vl (S i) ℓ v)
  end

with open_loc_nv {var lbl loc lang} (i : nat) (ℓ : loc * lbl) (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (open_loc_vnt i ℓ E)
  | nv_bloc x n σ' =>
    if i =? n
    then nv_floc x ℓ (open_loc_nv i ℓ σ')
    else nv_bloc x n (open_loc_nv i ℓ σ')
  | nv_floc x ℓ' σ' =>
    nv_floc x ℓ' (open_loc_nv i ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (open_loc_wvl i ℓ w) (open_loc_nv i ℓ σ')
  end

with open_loc_vl {var lbl loc lang} (i : nat) (ℓ : loc * lbl) (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => vl_ev (open_loc_vnt i ℓ E)
  | vl_exp σ => vl_exp (open_loc_nv i ℓ σ)
  | vl_clos e σ => vl_clos e (open_loc_nv i ℓ σ)
  | vl_nat n => vl_nat n
  end

with open_loc_vnt {var lbl loc lang} (i : nat) (ℓ : loc * lbl) (E : vnt var lbl loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (open_loc_vnt i ℓ E) x
  | Call E v => Call (open_loc_vnt i ℓ E) (open_loc_vl i ℓ v)
  | Succ E => Succ (open_loc_vnt i ℓ E)
  | Pred E => Pred (open_loc_vnt i ℓ E)
  end.

(* close the free location ℓ with the binding depth i *)
Fixpoint close_wvl {var lbl loc lang} `{Eq lbl} `{Eq loc} (i : nat) (ℓ : loc * lbl) (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v => wvl_v (close_vl i ℓ v)
  | wvl_recv p v => wvl_recv p (close_vl (S i) ℓ v)
  end

with close_nv {var lbl loc lang} `{Eq lbl} `{Eq loc} (i : nat) (ℓ : loc * lbl) (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (close_vnt i ℓ E)
  | nv_bloc x n σ' =>
    nv_bloc x n (close_nv i ℓ σ')
  | nv_floc x ℓ' σ' =>
    if eqb ℓ ℓ'
    then nv_bloc x i (close_nv i ℓ σ')
    else nv_floc x ℓ' (close_nv i ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (close_wvl i ℓ w) (close_nv i ℓ σ')
  end

with close_vl {var lbl loc lang} `{Eq lbl} `{Eq loc} (i : nat) (ℓ : loc * lbl) (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => vl_ev (close_vnt i ℓ E)
  | vl_exp σ => vl_exp (close_nv i ℓ σ)
  | vl_clos e σ => vl_clos e (close_nv i ℓ σ)
  | vl_nat n => vl_nat n
  end

with close_vnt {var lbl loc lang} `{Eq lbl} `{Eq loc} (i : nat) (ℓ : loc * lbl) (E : vnt var lbl loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (close_vnt i ℓ E) x
  | Call E v => Call (close_vnt i ℓ E) (close_vl i ℓ v)
  | Succ E => Succ (close_vnt i ℓ E)
  | Pred E => Pred (close_vnt i ℓ E)
  end.

(* open the bound location i with u *)
Fixpoint open_wvl_wvl {var lbl loc lang} (i : nat) (u : wvl var lbl loc lang) (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v => wvl_v (open_wvl_vl i u v)
  | wvl_recv p v => wvl_recv p (open_wvl_vl (S i) u v)
  end

with open_wvl_nv {var lbl loc lang} (i : nat) (u : wvl var lbl loc lang) (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (open_wvl_vnt i u E)
  | nv_bloc x n σ' =>
    if i =? n
    then nv_bval x u (open_wvl_nv i u σ')
    else nv_bloc x n (open_wvl_nv i u σ')
  | nv_floc x ℓ' σ' =>
    nv_floc x ℓ' (open_wvl_nv i u σ')
  | nv_bval x w σ' =>
    nv_bval x (open_wvl_wvl i u w) (open_wvl_nv i u σ')
  end

with open_wvl_vl {var lbl loc lang} (i : nat) (u : wvl var lbl loc lang) (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => vl_ev (open_wvl_vnt i u E)
  | vl_exp σ => vl_exp (open_wvl_nv i u σ)
  | vl_clos e σ => vl_clos e (open_wvl_nv i u σ)
  | vl_nat n => vl_nat n
  end

with open_wvl_vnt {var lbl loc lang} (i : nat) (u : wvl var lbl loc lang) (E : vnt var lbl loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (open_wvl_vnt i u E) x
  | Call E v => Call (open_wvl_vnt i u E) (open_wvl_vl i u v)
  | Succ E => Succ (open_wvl_vnt i u E)
  | Pred E => Pred (open_wvl_vnt i u E)
  end.

(* substitute the free location ℓ for ℓ' *)
Fixpoint subst_loc_wvl {var lbl loc lang} `{Eq lbl} `{Eq loc} (ν ℓ : loc * lbl) (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v => wvl_v (subst_loc_vl ν ℓ v)
  | wvl_recv p v => wvl_recv p (subst_loc_vl ν ℓ v)
  end

with subst_loc_nv {var lbl loc lang} `{Eq lbl} `{Eq loc} (ν ℓ : loc * lbl) (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (subst_loc_vnt ν ℓ E)
  | nv_bloc x n σ' =>
    nv_bloc x n (subst_loc_nv ν ℓ σ')
  | nv_floc x ℓ' σ' =>
    if eqb ℓ ℓ'
    then nv_floc x ν (subst_loc_nv ν ℓ σ')
    else nv_floc x ℓ' (subst_loc_nv ν ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (subst_loc_wvl ν ℓ w) (subst_loc_nv ν ℓ σ')
  end

with subst_loc_vl {var lbl loc lang} `{Eq lbl} `{Eq loc} (ν ℓ : loc * lbl) (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => vl_ev (subst_loc_vnt ν ℓ E)
  | vl_exp σ => vl_exp (subst_loc_nv ν ℓ σ)
  | vl_clos e σ => vl_clos e (subst_loc_nv ν ℓ σ)
  | vl_nat n => vl_nat n
  end

with subst_loc_vnt {var lbl loc lang} `{Eq lbl} `{Eq loc} (ν ℓ : loc * lbl) (E : vnt var lbl loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (subst_loc_vnt ν ℓ E) x
  | Call E v => Call (subst_loc_vnt ν ℓ E) (subst_loc_vl ν ℓ v)
  | Succ E => Succ (subst_loc_vnt ν ℓ E)
  | Pred E => Pred (subst_loc_vnt ν ℓ E)
  end.

(* multiple substitutions *)
Fixpoint map_wvl {var lbl loc lang} (φ : loc -> loc) (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v => wvl_v (map_vl φ v)
  | wvl_recv p v => wvl_recv p (map_vl φ v)
  end

with map_nv {var lbl loc lang} (φ : loc -> loc) (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (map_vnt φ E)
  | nv_bloc x n σ' =>
    nv_bloc x n (map_nv φ σ')
  | nv_floc x (ℓ', p') σ' =>
    nv_floc x (φ ℓ', p') (map_nv φ σ')
  | nv_bval x w σ' =>
    nv_bval x (map_wvl φ w) (map_nv φ σ')
  end

with map_vl {var lbl loc lang} (φ : loc -> loc) (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => vl_ev (map_vnt φ E)
  | vl_exp σ => vl_exp (map_nv φ σ)
  | vl_clos e σ => vl_clos e (map_nv φ σ)
  | vl_nat n => vl_nat n
  end

with map_vnt {var lbl loc lang} (φ : loc -> loc) (E : vnt var lbl loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (map_vnt φ E) x
  | Call E v => Call (map_vnt φ E) (map_vl φ v)
  | Succ E => Succ (map_vnt φ E)
  | Pred E => Pred (map_vnt φ E)
  end.

(* substitute the free location ℓ for u *)
Fixpoint subst_wvl_wvl {var lbl loc lang} `{Eq lbl} `{Eq loc} (u : wvl var lbl loc lang) (ℓ : loc * lbl) (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v => wvl_v (subst_wvl_vl u ℓ v)
  | wvl_recv p v => wvl_recv p (subst_wvl_vl u ℓ v)
  end

with subst_wvl_nv {var lbl loc lang} `{Eq lbl} `{Eq loc} (u : wvl var lbl loc lang) (ℓ : loc * lbl) (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (subst_wvl_vnt u ℓ E)
  | nv_bloc x n σ' =>
    nv_bloc x n (subst_wvl_nv u ℓ σ')
  | nv_floc x ℓ' σ' =>
    if eqb ℓ ℓ'
    then nv_bval x u (subst_wvl_nv u ℓ σ')
    else nv_floc x ℓ' (subst_wvl_nv u ℓ σ')
  | nv_bval x w σ' =>
    nv_bval x (subst_wvl_wvl u ℓ w) (subst_wvl_nv u ℓ σ')
  end

with subst_wvl_vl {var lbl loc lang} `{Eq lbl} `{Eq loc} (u : wvl var lbl loc lang) (ℓ : loc * lbl) (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => vl_ev (subst_wvl_vnt u ℓ E)
  | vl_exp σ => vl_exp (subst_wvl_nv u ℓ σ)
  | vl_clos e σ => vl_clos e (subst_wvl_nv u ℓ σ)
  | vl_nat n => vl_nat n
  end

with subst_wvl_vnt {var lbl loc lang} `{Eq lbl} `{Eq loc} (u : wvl var lbl loc lang) (ℓ : loc * lbl) (E : vnt var lbl loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (subst_wvl_vnt u ℓ E) x
  | Call E v => Call (subst_wvl_vnt u ℓ E) (subst_wvl_vl u ℓ v)
  | Succ E => Succ (subst_wvl_vnt u ℓ E)
  | Pred E => Pred (subst_wvl_vnt u ℓ E)
  end.

(* free locations *)
Fixpoint floc_wvl {var lbl loc lang} (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v | wvl_recv _ v => floc_vl v
  end

with floc_nv {var lbl loc lang} (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => []
  | nv_ev E => floc_vnt E
  | nv_bloc _ _ σ' => floc_nv σ'
  | nv_floc _ (ℓ, p) σ' => ℓ :: floc_nv σ'
  | nv_bval _ w σ' => floc_wvl w ++ floc_nv σ'
  end

with floc_vl {var lbl loc lang} (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => floc_vnt E
  | vl_exp σ | vl_clos _ σ => floc_nv σ
  | vl_nat _ => []
  end

with floc_vnt {var lbl loc lang} (E : vnt var lbl loc lang) :=
  match E with
  | Init => []
  | Read E x => floc_vnt E
  | Call E v => floc_vnt E ++ floc_vl v
  | Succ E | Pred E => floc_vnt E
  end.

(* free labelled locations *)
Fixpoint flloc_wvl {var lbl loc lang} (w : wvl var lbl loc lang) :=
  match w with
  | wvl_v v | wvl_recv _ v => flloc_vl v
  end

with flloc_nv {var lbl loc lang} (σ : nv var lbl loc lang) :=
  match σ with
  | nv_mt => []
  | nv_ev E => flloc_vnt E
  | nv_bloc _ _ σ' => flloc_nv σ'
  | nv_floc _ ℓ σ' => ℓ :: flloc_nv σ'
  | nv_bval _ w σ' => flloc_wvl w ++ flloc_nv σ'
  end

with flloc_vl {var lbl loc lang} (v : vl var lbl loc lang) :=
  match v with
  | vl_ev E => flloc_vnt E
  | vl_exp σ | vl_clos _ σ => flloc_nv σ
  | vl_nat _ => []
  end

with flloc_vnt {var lbl loc lang} (E : vnt var lbl loc lang) :=
  match E with
  | Init => []
  | Read E x => flloc_vnt E
  | Call E v => flloc_vnt E ++ flloc_vl v
  | Succ E | Pred E => flloc_vnt E
  end.

Section LCDefs.
  Context {var lbl loc lang : Type}.

  (* locally closed predicates *)
  Inductive wvalue : wvl var lbl loc lang -> Prop :=
  | wvalue_v v (VAL : value v) : wvalue (wvl_v v)
  | wvalue_recv L p v
    (VAL : forall ℓ, ~ In ℓ L -> value (open_loc_vl 0 (ℓ, p) v))
  : wvalue (wvl_recv p v)

  with env : nv var lbl loc lang -> Prop :=
  | env_mt : env nv_mt
  | env_ev E (EVENT : event E) : env (nv_ev E)
  | env_floc x ℓ σ (ENV : env σ) : env (nv_floc x ℓ σ)
  | env_bval x w σ (WVALUE : wvalue w) (ENV : env σ) : env (nv_bval x w σ)

  with value : vl var lbl loc lang -> Prop :=
  | value_ev E (EVENT : event E) : value (vl_ev E)
  | value_exp σ (ENV : env σ) : value (vl_exp σ)
  | value_clos e σ (ENV : env σ) : value (vl_clos e σ)
  | value_nat n : value (vl_nat n)

  with event : vnt var lbl loc lang -> Prop :=
  | event_Init : event Init
  | event_Read E x (EVENT : event E) : event (Read E x)
  | event_Call E v (EVENT : event E) (VAL : value v) : event (Call E v)
  | event_Succ E (EVENT : event E) : event (Succ E)
  | event_Pred E (EVENT : event E) : event (Pred E)
  .

  Scheme wvalue_ind_mut := Induction for wvalue Sort Prop
  with env_ind_mut := Induction for env Sort Prop
  with value_ind_mut := Induction for value Sort Prop
  with event_ind_mut := Induction for event Sort Prop.

  Combined Scheme val_ind from wvalue_ind_mut, env_ind_mut, value_ind_mut, event_ind_mut.
End LCDefs.

Section eqb.
  Context {var lbl} `{EqVar : Eq var} `{EqLbl : Eq lbl}.

  Fixpoint eqb_tm (t1 t2 : @tm var lbl) :=
    match t1, t2 with
    | tm_var x1, tm_var x2 => eqb x1 x2
    | tm_lam x1 t1, tm_lam x2 t2 => eqb x1 x2 && eqb_ltm t1 t2
    | tm_app t11 t12, tm_app t21 t22 =>
      eqb_ltm t11 t21 && eqb_ltm t12 t22
    | tm_link t11 t12, tm_link t21 t22 =>
      eqb_ltm t11 t21 && eqb_ltm t12 t22
    | tm_mt, tm_mt => true
    | tm_bind x1 t11 t12, tm_bind x2 t21 t22 =>
      eqb x1 x2 && eqb_ltm t11 t21 && eqb_ltm t12 t22
    | tm_zero, tm_zero => true
    | tm_succ t1, tm_succ t2 => eqb_ltm t1 t2
    | tm_case t1 z1 n1 s1, tm_case t2 z2 n2 s2 =>
      eqb_ltm t1 t2 && eqb_ltm z1 z2 && eqb n1 n2 && eqb_ltm s1 s2
    | _, _ => false
    end

  with eqb_ltm (t1 t2 : @ltm var lbl) :=
    match t1, t2 with
    | lblled p1 t1, lblled p2 t2 =>
      eqb p1 p2 && eqb_tm t1 t2
    end.

  Lemma eqb_term :
    (forall t1 t2, eqb_tm t1 t2 = true <-> t1 = t2) /\
    (forall t1 t2, eqb_ltm t1 t2 = true <-> t1 = t2).
  Proof.
    apply term_ind; ii; split; ii;
    try match goal with
    | |- _ = true =>
      repeat rrw; s; try rewrite eqb_refl; s;
      repeat rw; try reflexivity;
      repeat rewrite andb_true_iff; repeat split;
      rw; reflexivity
    | RR : _ _ ?t = true |- _ =>
      destruct t; ss; repeat des_hyp;
      f_equal;
      first [eqb2eq var | eqb2eq loc | eqb2eq lbl | rrw]; auto;
      rrw; auto
    end.
  Qed.
End eqb.

#[export, refine] Instance EqTm {var lbl} `{EqVar : Eq var} `{EqLbl : Eq lbl} : Eq (@tm var lbl) :=
{
  eqb := @eqb_tm var lbl EqVar EqLbl;
}.
  apply eqb_term.
Defined.

#[export, refine] Instance EqLtm {var lbl} `{EqVar : Eq var} `{EqLbl : Eq lbl} : Eq (@ltm var lbl) :=
{
  eqb := @eqb_ltm var lbl EqVar EqLbl;
}.
  apply eqb_term.
Defined.

Definition update {loc T} `{Eq loc} (f : loc -> option T) ℓ ℓ' ℓ_param :=
  if eqb ℓ ℓ_param then Some ℓ' else f ℓ_param.

Notation "ℓ '!->' ℓℓ ';' f" := (update f ℓ ℓℓ)
  (at level 100, ℓℓ at next level, right associativity).

Lemma update_ext {loc T} `{Eq loc} L (f f' : loc -> option T) ℓ ℓ' :
  (forall x, In x L -> f x = f' x) ->
  (forall x, x = ℓ \/ In x L -> (ℓ !-> ℓ' ; f) x = (ℓ !-> ℓ' ; f') x).
Proof. ii; unfold update; des_goal; repeat rw; eauto. eqb2eq loc; des; clarify. Qed.

Lemma update_comm {loc T} `{Eq loc} (f : loc -> option T) ℓ ℓ' ν ν' x :
  ℓ <> ν ->
  (ℓ !-> ℓ' ; ν !-> ν' ; f) x = (ν !-> ν' ; ℓ !-> ℓ' ; f) x.
Proof.
  ii. unfold update.
  des_ifs; eqb2eq loc; clarify.
Qed.

Definition swap {loc T} `{Eq loc} (f : loc -> T) ℓ ν x :=
  if eqb x ℓ then f ν else if eqb x ν then f ℓ else f x.

Lemma swap_update_assoc {loc T} `{Eq loc} (f : loc -> option T) ℓ' ℓ ν x :
  x <> ν -> x <> ℓ ->
  forall y,
    swap (x !-> ℓ'; f) ν ℓ y = (x !-> ℓ'; swap f ν ℓ) y.
Proof.
  ii. unfold swap, update.
  des_ifs; eqb2eq loc; clarify.
Qed.

(* one-to-one, or injective, function *)
Definition oto {A B} (φ : A -> B) := forall ℓ ν (fEQ : φ ℓ = φ ν), ℓ = ν.

(* about predE *)
Lemma predE_map {var lbl loc lang} φ (E : vnt var lbl loc lang) :
  map_vnt φ (predE E) = predE (map_vnt φ E).
Proof. destruct E; simpl; auto. Qed.

Lemma predE_flloc {var lbl loc lang} (E : vnt var lbl loc lang) :
  flloc_vnt (predE E) = flloc_vnt E.
Proof. destruct E; simpl; auto. Qed.

Lemma predE_subst_loc {var lbl loc lang} `{Eq lbl, Eq loc, Eq lbl} ν ℓ (E : vnt var lbl loc lang) :
  subst_loc_vnt ν ℓ (predE E) = predE (subst_loc_vnt ν ℓ E).
Proof. destruct E; simpl; auto. Qed.

Lemma predE_subst_wvl {var lbl loc lang} `{Eq lbl, Eq loc, Eq lbl} u ℓ (E : vnt var lbl loc lang) :
  subst_wvl_vnt u ℓ (predE E) = predE (subst_wvl_vnt u ℓ E).
Proof. destruct E; simpl; auto. Qed.

Lemma predE_lc {var lbl loc lang} (E : vnt var lbl loc lang) :
  event E -> event (predE E).
Proof. destruct E; ss; intro LC; try constructor; auto. inv LC. auto. Qed.

Hint Resolve predE_lc : core.

