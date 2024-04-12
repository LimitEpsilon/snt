From Basics Require Import Basics.

Section PreDefs.
  Variable var : Type.
  Variable loc : Type.
  Variable lang : Type.

  (* pre-values *)
  Inductive wvl :=
  | wvl_v (v : vl) (* v *)
  | wvl_recv (v : vl) (* μ.v *)

  with nv :=
  | nv_mt (* • *)
  | nv_ev (E : vnt) (* [E] *)
  | nv_bloc (x : var) (n : nat) (σ : nv) (* bound location *)
  | nv_floc (x : var) (ℓ : loc) (σ : nv) (* free location *)
  | nv_bval (x : var) (w : wvl) (σ : nv) (* bound value *)

  with vl :=
  | vl_ev (E : vnt)
  | vl_exp (σ : nv)
  | vl_clos (e : lang) (σ : nv)

  with vnt :=
  | Init
  | Read (E : vnt) (x : var)
  | Call (E : vnt) (v : vl)
  .

  Scheme wvl_ind_mut := Induction for wvl Sort Prop
  with nv_ind_mut := Induction for nv Sort Prop
  with vl_ind_mut := Induction for vl Sort Prop
  with vnt_ind_mut := Induction for vnt Sort Prop.

  Combined Scheme pre_val_ind from wvl_ind_mut, nv_ind_mut, vl_ind_mut, vnt_ind_mut.
End PreDefs.

Arguments wvl_v {var loc lang}.
Arguments wvl_recv {var loc lang}.
Arguments nv_mt {var loc lang}.
Arguments nv_ev {var loc lang}.
Arguments nv_bloc {var loc lang}.
Arguments nv_floc {var loc lang}.
Arguments nv_bval {var loc lang}.
Arguments vl_exp {var loc lang}.
Arguments vl_clos {var loc lang}.
Arguments vl_ev {var loc lang}.
Arguments Init {var loc lang}.
Arguments Read {var loc lang}.
Arguments Call {var loc lang}.

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

with open_loc_vl {var loc lang} (i : nat) (ℓ : loc) (v : vl var loc lang) :=
  match v with
  | vl_ev E => vl_ev (open_loc_vnt i ℓ E)
  | vl_exp σ => vl_exp (open_loc_nv i ℓ σ)
  | vl_clos e σ => vl_clos e (open_loc_nv i ℓ σ)
  end

with open_loc_vnt {var loc lang} (i : nat) (ℓ : loc) (E : vnt var loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (open_loc_vnt i ℓ E) x
  | Call E v => Call (open_loc_vnt i ℓ E) (open_loc_vl i ℓ v)
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

with close_vl {var loc lang} `{Eq loc} (i : nat) (ℓ : loc) (v : vl var loc lang) :=
  match v with
  | vl_ev E => vl_ev (close_vnt i ℓ E)
  | vl_exp σ => vl_exp (close_nv i ℓ σ)
  | vl_clos e σ => vl_clos e (close_nv i ℓ σ)
  end

with close_vnt {var loc lang} `{Eq loc} (i : nat) (ℓ : loc) (E : vnt var loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (close_vnt i ℓ E) x
  | Call E v => Call (close_vnt i ℓ E) (close_vl i ℓ v)
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

with open_wvl_vl {var loc lang} (i : nat) (u : wvl var loc lang) (v : vl var loc lang) :=
  match v with
  | vl_ev E => vl_ev (open_wvl_vnt i u E)
  | vl_exp σ => vl_exp (open_wvl_nv i u σ)
  | vl_clos e σ => vl_clos e (open_wvl_nv i u σ)
  end

with open_wvl_vnt {var loc lang} (i : nat) (u : wvl var loc lang) (E : vnt var loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (open_wvl_vnt i u E) x
  | Call E v => Call (open_wvl_vnt i u E) (open_wvl_vl i u v)
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

with subst_loc_vl {var loc lang} `{Eq loc} (ν ℓ : loc) (v : vl var loc lang) :=
  match v with
  | vl_ev E => vl_ev (subst_loc_vnt ν ℓ E)
  | vl_exp σ => vl_exp (subst_loc_nv ν ℓ σ)
  | vl_clos e σ => vl_clos e (subst_loc_nv ν ℓ σ)
  end

with subst_loc_vnt {var loc lang} `{Eq loc} (ν ℓ : loc) (E : vnt var loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (subst_loc_vnt ν ℓ E) x
  | Call E v => Call (subst_loc_vnt ν ℓ E) (subst_loc_vl ν ℓ v)
  end.

(* multiple substitutions *)
Fixpoint map_wvl {var loc lang} (φ : loc -> loc) (w : wvl var loc lang) :=
  match w with
  | wvl_v v => wvl_v (map_vl φ v)
  | wvl_recv v => wvl_recv (map_vl φ v)
  end

with map_nv {var loc lang} (φ : loc-> loc) (σ : nv var loc lang) :=
  match σ with
  | nv_mt => nv_mt
  | nv_ev E => nv_ev (map_vnt φ E)
  | nv_bloc x n σ' =>
    nv_bloc x n (map_nv φ σ')
  | nv_floc x ℓ' σ' =>
    nv_floc x (φ ℓ') (map_nv φ σ')
  | nv_bval x w σ' =>
    nv_bval x (map_wvl φ w) (map_nv φ σ')
  end

with map_vl {var loc lang} (φ : loc -> loc) (v : vl var loc lang) :=
  match v with
  | vl_ev E => vl_ev (map_vnt φ E)
  | vl_exp σ => vl_exp (map_nv φ σ)
  | vl_clos e σ => vl_clos e (map_nv φ σ)
  end

with map_vnt {var loc lang} (φ : loc -> loc) (E : vnt var loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (map_vnt φ E) x
  | Call E v => Call (map_vnt φ E) (map_vl φ v)
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

with subst_wvl_vl {var loc lang} `{Eq loc} (u : wvl var loc lang) (ℓ : loc) (v : vl var loc lang) :=
  match v with
  | vl_ev E => vl_ev (subst_wvl_vnt u ℓ E)
  | vl_exp σ => vl_exp (subst_wvl_nv u ℓ σ)
  | vl_clos e σ => vl_clos e (subst_wvl_nv u ℓ σ)
  end

with subst_wvl_vnt {var loc lang} `{Eq loc} (u : wvl var loc lang) (ℓ : loc) (E : vnt var loc lang) :=
  match E with
  | Init => Init
  | Read E x => Read (subst_wvl_vnt u ℓ E) x
  | Call E v => Call (subst_wvl_vnt u ℓ E) (subst_wvl_vl u ℓ v)
  end.

(* free locations *)
Fixpoint floc_wvl {var loc lang} (w : wvl var loc lang) :=
  match w with
  | wvl_v v | wvl_recv v => floc_vl v
  end

with floc_nv {var loc lang} (σ : nv var loc lang) :=
  match σ with
  | nv_mt => []
  | nv_ev E => floc_vnt E
  | nv_bloc _ _ σ' => floc_nv σ'
  | nv_floc _ ℓ σ' => ℓ :: floc_nv σ'
  | nv_bval _ w σ' => floc_wvl w ++ floc_nv σ'
  end

with floc_vl {var loc lang} (v : vl var loc lang) :=
  match v with
  | vl_ev E => floc_vnt E
  | vl_exp σ | vl_clos _ σ => floc_nv σ
  end

with floc_vnt {var loc lang} (E : vnt var loc lang) :=
  match E with
  | Init => []
  | Read E x => floc_vnt E
  | Call E v => floc_vnt E ++ floc_vl v
  end.

Section LCDefs.
  Variable var : Type.
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
  | env_ev E (EVENT : event E) : env (nv_ev E)
  | env_floc x ℓ σ (ENV : env σ) : env (nv_floc x ℓ σ)
  | env_bval x w σ (WVALUE : wvalue w) (ENV : env σ) : env (nv_bval x w σ)

  with value : vl var loc lang -> Prop :=
  | value_ev E (EVENT : event E) : value (vl_ev E)
  | value_exp σ (ENV : env σ) : value (vl_exp σ)
  | value_clos e σ (ENV : env σ) : value (vl_clos e σ)

  with event : vnt var loc lang -> Prop :=
  | event_Init : event Init
  | event_Read E x (EVENT : event E) : event (Read E x)
  | event_Call E v (EVENT : event E) (VAL : value v) : event (Call E v)
  .

  Scheme wvalue_ind_mut := Induction for wvalue Sort Prop
  with env_ind_mut := Induction for env Sort Prop
  with value_ind_mut := Induction for value Sort Prop
  with event_ind_mut := Induction for event Sort Prop.

  Combined Scheme val_ind from wvalue_ind_mut, env_ind_mut, value_ind_mut, event_ind_mut.
End LCDefs.

Arguments wvalue {var loc lang}.
Arguments wvalue_v {var loc lang}.
Arguments wvalue_recv {var loc lang}.
Arguments env {var loc lang}.
Arguments env_ev {var loc lang}.
Arguments env_mt {var loc lang}.
Arguments env_floc {var loc lang}.
Arguments env_bval {var loc lang}.
Arguments value {var loc lang}.
Arguments value_ev {var loc lang}.
Arguments value_exp {var loc lang}.
Arguments value_clos {var loc lang}.
Arguments event {var loc lang}.
Arguments event_Init {var loc lang}.
Arguments event_Read {var loc lang}.
Arguments event_Call {var loc lang}.

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

Definition remove {loc T} `{Eq loc} (f : loc -> option T) ℓ ℓ_param :=
  if eqb ℓ ℓ_param then None else f ℓ_param.

Notation "f '!!' ℓ" := (remove f ℓ)
  (at level 100, ℓ at next level, right associativity).

Lemma remove_assoc {loc T} `{Eq loc} (f : loc -> option T) ℓ ℓ' x :
  ((f !! ℓ) !! ℓ') x = ((f !! ℓ') !! ℓ) x.
Proof.
  ii. unfold remove. des_ifs.
Qed.

Lemma remove_update_assoc {loc T} `{Eq loc} (f : loc -> option T) ℓ ν ℓ' x :
  ℓ <> ν ->
  ((ℓ !-> ℓ' ; f) !! ν) x = (ℓ !-> ℓ' ; f !! ν) x.
Proof.
  ii. unfold remove, update.
  des_ifs. eqb2eq loc. clarify.
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
