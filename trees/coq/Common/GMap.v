(*****************************************************************************
Copyright: std++ developers and contributors

------------------------------------------------------------------------------

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the copyright holder nor the names of its contributors
      may be used to endorse or promote products derived from this software
      without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
******************************************************************************)

From Stdlib Require Import Utf8 Program.Basics.
From Koika Require Import Common PMapDep PMap Environments IndexUtils.

Local Open Scope positive.
Local Open Scope program_scope.

Local Generalizable All Variables.

(** Note that [Countable A] gives rise to [EqDecision A] by checking equality of
the results of [encode]. This instance of [EqDecision A] is very inefficient, so
the native decider is typically preferred for actual computation. To avoid
overlapping instances, we include [EqDecision A] explicitly as a parameter of
[Countable A]. *)
Class Countable A `{EqDec A} := {
  encode : A → positive;
  decode : positive → option A;
  decode_encode x : decode (encode x) = Some x
}.
Global Hint Mode Countable ! - : typeclass_instances.
Global Arguments encode : simpl never.
Global Arguments decode : simpl never.

(** * Instances *)
(** ** Injection *)
Section inj_countable.
  Context `{Countable A, EqDec B}.
  Context (f : B → A) (g : A → option B) (fg : ∀ x, g (f x) = Some x).

  Program Definition inj_countable : Countable B :=
    {| encode y := encode (f y); decode p := match decode p with Some x => g x | _ => None end |}.
  Next Obligation. now rewrite decode_encode. Qed.
End inj_countable.

Section inj_countable'.
  Context `{Countable A, EqDec B}.
  Context (f : B → A) (g : A → B) (fg : ∀ x, g (f x) = x).

  Program Definition inj_countable' : Countable B := inj_countable f (Some ∘ g) _.
  Next Obligation. cbv. now f_equal. Qed.
End inj_countable'.

(** ** Empty *)
Global Program Instance Empty_set_countable : Countable Empty_set :=
  {| encode u := 1; decode p := None |}.
Next Obligation. destruct x. Qed.

(** ** Unit *)
Global Program Instance unit_countable : Countable unit :=
  {| encode u := 1; decode p := Some tt |}.
Next Obligation. now destruct x. Qed.

(** ** Bool *)
Global Program Instance bool_countable : Countable bool := {|
  encode b := if b then 1 else 2;
  decode p := Some match p return bool with 1 => true | _ => false end
|}.
Next Obligation. now destruct x. Qed.

(** ** Option *)
Global Program Instance option_countable `{Countable A} : Countable (option A) := {|
  encode o := match o with None => 1 | Some x => Pos.succ (encode x) end;
  decode p := if eq_dec p 1 then Some None else match decode (Pos.pred p) with Some x => Some (Some x) | None => None end
|}.
Next Obligation.
  match goal with |- (if ?f ?x 1 then _ else _) = _ => change (f x 1) with (eq_dec x 1) end.
  destruct x. 2: rewrite eq_dec_refl; auto.
  destruct (eq_dec _ 1); [lia|].
  now rewrite Pos.pred_succ, decode_encode.
Qed.

(** ** Sums *)
Global Program Instance sum_countable `{Countable A} `{Countable B} :
  Countable (A + B)%type := {|
    encode xy :=
      match xy with inl x => (encode x)~0 | inr y => (encode y)~1 end;
    decode p :=
      match p with
      | 1 => None
      | p~0 => match decode p with Some x => Some (inl x) | _ => None end
      | p~1 => match decode p with Some x => Some (inr x) | _ => None end
      end
  |}.
Next Obligation. now destruct x as [x|y]; simpl; rewrite decode_encode. Qed.

(** ** Products *)
Fixpoint prod_encode_fst (p : positive) : positive :=
  match p with
  | 1 => 1
  | p~0 => (prod_encode_fst p)~0~0
  | p~1 => (prod_encode_fst p)~0~1
  end.
Fixpoint prod_encode_snd (p : positive) : positive :=
  match p with
  | 1 => 1~0
  | p~0 => (prod_encode_snd p)~0~0
  | p~1 => (prod_encode_snd p)~1~0
  end.
Fixpoint prod_encode (p q : positive) : positive :=
  match p, q with
  | 1, 1 => 1~1
  | p~0, 1 => (prod_encode_fst p)~1~0
  | p~1, 1 => (prod_encode_fst p)~1~1
  | 1, q~0 => (prod_encode_snd q)~0~1
  | 1, q~1 => (prod_encode_snd q)~1~1
  | p~0, q~0 => (prod_encode p q)~0~0
  | p~0, q~1 => (prod_encode p q)~1~0
  | p~1, q~0 => (prod_encode p q)~0~1
  | p~1, q~1 => (prod_encode p q)~1~1
  end.
Fixpoint prod_decode_fst (p : positive) : option positive :=
  match p with
  | p~0~0 => match prod_decode_fst p with Some q => Some q~0 | _ => None end
  | p~0~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end
  | p~1~0 => match prod_decode_fst p with Some q => Some q~0 | _ => None end
  | p~1~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end
  | 1~0 => None
  | 1~1 => Some 1
  | 1 => Some 1
  end.
Fixpoint prod_decode_snd (p : positive) : option positive :=
  match p with
  | p~0~0 => match prod_decode_snd p with Some q => Some q~0 | _ => None end
  | p~0~1 => match prod_decode_snd p with Some q => Some q~0 | _ => None end
  | p~1~0 => Some match prod_decode_snd p with Some q => q~1 | _ => 1 end
  | p~1~1 => Some match prod_decode_snd p with Some q => q~1 | _ => 1 end
  | 1~0 => Some 1
  | 1~1 => Some 1
  | 1 => None
  end.

Lemma prod_decode_encode_fst p q : prod_decode_fst (prod_encode p q) = Some p.
Proof.
  assert (∀ p, prod_decode_fst (prod_encode_fst p) = Some p).
  { intros p'. induction p'; simpl; auto; now rewrite IHp'. }
  assert (∀ p, prod_decode_fst (prod_encode_snd p) = None).
  { intros p'. induction p'; simpl; auto; now rewrite IHp'. }
  revert q. induction p; intros [?|?|]; simpl;
  repeat match goal with
  | _ => solve [auto]
  | H : _ |- _ => rewrite H
  end.
Qed.
Lemma prod_decode_encode_snd p q : prod_decode_snd (prod_encode p q) = Some q.
Proof.
  assert (∀ p, prod_decode_snd (prod_encode_snd p) = Some p).
  { intros p'. induction p'; simpl; auto; now rewrite IHp'. }
  assert (∀ p, prod_decode_snd (prod_encode_fst p) = None).
  { intros p'. induction p'; simpl; auto; now rewrite IHp'. }
  revert q. induction p; intros [?|?|]; simpl;
  repeat match goal with
  | _ => solve [auto]
  | H : _ |- _ => rewrite H
  end.
Qed.
Global Program Instance prod_countable `{Countable A} `{Countable B} :
  Countable (A * B)%type := {|
    encode xy := prod_encode (encode (fst xy)) (encode (snd xy));
    decode p :=
      match prod_decode_fst p with
      | Some x => match decode x with Some x =>
        match prod_decode_snd p with
        | Some y => match decode y with Some y => Some (x, y) | _ => None end
        | _ => None
        end | _ => None end
      | _ => None
      end
  |}.
Next Obligation.
  simpl.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd; simpl.
  now rewrite !decode_encode.
Qed.

(** Since [positive] represents lists of bits, we definempty list operations
on it. These operations are in reverse, as positives are treated as snoc
lists instead of cons lists. *)
#[local] Fixpoint app (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => (app p1 p2)~0
  | p2~1 => (app p1 p2)~1
  end.

Module Import app_notations.
  Infix "++" := app : positive_scope.
  Notation "(++)" := app (only parsing) : positive_scope.
  Notation "( p ++.)" := (app p) (only parsing) : positive_scope.
  Notation "(.++ q )" := (λ p, app p q) (only parsing) : positive_scope.
End app_notations.

#[local] Fixpoint reverse_go (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => reverse_go (p1~0) p2
  | p2~1 => reverse_go (p1~1) p2
  end.
#[local] Definition reverse : positive → positive := reverse_go 1.

#[local] Lemma app_1_l p : 1 ++ p = p.
Proof. induction p; simpl; f_equal; auto. Qed.
#[local] Lemma app_1_r p : p ++ 1 = p.
Proof. induction p; simpl; f_equal; auto. Qed.
#[local] Lemma app_assoc p q r : p ++ q ++ r = (p ++ q) ++ r.
Proof. induction r; simpl; f_equal; auto. Qed.
#[local] Lemma app_inj p : ∀ x y, app x p = app y p → x = y.
Proof. induction p; simpl; auto; intros; apply IHp; congruence. Qed.

#[local] Lemma reverse_go_app p1 p2 p3 :
  reverse_go p1 (p2 ++ p3) = reverse_go p1 p3 ++ reverse_go 1 p2.
Proof.
  revert p3 p1 p2.
  cut (∀ p1 p2 p3, reverse_go (p2 ++ p3) p1 = p2 ++ reverse_go p3 p1).
  { now intros go p3; induction p3; intros p1 p2; simpl; auto; rewrite <-?go. }
  intros p1; induction p1 as [p1 IH|p1 IH|]; intros p2 p3; simpl; auto.
  - apply (IH _ (_~1)).
  - apply (IH _ (_~0)).
Qed.
#[local] Lemma reverse_app p1 p2 : reverse (p1 ++ p2) = reverse p2 ++ reverse p1.
Proof. unfold reverse. now rewrite reverse_go_app. Qed.
#[local] Lemma reverse_xO p : reverse (p~0) = (1~0) ++ reverse p.
Proof. apply (reverse_app p (1~0)). Qed.
#[local] Lemma reverse_xI p : reverse (p~1) = (1~1) ++ reverse p.
Proof. apply (reverse_app p (1~1)). Qed.

#[local] Lemma reverse_involutive p : reverse (reverse p) = p.
Proof.
  induction p as [p IH|p IH|]; simpl.
  - now rewrite reverse_xI, reverse_app, IH.
  - now rewrite reverse_xO, reverse_app, IH.
  - reflexivity.
Qed.

#[local] Lemma reverse_inj : ∀ x y, reverse x = reverse y → x = y.
Proof.
  intros p q eq.
  rewrite <-(reverse_involutive p).
  rewrite <-(reverse_involutive q).
  now rewrite eq.
Qed.

#[local] Fixpoint length (p : positive) : nat :=
  match p with 1 => 0%nat | p~0 | p~1 => S (length p) end.
#[local] Lemma length_app p1 p2 : length (p1 ++ p2) = (length p2 + length p1)%nat.
Proof. now induction p2; simpl; f_equal. Qed.

#[local] Lemma lt_sum (x y : positive) : x < y ↔ ∃ z, y = x + z.
Proof.
  split.
  - exists (y - x)%positive. symmetry. apply Pplus_minus. lia.
  - intros [z ->]. lia.
Qed.

(** Duplicate the bits of a positive, i.e. 1~0~1 -> 1~0~0~1~1 and
    1~1~0~0 -> 1~1~1~0~0~0~0 *)
#[local] Fixpoint dup (p : positive) : positive :=
  match p with
  | 1 => 1
  | p'~0 => (dup p')~0~0
  | p'~1 => (dup p')~1~1
  end.

#[local] Lemma dup_app p q :
  dup (p ++ q) = dup p ++ dup q.
Proof.
  revert p.
  induction q as [p IH|p IH|]; intros q; simpl.
  - now rewrite IH.
  - now rewrite IH.
  - reflexivity.
Qed.

#[local] Lemma dup_suffix_eq p q s1 s2 :
  s1~1~0 ++ dup p = s2~1~0 ++ dup q → p = q.
Proof.
  revert q.
  induction p as [p IH|p IH|]; intros [q|q|] eq; simpl in *; try congruence.
  - f_equal. apply IH. congruence.
  - f_equal. apply IH. congruence.
Qed.

#[local] Lemma dup_inj : ∀ x y, dup x = dup y → x = y.
Proof.
  intros p q eq.
  apply (dup_suffix_eq _ _ 1 1).
  now rewrite eq.
Qed.

#[local] Lemma reverse_dup p :
  reverse (dup p) = dup (reverse p).
Proof.
  induction p as [p IH|p IH|]; simpl.
  - rewrite 3!reverse_xI.
    rewrite app_assoc.
    rewrite IH.
    rewrite dup_app.
    reflexivity.
  - rewrite 3!reverse_xO.
    rewrite app_assoc.
    rewrite IH.
    rewrite dup_app.
    reflexivity.
  - reflexivity.
Qed.

(** These next functions allow to efficiently encode lists of positives (bit
strings) into a single positive and go in the other direction as well. This is
for example used for the countable instance of lists and in namespaces.
 The main functions are [positives_flatten] and [positives_unflatten]. *)
Fixpoint positives_flatten_go (xs : list positive) (acc : positive) : positive :=
  match xs with
  | [] => acc
  | x :: xs => positives_flatten_go xs (acc~1~0 ++ reverse (dup x))
  end.

(** Flatten a list of positives into a single positive by duplicating the bits
of each element, so that:

- [0 -> 00]
- [1 -> 11]

and then separating each element with [10]. *)
Definition positives_flatten (xs : list positive) : positive :=
  positives_flatten_go xs 1.

Fixpoint positives_unflatten_go
        (p : positive)
        (acc_xs : list positive)
        (acc_elm : positive)
  : option (list positive) :=
  match p with
  | 1 => Some acc_xs
  | p'~0~0 => positives_unflatten_go p' acc_xs (acc_elm~0)
  | p'~1~1 => positives_unflatten_go p' acc_xs (acc_elm~1)
  | p'~1~0 => positives_unflatten_go p' (acc_elm :: acc_xs) 1
  | _ => None
  end%positive.

(** Unflatten a positive into a list of positives, assuming the encoding
used by [positives_flatten]. *)
Definition positives_unflatten (p : positive) : option (list positive) :=
  positives_unflatten_go p [] 1.

(** Lemmas about [positives_flatten] and [positives_unflatten]. *)
Section positives_flatten_unflatten.
  Lemma positives_flatten_go_app xs acc :
    positives_flatten_go xs acc = acc ++ positives_flatten_go xs 1.
  Proof.
    revert acc.
    induction xs as [|x xs IH]; intros acc; simpl.
    - reflexivity.
    - rewrite IH.
      rewrite (IH (6 ++ _)).
      rewrite 2!app_assoc.
      reflexivity.
  Qed.

  Lemma positives_unflatten_go_app p suffix xs acc :
    positives_unflatten_go (suffix ++ reverse (dup p)) xs acc =
    positives_unflatten_go suffix xs (acc ++ p).
  Proof.
    revert suffix acc.
    induction p as [p IH|p IH|]; intros acc suffix; simpl.
    - rewrite 2!reverse_xI.
      rewrite 2!app_assoc.
      rewrite IH.
      reflexivity.
    - rewrite 2!reverse_xO.
      rewrite 2!app_assoc.
      rewrite IH.
      reflexivity.
    - reflexivity.
  Qed.

  Lemma positives_unflatten_flatten_go suffix xs acc :
    positives_unflatten_go (suffix ++ positives_flatten_go xs 1) acc 1 =
    positives_unflatten_go suffix (xs ++ acc) 1.
  Proof.
    revert suffix acc.
    induction xs as [|x xs IH]; intros suffix acc; simpl.
    - reflexivity.
    - rewrite positives_flatten_go_app.
      rewrite app_assoc.
      rewrite IH.
      rewrite app_assoc.
      rewrite positives_unflatten_go_app.
      simpl.
      rewrite app_1_l.
      reflexivity.
  Qed.

  Lemma positives_unflatten_flatten xs :
    positives_unflatten (positives_flatten xs) = Some xs.
  Proof.
    unfold positives_flatten, positives_unflatten.
    replace (positives_flatten_go xs 1)
      with (1 ++ positives_flatten_go xs 1)
      by apply (app_1_l).
    rewrite positives_unflatten_flatten_go.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  Qed.

  Lemma positives_flatten_app xs ys :
    positives_flatten (xs ++ ys) = positives_flatten xs ++ positives_flatten ys.
  Proof.
    unfold positives_flatten.
    revert ys.
    induction xs as [|x xs IH]; intros ys; simpl.
    - rewrite app_1_l.
      reflexivity.
    - rewrite positives_flatten_go_app, (positives_flatten_go_app xs).
      rewrite IH.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Lemma positives_flatten_cons x xs :
    positives_flatten (x :: xs)
    = 1~1~0 ++ reverse (dup x) ++ positives_flatten xs.
  Proof.
    change (x :: xs) with ([x] ++ xs)%list.
    rewrite positives_flatten_app.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Lemma positives_flatten_suffix (l k : list positive) :
    (∃ l', k = l' ++ l)%list → ∃ q, positives_flatten k = q ++ positives_flatten l.
  Proof.
    intros [l' ->].
    exists (positives_flatten l').
    apply positives_flatten_app.
  Qed.

  Lemma positives_flatten_suffix_eq p1 p2 (xs ys : list positive) :
    List.length xs = List.length ys →
    p1 ++ positives_flatten xs = p2 ++ positives_flatten ys →
    xs = ys.
  Proof.
    revert p1 p2 ys; induction xs as [|x xs IH];
      intros p1 p2 [|y ys] ?; simpl in *; auto; try congruence.
    rewrite !positives_flatten_cons, !app_assoc; intros Hl.
    assert (xs = ys) as <- by eauto; clear IH; f_equal.
    apply app_inj in Hl.
    rewrite 2!reverse_dup in Hl.
    apply (dup_suffix_eq _ _ p1 p2) in Hl.
    now apply reverse_inj.
  Qed.
End positives_flatten_unflatten.

#[local] Definition mapM_go {A B} (f : A → option B) : list B → list A → option (list B) :=
  fix go acc l :=
  match l with
  | [] => Some (rev_append acc [])
  | hd :: tl =>
    match f hd with
    | Some hd => go (hd :: acc) tl
    | None => None
    end
  end.

Lemma mapM_go_spec {A B} (f : A → option B) :
  ∀ l acc, mapM_go f acc l =
    match mapM_go f [] l with
    | Some l' => Some (rev acc ++ l')
    | None => None
    end%list.
Proof.
  induction l; simpl; auto.
  - intros. now rewrite <- rev_alt, app_nil_r.
  - intros. destruct (f a); auto.
    rewrite IHl, (IHl [b]). simpl.
    destruct (mapM_go f [] l); auto.
    now rewrite <- List.app_assoc.
Qed.

Definition mapM {A B} (f : A → option B) : list A → option (list B) :=
  mapM_go f []
.

Lemma mapM_spec {A B} (f : A → option B) :
  ∀ n (v : vect A n),
    match mapM f (vect_to_list v) with
    | Some l' =>
      match list_to_vect n l' with
      | Some v' => ∀ i, f (vect_nth v i) = Some (vect_nth v' i)
      | None => False
      end
    | None => ∃ i, f (vect_nth v i) = None
    end.
Proof.
  induction n; simpl. destruct i.
  intros (hd & tl).
  unfold vect_to_list. simpl.
  unfold mapM. simpl.
  destruct (f hd) eqn:HD. 2: exists thisone; eauto.
  rewrite mapM_go_spec. simpl.
  change (mapM_go f _ _) with (mapM f (vect_to_list tl)).
  specialize (IHn tl). destruct (mapM f _) eqn:TL.
  2: des; exists (anotherone i); eauto.
  destruct (list_to_vect n l); try contradiction.
  intros [|i]; simpl; eauto.
Qed.

(** ** Lists *)
Global Program Instance list_countable `{Countable A} : Countable (list A) :=
  {| encode xs := positives_flatten (map encode xs);
     decode p := match positives_unflatten p with
                 | Some positives => mapM decode positives
                 | None => None
                 end; |}.
Next Obligation.
  rewrite positives_unflatten_flatten.
  simpl. unfold mapM.
  induction x; simpl; auto.
  now rewrite decode_encode, mapM_go_spec, IHx.
Qed.

(** ** Vectors *)
Global Program Instance vect_countable `{Countable A} n : Countable (vect A n) :=
  {| encode v := encode (vect_to_list v);
     decode p := match decode p : option (list A) with
                 | Some l => list_to_vect n l
                 | None => None
                 end; |}.
Next Obligation.
  now rewrite decode_encode, list_to_vect_to_list.
Qed.

(** dependent lists *)
Global Program Instance sigT_countable `{Countable A} (B : A → Type)
    `{!∀ x, EqDec (B x), !∀ x, Countable (B x)} : Countable (sigT B) :=
  {| encode xy := prod_encode (encode (projT1 xy)) (encode (projT2 xy));
     decode p :=
       match prod_decode_fst p with
       | Some x => match decode x with Some x =>
         match prod_decode_snd p with
         | Some y => match decode y with Some y => Some (existT _ x y) | _ => None end
         | _ => None
         end | _ => None end
       | _ => None
       end; |}.
Next Obligation.
  simpl.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd; simpl.
  now repeat (rewrite decode_encode; simpl).
Qed.

Global Program Instance context_countable `{Countable A} (B : A → Type)
    `{!∀ x, EqDec (B x), !∀ x, Countable (B x)} l : Countable (context B l) :=
  {| encode ctx := encode (ctx_to_list ctx);
     decode p :=
       match decode p : option (list {a : A & B a}) with
       | Some l' =>
         match eq_dec (map (projT1 (P:=B)) l') l with
         | left EQ => Some (rew [context B] EQ in list_to_ctx l')
         | right _ => None
         end
       | None => None
       end; |}.
Next Obligation.
  rewrite decode_encode; simpl.
  destruct (list_eq_dec _ _ _).
  - f_equal. erewrite (UIP_dec e). apply list_to_ctx_to_list.
  - exfalso. apply n. apply list_to_ctx_cast.
Qed.

(** ** Numbers *)
Global Instance pos_countable : Countable positive :=
  {| encode := id; decode := Some; decode_encode x := eq_refl |}.
Global Program Instance N_countable : Countable N := {|
  encode x := match x with N0 => 1 | Npos p => Pos.succ p end;
  decode p := if eq_dec p 1 then Some 0%N else Some (Npos (Pos.pred p))
|}.
Next Obligation.
  destruct x as [|p]; simpl; [auto|].
  match goal with |- (if ?f ?x 1 then _ else _) = _ => change (f x 1) with (eq_dec x 1) end.
  destruct (eq_dec _ _); [lia|].
  now rewrite Pos.pred_succ.
Qed.
Global Program Instance Z_countable : Countable Z := {|
  encode x := match x with Z0 => 1 | Zpos p => p~0 | Zneg p => p~1 end;
  decode p := Some match p with 1 => Z0 | p~0 => Zpos p | p~1 => Zneg p end
|}.
Next Obligation. now destruct x as [|p|p]. Qed.
Global Program Instance nat_countable : Countable nat :=
  {| encode x := encode (N.of_nat x); decode p := match decode p with Some n => Some (N.to_nat n) | None => None end |}.
Next Obligation.
  now rewrite decode_encode, Nat2N.id.
Qed.

Global Instance index_countable n : Countable (Vect.index n) :=
  inj_countable index_to_nat (index_of_nat n) index_of_nat_to_nat
.

Local Close Scope positive.

Inductive gen_tree (T : Type) : Type :=
  | GenLeaf : T → gen_tree T
  | GenNode : nat → list (gen_tree T) → gen_tree T.
Global Arguments GenLeaf {_} _ : assert.
Global Arguments GenNode {_} _ _ : assert.

Global Instance gen_tree_dec `{EqDec T} : EqDec (gen_tree T).
Proof.
  constructor. refine (fix go t1 t2 :=
  let eq_dec_tree := {| eq_dec := go |} in
  match t1, t2 with
  | GenLeaf x1, GenLeaf x2 =>
    if eq_dec x1 x2 then left _ else right _
  | GenNode n1 ts1, GenNode n2 ts2 =>
    if eq_dec n1 n2 then
      if eq_dec ts1 ts2 then left _ else right _
    else right _
  | _, _ => right _
  end); abstract congruence.
Defined.

Definition list_bind {A B} (f : A → list B) :=
  fix go (l : list A) := match l with [] => [] | x :: l => f x ++ go l end%list
.

Fixpoint gen_tree_to_list {T} (t : gen_tree T) : list (nat * nat + T) :=
  match t with
  | GenLeaf x => [inr x]
  | GenNode n ts => (list_bind gen_tree_to_list ts) ++ [inl (List.length ts, n)]
  end%list.

Fixpoint gen_tree_of_list {T}
    (k : list (gen_tree T)) (l : list (nat * nat + T)) : option (gen_tree T) :=
  match l with
  | [] => head k
  | inr x :: l => gen_tree_of_list (GenLeaf x :: k) l
  | inl (len,n) :: l =>
     gen_tree_of_list (GenNode n (rev (firstn len k)) :: skipn len k) l
  end.

Lemma gen_tree_of_to_list {T} k l (t : gen_tree T) :
  gen_tree_of_list k (gen_tree_to_list t ++ l) = gen_tree_of_list (t :: k) l.
Proof.
  revert t k l; fix FIX 1; intros [|n ts] k l; simpl; auto.
  transitivity (gen_tree_of_list (rev ts ++ k) ([inl (List.length ts, n)] ++ l)).
  - rewrite <-List.app_assoc. revert k. generalize ([inl (List.length ts, n)] ++ l).
    induction ts as [|t ts'' IH]; intros k ts'''; simpl; auto.
    change [t] with (rev [t]). rewrite <- rev_app_distr.
    rewrite <- List.app_assoc, FIX; simpl.
    now rewrite <- List.app_assoc.
  - simpl. replace (List.length ts) with (List.length (rev ts)) by apply length_rev.
    rewrite firstn_app, skipn_app, Nat.sub_diag, firstn_0, app_nil_r; auto.
    now rewrite firstn_all, skipn_all, rev_involutive.
Qed.

Global Program Instance gen_tree_countable `{Countable T} : Countable (gen_tree T) :=
  inj_countable gen_tree_to_list (gen_tree_of_list []) _.
Next Obligation.
  now rewrite <- (app_nil_r (gen_tree_to_list _)), gen_tree_of_to_list.
Qed.

(** Generic extensional maps on countable keys *)
Record gmap_key K `{Countable K} (q : positive) :=
  GMapKey { _ : match decode q with Some q => Some (encode (A:=K) q) | None => None end = Some q }.
Add Printing Constructor gmap_key.
Global Arguments GMapKey {_ _ _ _} _.

Lemma gmap_key_encode `{Countable K} (k : K) : gmap_key K (encode k).
Proof. constructor. now rewrite decode_encode. Qed.
Lemma gmap_key_pi `{Countable K} q : ∀ pf pf' : gmap_key K q, pf = pf'.
Proof. intros [?] [?]. f_equal. apply UIP_dec. Qed.

Record gmap_ne K `{Countable K} A := GMap { gmap_car : pmap' A (gmap_key K) }.
Add Printing Constructor gmap_ne.
Global Arguments GMap {_ _ _ _} _.
Global Arguments gmap_car {_ _ _ _} _.

Variant gmap `{Countable K} {A} := empty | nempty (m : gmap_ne K A).
Arguments gmap K {_ _} A.

Record gmap_val K `{Countable K} (V : K → Type) (q : positive) : Type :=
  GMapVal { _ : match decode q : option K with Some k => V k | None => False end }.
Add Printing Constructor gmap_val.
Global Arguments GMapVal {_ _ _ _ _} _.

Definition proj_gmap_val `{Countable K} {V k} (v : gmap_val K V (encode k)) : V k.
Proof.
  refine match v with
  | GMapVal x => _
  end.
  rewrite decode_encode in x. assumption.
Defined.

Definition GMapVal' `{Countable K} {V k} (v : V k) : gmap_val K V (encode k).
Proof.
  refine (GMapVal _).
  rewrite decode_encode. assumption.
Defined.

Lemma proj_gmap_val_GMapVal' `{Countable K} {V k} (v : V k) :
  proj_gmap_val (GMapVal' v) = v.
Proof.
  unfold proj_gmap_val, GMapVal'.
  generalize (decode_encode k). destruct (decode (encode k)).
  - inversion e; subst.
    erewrite (UIP_dec e). instantiate (1 := eq_refl). auto.
  - inversion e.
Qed.

Lemma GMapVal'_proj_gmap_val `{Countable K} {V k} (v : gmap_val K V (encode k)) :
  GMapVal' (proj_gmap_val v) = v.
Proof.
  unfold proj_gmap_val, GMapVal'. destruct v as [v]. f_equal. revert v.
  generalize (decode_encode k). destruct (decode (encode k)).
  - inversion e; subst. intros.
    erewrite (UIP_dec e). instantiate (1 := eq_refl). auto.
  - inversion e.
Qed.

Record gmap_dep_ne K `{Countable K} V := GMapDep { gmap_dep_car : pmap_dep' (gmap_key K) (gmap_val K V) }.
Add Printing Constructor gmap_dep_ne.
Global Arguments GMapDep {_ _ _ _} _.
Global Arguments gmap_dep_car {_ _ _ _} _.

Variant gmap_dep `{Countable K} {V} := empty_dep | nempty_dep (m : gmap_dep_ne K V).
Arguments gmap_dep K {_ _} V.

Section map_ok.
  Context `{Ok : Countable K}.

  Definition get' {V} (m : gmap_ne K V) k : option V := get' m.(gmap_car) (encode k).
  Definition get {V} (m : gmap K V) k : option V :=
    match m with empty => None | nempty m => get' m k end.

  Definition put0 {V} k v : gmap_ne K V :=
    GMap (put0 v (encode k) (gmap_key_encode k)).
  Definition put' {V} (m : gmap K V) k v : gmap_ne K V :=
    match m with
    | empty => put0 k v
    | nempty m => GMap (put' v m.(gmap_car) (encode k) (gmap_key_encode k))
    end.
  Definition put {V} (m : gmap K V) k v : gmap K V := nempty (put' m k v).

  Definition alter' {V} (m : gmap_ne K V) k f : gmap K V :=
    match alter' f m.(gmap_car) (encode k) (gmap_key_encode k) with
    | Some m => nempty (GMap m)
    | None => empty
    end.
  Definition alter {V} (m : gmap K V) k f : gmap K V :=
    match m with
    | nempty m => alter' m k f
    | empty =>
      match f None with
      | Some v => nempty (put0 k v)
      | None => empty
      end
    end.

  Definition remove' {V} (m : gmap_ne K V) k : gmap K V :=
    match remove' (encode k) m.(gmap_car) with
    | Some m => nempty (GMap m)
    | None => empty
    end.
  Definition remove {V} (m : gmap K V) k : gmap K V :=
    match m with empty => empty | nempty m => remove' m k end.

  Definition fold' {R V} (f : R → K → V → R) init (m : gmap_ne K V) : R :=
    fold' (fun acc k v =>
      match decode k with
      | Some k => f acc k v
      | None => acc
      end) init m.(gmap_car)
  .
  Definition fold {R V} (f : R → K → V -> R) init (m : gmap K V) : R :=
    match m with empty => init | nempty m => fold' f init m end.

  Lemma get_empty {V} : forall i, get (V := V) empty i = None.
  Proof. intros. auto. Qed.
  Lemma get_nonempty {V} m : exists k, get' (V := V) m k <> None.
  Proof.
    destruct m.
    specialize (pmap'_nonempty gmap_car0).
    intros (k & SOME & [KEY]).
    destruct (decode k) as [q|]; [|discriminate].
    exists q. unfold get'. simpl. apply Some_inj in KEY.
    rewrite KEY. auto.
  Qed.

  Lemma get'_put0_same {V} i (x : V) :
    get' (put0 i x) i = Some x.
  Proof. unfold get', put0. apply get'_put0_same. Qed.
  Lemma get'_put'_same {V} (m : gmap K V) :
    forall i x, get' (put' m i x) i = Some x.
  Proof.
    unfold get', put'. destruct m; intros.
    apply get'_put0_same. apply get'_put'_same.
  Qed.
  Lemma get_put_same {V} (m : gmap K V) :
    forall i x, get (put m i x) i = Some x.
  Proof. apply get'_put'_same. Qed.

  Lemma get'_put0_diff {V} i j (x : V) :
    i <> j -> get' (put0 j x) i = None.
  Proof.
    unfold get', put0. intros. apply get'_put0_diff.
    intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in *. congruence.
  Qed.
  Lemma get'_put'_diff {V} (m : gmap K V) :
    forall i j (x : V), i <> j -> get' (put' m j x) i = get m i.
  Proof.
    destruct m; simpl. apply get'_put0_diff.
    unfold get'. intros. simpl. apply get'_put'_diff.
    intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in *. congruence.
  Qed.
  Lemma get_put_diff {V} (m : gmap K V) :
    forall i j x, i <> j -> get (put m j x) i = get m i.
  Proof. apply get'_put'_diff. Qed.

  Lemma get_alter'_same {V} (m : gmap_ne K V) :
    forall i f, get (alter' m i f) i = f (get' m i).
  Proof.
    intros. unfold get'.
    erewrite <- get_alter'_same. instantiate (1 := gmap_key_encode i).
    unfold get, alter'. destruct (PMap.alter' _ _ _ _); auto.
  Qed.
  Lemma get_alter_same {V} (m : gmap K V) :
    forall i f, get (alter m i f) i = f (get m i).
  Proof.
    intros. destruct m; simpl.
    destruct (f None); auto.
    apply get'_put0_same.
    apply get_alter'_same.
  Qed.
  Lemma get_alter'_diff {V} (m : gmap_ne K V) :
    forall i j f, i <> j -> get (alter' m j f) i = get' m i.
  Proof.
    intros. unfold get'.
    erewrite <- get_alter'_diff. 2: instantiate (1 := encode j).
    instantiate (1 := gmap_key_encode j). instantiate (1 := f).
    unfold get, alter'.
    destruct (PMap.alter' _ _ _ _); auto.
    intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in *. congruence.
  Qed.
  Lemma get_alter_diff {V} (m : gmap K V) :
    forall i j f, i <> j -> get (alter m j f) i = get m i.
  Proof.
    intros. destruct m; simpl.
    destruct (f None); auto.
    apply get'_put0_diff; auto.
    apply get_alter'_diff; auto.
  Qed.

  Lemma get_remove'_same {V} (m : gmap_ne K V) :
    forall i, get (remove' m i) i = None.
  Proof.
    intros. erewrite <- get_remove'_same.
    instantiate (1 := encode i). instantiate (1 := gmap_car m).
    unfold remove'. destruct (PMap.remove' _ _); auto.
  Qed.
  Lemma get_remove_same {V} (m : gmap K V) :
    forall i, get (remove m i) i = None.
  Proof.
    intros. destruct m; simpl; auto.
    apply get_remove'_same.
  Qed.

  Lemma get_remove'_diff {V} (m : gmap_ne K V) :
    forall i j, i <> j -> get (remove' m j) i = get' m i.
  Proof.
    intros. unfold get'. erewrite <- get_remove'_diff.
    instantiate (1 := encode j).
    unfold remove'. destruct (PMap.remove' _ _); auto.
    intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in EQ. apply Some_inj in EQ. auto.
  Qed.
  Lemma get_remove_diff {V} (m : gmap K V) :
    forall i j, i <> j -> get (remove m j) i = get m i.
  Proof.
    intros. destruct m; auto. simpl. apply get_remove'_diff; auto.
  Qed.

  Lemma fold'_spec {R V} (Q : gmap K V -> R -> Prop) f init
    (PEmpty : Q empty init)
    (PNodes : forall i v m r (Hget : get m i = None) (IHfold : Q m r),
       Q (put m i v) (f r i v)) :
    forall m, Q (nempty m) (fold' f init m).
  Proof.
    unfold fold'. intros. destruct m as [m].
    apply fold'_spec with (Q := fun m =>
      match m with Some m => Q (nempty (GMap m)) | None => Q empty end); auto.
    clear m. intros.
    assert (∃ q, i = encode q).
    { destruct k. destruct (decode i); inversion e; subst; eauto. }
    des; subst.
    specialize (PNodes q v
      match m with Some m => nempty (GMap m) | None => empty end r).
    rewrite decode_encode.
    exploit PNodes; destruct m; auto.
    all: erewrite (gmap_key_pi _ k); eauto.
  Qed.
  Lemma fold_spec {R V} (Q : gmap K V -> R -> Prop) f init
    (PEmpty : Q empty init)
    (PNodes : forall i v m r (Hget : get m i = None) (IHfold : Q m r),
       Q (put m i v) (f r i v)) :
    forall m, Q m (fold f init m).
  Proof.
    intros. destruct m; simpl; auto. now apply fold'_spec.
  Qed.

  Lemma fold'_parametricity {A B V : Type} (R : A -> B -> Prop)
    (fa : A -> K -> V -> A) (fb : B -> K -> V -> B)
    (RApp : forall a b i v (REL : R a b), R (fa a i v) (fb b i v)) :
    forall (m : gmap_ne K V) a0 b0 (RInit : R a0 b0),
      R (fold' fa a0 m) (fold' fb b0 m).
  Proof.
    intros. unfold fold'.
    apply PMap.fold'_parametricity; auto.
    intros. destruct (decode i); auto.
  Qed.
  Lemma fold_parametricity {A B V : Type} (R : A -> B -> Prop)
    (fa : A -> K -> V -> A) (fb : B -> K -> V -> B)
    (RApp : forall a b i v (REL : R a b), R (fa a i v) (fb b i v)) :
    forall (m : gmap K V) a0 b0 (RInit : R a0 b0),
      R (fold fa a0 m) (fold fb b0 m).
  Proof.
    intros. destruct m; simpl; auto. apply fold'_parametricity; auto.
  Qed.

  Lemma gmap_ne_ext {V} (m1 : gmap_ne K V) :
    forall m2 (EQ : forall k, get' m1 k = get' m2 k),
      m1 = m2.
  Proof.
    destruct m1 as [m1], m2 as [m2].
    unfold get'. intros. f_equal. apply pmap'_ext.
    apply gmap_key_pi.
    intros ? pf. simpl in *.
    assert (∃ q, k = encode q).
    { destruct pf. destruct (decode k); inversion e; subst; eauto. }
    des; subst. auto.
  Qed.
  Lemma gmap_ext {V} (m1 : gmap K V) :
    forall m2 (EQ : forall k, get m1 k = get m2 k),
      m1 = m2.
  Proof.
    destruct m1, m2; simpl; auto.
    - unfold get'. intros. exfalso.
      unshelve eapply pmap'_contradiction.
      2: exact (gmap_key K). 2: exact (gmap_car m).
      intros k pf.
      assert (∃ q, k = encode q).
      { destruct pf. destruct (decode k); inversion e; subst; eauto. }
      des; subst. auto.
    - unfold get'. intros. exfalso.
      unshelve eapply pmap'_contradiction.
      2: exact (gmap_key K). 2: exact (gmap_car m).
      intros k pf.
      assert (∃ q, k = encode q).
      { destruct pf. destruct (decode k); inversion e; subst; eauto. }
      des; subst. auto.
    - intros. f_equal. apply gmap_ne_ext; auto.
  Qed.

  Definition list_to_map {V} (l : list (K * V)) :=
    fold_right (fun '(k, v) m => put m k v) empty l
  .
  Definition map_to_list {V} (m : gmap K V) :=
    fold (fun l k v => (k, v) :: l) [] m
  .

  Lemma map_to_list_spec {V} (m : gmap K V) :
    NoDup (map fst (map_to_list m)) ∧ (∀ i x, In (i, x) (map_to_list m) ↔ get m i = Some x).
  Proof.
    unfold map_to_list. eapply fold_spec.
    - split. constructor. setoid_rewrite get_empty.
      simpl. intuition congruence.
    - intros. clear m. rename m0 into m.
      destruct IHfold as (NODUP & IH). cbn [map fst].
      split.
      + rewrite NoDup_cons_iff. split; auto.
        intro IN.
        rewrite in_map_iff in IN.
        des; subst. destruct x as (i & x); simpl in *.
        rewrite IH in *. congruence.
      + intros j x. destruct (eq_dec i j); subst.
        rewrite get_put_same. cbn [In].
        split; intro EQ.
        des; try congruence. rewrite IH in *. congruence.
        left. congruence.
        rewrite get_put_diff; auto. rewrite <- IH.
        cbn [In]. intuition congruence.
  Qed.

  Lemma list_to_map_to_list {V} (m : gmap K V) : list_to_map (map_to_list m) = m.
  Proof.
    apply gmap_ext. intros i.
    specialize (map_to_list_spec m). intros (NODUP & IN).
    destruct (get m i) as [v|] eqn:GET.
    - rewrite <- IN in GET. revert GET NODUP. generalize (map_to_list m).
      clear. intro. revert i.
      induction l; simpl; try contradiction; destruct 1; subst; cbn [fst].
      + rewrite get_put_same. auto.
      + destruct a as (k & v').
        rewrite NoDup_cons_iff. apply (in_map fst) in H0 as IN.
        cbn [fst] in *.
        intros. des.
        destruct (eq_dec k i); subst. contradiction.
        rewrite get_put_diff by auto. eauto.
    - assert (∀ x, ¬ In (i, x) (map_to_list m)) as HINT.
      { intro. rewrite IN. intro. congruence. }
      revert HINT. generalize (map_to_list m). clear. intro. revert i.
      induction l; simpl.
      + auto.
      + destruct a as (k & v). intros.
        destruct (eq_dec i k); subst.
        1: specialize (HINT v); exfalso; eauto.
        rewrite get_put_diff by auto. apply IHl. intuition eauto.
  Qed.
End map_ok.

Global Instance GMapNEEqDec `{Countable K} `{EqDec V} : EqDec (gmap_ne K V).
Proof.
  set (EqDecPMap' := pmap'_eq_dec gmap_key_pi).
  typeclasses eauto.
Defined.
Global Instance GMapEqDec `{Countable K} `{EqDec V} : EqDec (gmap K V) := _.

#[refine, global] Instance GMapNECountable `{Countable K, Countable V} : Countable (gmap_ne K V) :=
{
  encode m := encode (map_to_list (nempty m));
  decode p := match decode p with Some l => match list_to_map l with nempty m => Some m | empty => None end | None => None end;
}.
Proof.
  abstract (intros; now rewrite decode_encode, list_to_map_to_list).
Defined.
Global Program Instance GMapCountable `{Countable K, Countable V} : Countable (gmap K V) :=
{
  encode m := encode (map_to_list m);
  decode p := match decode p with Some l => Some (list_to_map l) | None => None end;
}.
Next Obligation.
  rewrite decode_encode; simpl. now rewrite list_to_map_to_list.
Qed.

Section map_dep_ok.
  Context `{Ok : Countable K}.

  Definition get'_dep {V} (m : gmap_dep_ne K V) k : option (V k) :=
    match PMapDep.get' m.(gmap_dep_car) (encode k) with
    | Some v => Some (proj_gmap_val v)
    | None => None
    end.
  Definition get_dep {V} (m : gmap_dep K V) k : option (V k) :=
    match m with empty_dep => None | nempty_dep m => get'_dep m k end.

  Definition put0_dep {V} k (v : V k) : gmap_dep_ne K V :=
    GMapDep (PMapDep.put0 (encode k) (gmap_key_encode k) (GMapVal' v))
  .
  Definition put'_dep {V} (m : gmap_dep K V) k (v : V k) : gmap_dep_ne K V :=
    match m with
    | empty_dep => put0_dep k v
    | nempty_dep m =>
      GMapDep (PMapDep.put' m.(gmap_dep_car) (encode k) (gmap_key_encode k) (GMapVal' v))
    end.
  Definition put_dep {V} (m : gmap_dep K V) k (v : V k) : gmap_dep K V :=
    nempty_dep (put'_dep m k v)
  .

  Definition alter'_dep {V} (m : gmap_dep_ne K V) k (f : option (V k) → option (V k)) : gmap_dep K V :=
    match PMapDep.alter' m.(gmap_dep_car) (encode k) (gmap_key_encode k)
      (fun o =>
         let o' := match o with Some v => Some (proj_gmap_val v) | None => None end in
         match f o' with
         | Some v' => Some (GMapVal' v')
         | None => None
         end)
    with
    | Some m => nempty_dep (GMapDep m)
    | None => empty_dep
    end.
  Definition alter_dep {V} (m : gmap_dep K V) k (f : option (V k) → option (V k)) : gmap_dep K V :=
    match m with
    | nempty_dep m => alter'_dep m k f
    | empty_dep =>
      match f None with
      | Some v => nempty_dep (put0_dep k v)
      | None => empty_dep
      end
    end.

  Definition remove'_dep {V} (m : gmap_dep_ne K V) k : gmap_dep K V :=
    match PMapDep.remove' m.(gmap_dep_car) (encode k) with
    | Some m => nempty_dep (GMapDep m)
    | None => empty_dep
    end.
  Definition remove_dep {V} (m : gmap_dep K V) k : gmap_dep K V :=
    match m with nempty_dep m => remove'_dep m k | empty_dep => empty_dep end.

  Definition fold'_dep {R V} (f : R → ∀ k : K, V k → R) (init : R) (m : gmap_dep_ne K V) : R.
  Proof.
    refine (PMapDep.fold' _ init m.(gmap_dep_car)).
    refine (fun acc p v =>
      match decode p as o return
        match o with Some k => V k | None => False end → R
      with
      | Some k => f acc k
      | None => False_rect _
      end match v with GMapVal x => x end).
  Defined.
  Definition fold_dep {R V} (f : R → ∀ k : K, V k → R) (init : R) (m : gmap_dep K V) : R :=
    match m with nempty_dep m => fold'_dep f init m | empty_dep => init end.

  Lemma get_dep_empty_dep {V} : forall i, get_dep (V := V) empty_dep i = None.
  Proof. intros. auto. Qed.
  Lemma get_dep_nonempty {V} m : exists k, get'_dep (V := V) m k <> None.
  Proof.
    destruct m.
    specialize (PMapDep.pmap'_nonempty gmap_dep_car0).
    intros (k & SOME & [KEY]).
    destruct (decode k) as [q|]; [|discriminate].
    exists q. unfold get'_dep. simpl. apply Some_inj in KEY.
    subst. destruct (PMapDep.get' _ _); auto.
    inversion 1.
  Qed.

  Lemma get'_dep_put0_dep_same {V} i (x : V i) :
    get'_dep (put0_dep i x) i = Some x.
  Proof.
    unfold get'_dep, put0_dep. simpl.
    now rewrite PMapDep.get'_put0_same, proj_gmap_val_GMapVal'.
  Qed.
  Lemma get'_dep_put'_dep_same {V} (m : gmap_dep K V) :
    forall i x, get'_dep (put'_dep m i x) i = Some x.
  Proof.
    intros. destruct m; simpl. apply get'_dep_put0_dep_same.
    unfold get'_dep. simpl.
    now rewrite PMapDep.get'_put'_same, proj_gmap_val_GMapVal'.
  Qed.
  Lemma get_dep_put_dep_same {V} (m : gmap_dep K V) :
    forall i x, get_dep (put_dep m i x) i = Some x.
  Proof. apply get'_dep_put'_dep_same. Qed.

  Lemma get'_dep_put0_dep_diff {V} i j (x : V j) :
    i <> j -> get'_dep (put0_dep j x) i = None.
  Proof.
    intros. unfold get'_dep, put0_dep. simpl.
    rewrite PMapDep.get'_put0_diff; auto.
    intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in EQ; inversion EQ; subst; auto.
  Qed.
  Lemma get'_dep_put'_dep_diff {V} (m : gmap_dep K V) :
    forall i j x, i <> j -> get'_dep (put'_dep m j x) i = get_dep m i.
  Proof.
    intros. destruct m; simpl. rewrite get'_dep_put0_dep_diff; auto.
    unfold get'_dep. simpl.
    rewrite PMapDep.get'_put'_diff; auto.
    intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in EQ; inversion EQ; subst; auto.
  Qed.
  Lemma get_dep_put_dep_diff {V} (m : gmap_dep K V) :
    forall i j x, i <> j -> get_dep (put_dep m j x) i = get_dep m i.
  Proof. apply get'_dep_put'_dep_diff. Qed.

  Lemma get_dep_alter'_dep_same {V} (m : gmap_dep_ne K V) :
    forall i f, get_dep (alter'_dep m i f) i = f (get'_dep m i).
  Proof.
    intros. unfold get_dep, alter'_dep.
    remember (PMapDep.alter' _ _ _ _) as p eqn:ALTER.
    apply (f_equal (fun m => PMapDep.get m (encode i))) in ALTER.
    rewrite PMapDep.get_alter'_same in ALTER.
    destruct p; simpl in *.
    unfold get'_dep. simpl. rewrite ALTER.
    destruct (PMapDep.get' _ _).
    destruct (f _); auto. now rewrite proj_gmap_val_GMapVal'.
    destruct (f _); auto. now rewrite proj_gmap_val_GMapVal'.
    unfold get'_dep. destruct (PMapDep.get' _ _).
    destruct (f _); auto. inversion ALTER.
    destruct (f _); auto. inversion ALTER.
  Qed.
  Lemma get_dep_alter_dep_same {V} (m : gmap_dep K V) :
    forall i f, get_dep (alter_dep m i f) i = f (get_dep m i).
  Proof.
    destruct m; simpl. 2: apply get_dep_alter'_dep_same.
    intros. destruct (f _); auto.
    simpl. now rewrite get'_dep_put0_dep_same.
  Qed.

  Lemma get_dep_alter'_dep_diff {V} (m : gmap_dep_ne K V) :
    forall i j f, i <> j -> get_dep (alter'_dep m j f) i = get'_dep m i.
  Proof.
    intros. unfold get_dep, alter'_dep.
    remember (PMapDep.alter' _ _ _ _) as p eqn:ALTER.
    apply (f_equal (fun m => PMapDep.get m (encode i))) in ALTER.
    rewrite PMapDep.get_alter'_diff in ALTER.
    2: { intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in EQ; inversion EQ; subst; auto. }
    destruct p; simpl in *.
    unfold get'_dep. simpl. now rewrite ALTER.
    unfold get'_dep. now rewrite <- ALTER.
  Qed.
  Lemma get_dep_alter_dep_diff {V} (m : gmap_dep K V) :
    forall i j f, i <> j -> get_dep (alter_dep m j f) i = get_dep m i.
  Proof.
    intros. destruct m; simpl. 2: apply get_dep_alter'_dep_diff; auto.
    destruct (f None); simpl; auto.
    apply get'_dep_put0_dep_diff; auto.
  Qed.

  Lemma get_dep_remove'_dep_same {V} (m : gmap_dep_ne K V) :
    forall i, get_dep (remove'_dep m i) i = None.
  Proof.
    intros. unfold remove'_dep, get_dep.
    remember (PMapDep.remove' _ _) as p eqn:REMOVE.
    apply (f_equal (fun m => PMapDep.get m (encode i))) in REMOVE.
    rewrite PMapDep.get_remove'_same in REMOVE.
    destruct p; simpl in *; auto.
    unfold get'_dep. simpl. now rewrite REMOVE.
  Qed.
  Lemma get_dep_remove_dep_same {V} (m : gmap_dep K V) :
    forall i, get_dep (remove_dep m i) i = None.
  Proof.
    intros. destruct m; simpl; auto. apply get_dep_remove'_dep_same.
  Qed.

  Lemma get_dep_remove'_dep_diff {V} (m : gmap_dep_ne K V) :
    forall i j, i <> j -> get_dep (remove'_dep m j) i = get'_dep m i.
  Proof.
    intros. unfold remove'_dep, get_dep.
    remember (PMapDep.remove' _ _) as p eqn:REMOVE.
    apply (f_equal (fun m => PMapDep.get m (encode i))) in REMOVE.
    rewrite PMapDep.get_remove'_diff in REMOVE.
    2: { intro EQ. apply (f_equal decode) in EQ.
    repeat rewrite decode_encode in EQ; inversion EQ; subst; auto. }
    destruct p; simpl in *; auto.
    unfold get'_dep. simpl. now rewrite REMOVE.
    unfold get'_dep. now rewrite <- REMOVE.
  Qed.
  Lemma get_dep_remove_dep_diff {V} (m : gmap_dep K V) :
    forall i j, i <> j -> get_dep (remove_dep m j) i = get_dep m i.
  Proof.
    intros. destruct m; simpl; auto. now apply get_dep_remove'_dep_diff.
  Qed.

  Lemma fold'_dep_spec {R V} (Q : gmap_dep K V -> R -> Prop) f init
    (PEmpty : Q empty_dep init)
    (PNodes : forall i v m r (Hget : get_dep m i = None) (IHfold : Q m r),
       Q (put_dep m i v) (f r i v)) :
    forall m, Q (nempty_dep m) (fold'_dep f init m).
  Proof.
    intros. destruct m as [m]. unfold fold'_dep. simpl.
    apply PMapDep.fold'_spec with (Q := fun m =>
      match m with Some m => Q (nempty_dep (GMapDep m)) | None => Q empty_dep end);
    auto.
    clear m. intros.
    assert (∃ q, i = encode q).
    { destruct k. destruct (decode i); inversion e; subst; eauto. }
    des; subst.
    specialize (PNodes q (proj_gmap_val v)
      match m with Some m => nempty_dep (GMapDep m) | None => empty_dep end r).
    exploit PNodes; eauto.
    destruct m; simpl; auto.
    { unfold get'_dep; simpl in *. now rewrite H0. }
    { destruct m; simpl; auto. }
    match goal with
    | |- Q ?x ?y → Q ?x' ?y' => assert (x = x') as ->
    end.
    { unfold put_dep. f_equal. destruct m; simpl.
      rewrite GMapVal'_proj_gmap_val. erewrite (gmap_key_pi _ k); eauto.
      unfold put0_dep. f_equal.
      rewrite GMapVal'_proj_gmap_val. erewrite (gmap_key_pi _ k); eauto. }
    match goal with
    | |- Q ?x ?y → Q ?x' ?y' => assert (y = y') as ->; auto
    end.
    destruct v as [v]. clear. revert v. unfold proj_gmap_val.
    generalize (decode_encode q). rewrite decode_encode.
    intros. f_equal. erewrite (UIP_dec e). instantiate (1 := eq_refl). auto.
  Qed.
  Lemma fold_dep_spec {R V} (Q : gmap_dep K V -> R -> Prop) f init
    (PEmpty : Q empty_dep init)
    (PNodes : forall i v m r (Hget : get_dep m i = None) (IHfold : Q m r),
       Q (put_dep m i v) (f r i v)) :
    forall m, Q m (fold_dep f init m).
  Proof.
    intros. destruct m; simpl; auto. apply fold'_dep_spec; auto.
  Qed.

  Lemma fold'_dep_parametricity {A B : Type} {V} (R : A -> B -> Prop)
    (fa : A -> ∀ k : K, V k -> A) (fb : B -> ∀ k : K, V k -> B)
    (RApp : forall a b k v (REL : R a b), R (fa a k v) (fb b k v)) :
    forall (m : gmap_dep_ne K V) a0 b0 (RInit : R a0 b0),
      R (fold'_dep fa a0 m) (fold'_dep fb b0 m).
  Proof.
    intros. unfold fold'_dep. destruct m as [m]. simpl.
    apply PMapDep.fold'_parametricity; auto. destruct v as [v].
    intros. destruct (decode i); auto; contradiction.
  Qed.
  Lemma fold_dep_parametricity {A B : Type} {V} (R : A -> B -> Prop)
    (fa : A -> ∀ k : K, V k -> A) (fb : B -> ∀ k : K, V k -> B)
    (RApp : forall a b k v (REL : R a b), R (fa a k v) (fb b k v)) :
    forall (m : gmap_dep K V) a0 b0 (RInit : R a0 b0),
      R (fold_dep fa a0 m) (fold_dep fb b0 m).
  Proof.
    intros. destruct m; auto. simpl. apply fold'_dep_parametricity; auto.
  Qed.

  Lemma gmap_dep_ne_ext {V} (m1 : gmap_dep_ne K V) :
    forall m2 (EQ : forall k, get'_dep m1 k = get'_dep m2 k),
      m1 = m2.
  Proof.
    destruct m1 as [m1], m2 as [m2]; simpl; auto.
    intros. f_equal.
    apply PMapDep.pmap'_ext. exact gmap_key_pi.
    intros k pf.
    assert (∃ q, k = encode q).
    { destruct pf. destruct (decode k); inversion e; subst; eauto. }
    des; subst.
    specialize (EQ q). unfold get'_dep in EQ. simpl in EQ.
    destruct (PMapDep.get' m1 _), (PMapDep.get' m2 _); auto.
    - apply Some_inj, (f_equal GMapVal') in EQ.
      repeat rewrite GMapVal'_proj_gmap_val in EQ; subst; auto.
    - inversion EQ.
    - inversion EQ.
  Qed.
  Lemma gmap_dep_ext {V} (m1 : gmap_dep K V) :
    forall m2 (EQ : forall k, get_dep m1 k = get_dep m2 k),
      m1 = m2.
  Proof.
    intros. destruct m1 as [|m1], m2 as [|m2]; simpl in *; auto.
    - exfalso.
      unshelve eapply PMapDep.pmap'_contradiction.
      exact (gmap_key K). 2: exact (gmap_dep_car m2).
      intros k pf.
      assert (∃ q, k = encode q).
      { destruct pf. destruct (decode k); inversion e; subst; eauto. }
      des; subst. specialize (EQ q). unfold get'_dep in EQ.
      destruct (PMapDep.get' _ _); auto. inversion EQ.
    - exfalso.
      unshelve eapply PMapDep.pmap'_contradiction.
      exact (gmap_key K). 2: exact (gmap_dep_car m1).
      intros k pf.
      assert (∃ q, k = encode q).
      { destruct pf. destruct (decode k); inversion e; subst; eauto. }
      des; subst. specialize (EQ q). unfold get'_dep in EQ.
      destruct (PMapDep.get' _ _); auto. inversion EQ.
    - intros. f_equal. apply gmap_dep_ne_ext; auto.
  Qed.

  Definition list_to_map_dep {V} (l : list (sigT V)) :=
    fold_right (fun kv m => put_dep m (projT1 kv) (projT2 kv)) empty_dep l
  .
  Definition map_dep_to_list {V} (m : gmap_dep K V) : list (sigT V) :=
    fold_dep (fun l k v => existT V k v :: l) [] m
  .

  Lemma map_dep_to_list_spec {V} (m : gmap_dep K V) :
    NoDup (map (projT1 (P := V)) (map_dep_to_list m)) ∧ (∀ i x, In (existT V i x) (map_dep_to_list m) ↔ get_dep m i = Some x).
  Proof.
    unfold map_dep_to_list. eapply fold_dep_spec.
    - split. constructor. setoid_rewrite get_dep_empty_dep.
      simpl. intuition congruence.
    - intros. clear m. rename m0 into m.
      destruct IHfold as (NODUP & IH). cbn [map projT1].
      split.
      + rewrite NoDup_cons_iff. split; auto.
        intro IN.
        rewrite in_map_iff in IN.
        des; subst. destruct x as (i & x); simpl in *.
        rewrite IH in *. congruence.
      + intros j x. destruct (eq_dec i j); subst.
        rewrite get_dep_put_dep_same. cbn [In].
        split; intro EQ.
        des. apply Eqdep_dec.inj_pair2_eq_dec in EQ; subst; auto using eq_dec.
        rewrite IH in *. congruence.
        left. congruence.
        rewrite get_dep_put_dep_diff; auto. rewrite <- IH.
        cbn [In]. intuition congruence.
  Qed.

  Lemma list_to_map_dep_to_list {V} (m : gmap_dep K V) : list_to_map_dep (map_dep_to_list m) = m.
  Proof.
    apply gmap_dep_ext. intros i.
    specialize (map_dep_to_list_spec m). intros (NODUP & IN).
    destruct (get_dep m i) as [v|] eqn:GET.
    - rewrite <- IN in GET. revert GET NODUP. generalize (map_dep_to_list m).
      clear. intro. revert i v.
      induction l; simpl; destruct 1; subst; cbn [projT1].
      + rewrite get'_dep_put'_dep_same. auto.
      + destruct a as (k & v').
        rewrite NoDup_cons_iff. apply (in_map (projT1 (P := V))) in H0 as IN.
        cbn [projT1] in *.
        intros. des.
        destruct (eq_dec k i); subst. contradiction.
        rewrite get'_dep_put'_dep_diff by auto. eauto.
    - assert (∀ x, ¬ In (existT V i x) (map_dep_to_list m)) as HINT.
      { intro. rewrite IN. intro. congruence. }
      revert HINT. generalize (map_dep_to_list m). clear. intro. revert i.
      induction l; simpl; auto.
      + destruct a as (k & v). intros.
        destruct (eq_dec i k); subst.
        1: specialize (HINT v); exfalso; eauto.
        rewrite get'_dep_put'_dep_diff by auto. apply IHl. intuition eauto.
  Qed.
End map_dep_ok.

Global Instance GMapDepNEEqDec `{Countable K} `{!∀ k, EqDec (V k)} : EqDec (gmap_dep_ne K V).
Proof.
  unshelve eset (EqDecPMapDep := @PMapDep.pmap'_eq_dec (gmap_key K) (gmap_val K V) _ gmap_key_pi).
  1,2: auto.
  - intros. split. destruct t1, t2.
    unshelve eset (_ : ∀ x y, GMapVal (V := V) (q := p) x = GMapVal y → x = y).
    { congruence. }
    generalize e. generalize (GMapVal (V := V) (q := p)).
    clear e. revert y y0. destruct (decode p). 2: destruct y.
    intros. destruct (eq_dec y y0).
    + left. f_equal. assumption.
    + right. intro. apply e in H2. exact (n H2).
  - typeclasses eauto.
Defined.
Global Instance GMapDepEqDec `{Countable K} `{!∀ k, EqDec (V k)} : EqDec (gmap_dep K V) := _.

#[refine, global] Instance GMapDepNECountable `{Countable K, !∀ k, EqDec (V k), !∀ k, Countable (V k)} : Countable (gmap_dep_ne K V) :=
{
  encode m := encode (map_dep_to_list (nempty_dep m) : list (sigT V));
  decode p := match decode p : option (list (sigT V)) with Some l => match list_to_map_dep l with nempty_dep m => Some m | empty_dep => None end | None => None end;
}.
Proof.
  abstract (intros; now rewrite decode_encode, list_to_map_dep_to_list).
Defined.
Global Program Instance GMapDepCountable `{Countable K, !∀ k, EqDec (V k), !∀ k, Countable (V k)} : Countable (gmap_dep K V) :=
{
  encode m := encode (map_dep_to_list m : list (sigT V));
  decode p := match decode p : option (list (sigT V)) with Some l => Some (list_to_map_dep l) | None => None end;
}.
Next Obligation.
  rewrite decode_encode; simpl. now rewrite list_to_map_dep_to_list.
Qed.

Section map_map.
  Context `{Countable K} `{Countable K'}.

  Definition gmap_map {V W} (f : V → option W) :
    gmap K V → gmap K W :=
    fold (fun acc k v =>
      match f v with
      | Some v' => put acc k v'
      | None => acc
      end
    ) empty.

  Lemma gmap_map_spec {V W} (f : V → option W) m :
    ∀ k, get (gmap_map f m) k =
      match get m k with
      | Some v => f v
      | None => None
      end.
  Proof.
    unfold gmap_map. apply fold_spec.
    - intros. now repeat rewrite get_empty.
    - intros. destruct (eq_dec i k); subst.
      + rewrite get_put_same.
        destruct (f v).
        1: now rewrite get_put_same.
        specialize (IHfold k). rewrite Hget in IHfold. assumption.
      + rewrite get_put_diff by auto.
        rewrite <- IHfold. destruct (f v); auto.
        apply get_put_diff; auto.
  Qed.

  Definition gmap_filter_fst {V} (x : K) :
    gmap (K * K') V → gmap K' V :=
    fold (fun acc k v =>
      match eq_dec (fst k) x with
      | left EQ => put acc (snd k) v
      | right NEQ => acc
      end) empty.

  Lemma gmap_filter_fst_spec {V} (x : K) m :
    ∀ y, get (gmap_filter_fst (V := V) x m) y = get m (x, y).
  Proof.
    unfold gmap_filter_fst. apply fold_spec.
    - intros. now repeat rewrite get_empty.
    - intros. destruct i as (k & k'). cbn [fst snd] in *.
      destruct (eq_dec _ _); subst.
      destruct (eq_dec k' y); subst.
      + now repeat rewrite get_put_same.
      + repeat rewrite get_put_diff; auto.
        inversion 1; subst; auto.
      + rewrite get_put_diff by (inversion 1; subst; auto).
        auto.
  Qed.

  Definition gmap_filter_snd {V} (y : K') :
    gmap (K * K') V → gmap K V :=
    fold (fun acc k v =>
      match eq_dec (snd k) y with
      | left EQ => put acc (fst k) v
      | right NEQ => acc
      end) empty.

  Lemma gmap_filter_snd_spec {V} (y : K') m :
    ∀ x, get (gmap_filter_snd (V := V) y m) x = get m (x, y).
  Proof.
    unfold gmap_filter_snd. apply fold_spec.
    - intros. now repeat rewrite get_empty.
    - intros. destruct i as (k & k'). cbn [fst snd] in *.
      destruct (eq_dec _ _); subst.
      destruct (eq_dec k x); subst.
      + now repeat rewrite get_put_same.
      + repeat rewrite get_put_diff; auto.
        inversion 1; subst; auto.
      + rewrite get_put_diff by (inversion 1; subst; auto).
        auto.
  Qed.

  Definition gmap_dep_map {V W} (f : ∀ k, V k → option W) :
    gmap_dep K V → gmap K W :=
    fold_dep (fun acc k v =>
      match f k v with
      | Some v' => put acc k v'
      | None => acc
      end
    ) empty.

  Lemma gmap_dep_map_spec {V W} (f : ∀ k, V k → option W) m :
    ∀ k, get (gmap_dep_map f m) k =
      match get_dep m k with
      | Some v => f k v
      | None => None
      end.
  Proof.
    unfold gmap_dep_map. apply fold_dep_spec.
    - intros. now rewrite get_empty, get_dep_empty_dep.
    - intros. destruct (eq_dec i k); subst.
      + rewrite get_dep_put_dep_same.
        destruct (f k v).
        1: now rewrite get_put_same.
        specialize (IHfold k). rewrite Hget in IHfold. assumption.
      + rewrite get_dep_put_dep_diff by auto.
        rewrite <- IHfold. destruct (f i v); auto.
        apply get_put_diff; auto.
  Qed.

  Definition gmap_dep_map_dep {V W} (f : ∀ k, V k → option (W k)) :
    gmap_dep K V → gmap_dep K W :=
    fold_dep (fun acc k v =>
      match f k v with
      | Some v' => put_dep acc k v'
      | None => acc
      end
    ) empty_dep.

  Lemma gmap_dep_map_dep_spec {V W} (f : ∀ k, V k → option (W k)) m :
    ∀ k, get_dep (gmap_dep_map_dep f m) k =
      match get_dep m k with
      | Some v => f k v
      | None => None
      end.
  Proof.
    unfold gmap_dep_map_dep. apply fold_dep_spec.
    - intros. now repeat rewrite get_dep_empty_dep.
    - intros. destruct (eq_dec i k); subst.
      + rewrite get_dep_put_dep_same.
        destruct (f k v).
        1: now rewrite get_dep_put_dep_same.
        specialize (IHfold k). rewrite Hget in IHfold. assumption.
      + rewrite get_dep_put_dep_diff by auto.
        rewrite <- IHfold. destruct (f i v); auto.
        apply get_dep_put_dep_diff; auto.
  Qed.
End map_map.
