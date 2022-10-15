(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(** * triplet

Pierre Letouzey & Laurent Thery

Definition of triplets
*)

From Coq Require Export Bool.
From Stalmarck Require Export rZ.
From Coq Require Export List.
From Stalmarck Require Export normalize.
From Stalmarck Require Export sTactic.

(** Lifting of f from rNat-> bool to rZ -> bool compatible with rZComp *)
Definition rZEval (f : rNat -> bool) (r : rZ) : bool :=
  match r with
  | rZPlus n => f n
  | rZMinus n => negb (f n)
  end.

(** A triplet is an operation plus 3 rZ 
   a = b /\ c are coded as (Triplet rAnd a b c) *)
Inductive triplet : Set :=
    Triplet : rBoolOp -> rZ -> rZ -> rZ -> triplet.

(** Equality on triplets is decidable *)
Definition rBoolOpDec : forall a b : rBoolOp, {a = b} + {a <> b}.
intros a b; case a; case b; auto with stalmarck; right; red in |- *; intros; discriminate.
Defined.

(** Equality is decidable *)
Definition tripletDec : forall t1 t2 : triplet, {t1 = t2} + {t1 <> t2}.
intros t1 t2; case t1; case t2.
intros r r0 r1 r2 r3 r4 r5 r6; case (rBoolOpDec r3 r);
 [ idtac | intros H; right; Contradict H; inversion H ]; 
 auto with stalmarck.
intros H1; case (rZDec r4 r0);
 [ idtac | intros H; right; Contradict H; inversion H ]; 
 auto with stalmarck.
intros H2; case (rZDec r5 r1);
 [ idtac | intros H; right; Contradict H; inversion H ]; 
 auto with stalmarck.
intros H3; case (rZDec r6 r2);
 [ idtac | intros H; right; Contradict H; inversion H ]; 
 auto with stalmarck.
intros H4; left; rewrite H1; rewrite H2; rewrite H3; rewrite H4; auto with stalmarck.
Defined.

(** Evaluation tEval(a=b/\c)=(f(a)=f(b)/\f(b)) *)
Definition tEval (f : rNat -> bool) (t : triplet) : bool :=
  match t with
  | Triplet n v1 v2 v3 =>
      eqb (rZEval f v1) (rBoolOpFun n (rZEval f v2) (rZEval f v3))
  end.

(** f realizes a list of triplets if its evaluates all the triplets to true *)
Definition realizeTriplets (f : rNat -> bool) (L : list triplet) : Prop :=
  forall t : triplet, In t L -> tEval f t = true.

Theorem realizeTripletNil : forall f : rNat -> bool, realizeTriplets f nil.
Proof.
intros f; red in |- *.
intros t H'; inversion H'.
Qed.
#[export] Hint Resolve realizeTripletNil : stalmarck.

Theorem realizeTripletCons :
 forall (f : rNat -> bool) (t : triplet) (L : list triplet),
 tEval f t = true -> realizeTriplets f L -> realizeTriplets f (t :: L).
Proof.
intros f t L H' H'0; red in |- *; simpl in |- *.
intros t0 H'1; elim H'1; intros H'2; auto with stalmarck; rewrite <- H'2; auto with stalmarck.
Qed.

#[export] Hint Resolve realizeTripletCons : stalmarck.

Theorem realizeTripletIncl :
 forall (f : rNat -> bool) (L1 L2 : list triplet),
 realizeTriplets f L1 -> incl L2 L1 -> realizeTriplets f L2.
Proof.
intros f L1 L2 H'0 H'1; red in |- *; auto with stalmarck.
Qed.

#[export] Hint Resolve realizeTripletIncl : stalmarck.

(** An equation is valid if every f that realizes f and f(rZrue)=true
   then f(a)=f(b) *)
Definition validEquation (L : list triplet) (a b : rZ) : Prop :=
  forall f : rNat -> bool,
  realizeTriplets f L -> f zero = true -> rZEval f a = rZEval f b.

(** What is the maximal variable of a triplet *)
Definition maxVarTriplet (t : triplet) :=
  match t with
  | Triplet n v1 v2 v3 => rmax (rmax (valRz v1) (valRz v2)) (valRz v3)
  end.

(** Iteration to compute the max of a list of triplets *)
Fixpoint maxVarTriplets (l : list triplet) : rNat :=
  match l with
  | nil => zero
  | t :: q => rmax (maxVarTriplet t) (maxVarTriplets q)
  end.

(** Check if a variable is in a triplet *)
Definition inTriplet (a : rZ) (t : triplet) :=
  match t with
  | Triplet n v1 v2 v3 => eqRz a v1 \/ eqRz a v2 \/ eqRz a v3
  end.

Definition inTripletDec :
  forall (a : rZ) (t : triplet), {inTriplet a t} + {~ inTriplet a t}.
intros a t; case t; simpl in |- *; intros b v1 v2 v3; unfold eqRz in |- *.
case (rNatDec (valRz a) (valRz v1)); auto with stalmarck;
 case (rNatDec (valRz a) (valRz v2)); auto with stalmarck;
 case (rNatDec (valRz a) (valRz v3)); auto with stalmarck.
intros H' H'0 H'1; right; red in |- *; intros H'2; Elimc H'2; intros H'2;
 [ idtac | Elimc H'2; intros H'2 ]; auto with stalmarck.
Qed.

(** Check if a variable is in a list of triplets*)
Fixpoint inTriplets (v : rZ) (l : list triplet) {struct l} : Prop :=
  match l with
  | nil => eqRz v (rZPlus zero)
  | t :: q => inTriplet v t \/ inTriplets v q
  end.

Definition inTripletsDec :
  forall (a : rZ) (L : list triplet), {inTriplets a L} + {~ inTriplets a L}.
intros a L; elim L; simpl in |- *; auto with stalmarck.
unfold eqRz in |- *; apply rNatDec; auto with stalmarck.
intros a0 l H'; case H'; auto with stalmarck.
case (inTripletDec a a0); auto with stalmarck.
intros H'0 H'1; right; red in |- *; intros H'2; elim H'2; auto with stalmarck.
Qed.

Theorem inTripletsTrue : forall L : list triplet, inTriplets rZTrue L.
Proof.
intros L; elim L; simpl in |- *; auto with stalmarck.
Qed.

Theorem inTripletsFalse : forall L : list triplet, inTriplets rZFalse L.
Proof.
intros L; elim L; simpl in |- *; auto with stalmarck.
Qed.

Theorem inTripletsComp :
 forall (L : list triplet) (v : rZ),
 inTriplets v L -> inTriplets (rZComp v) L.
Proof.
intros L; elim L; simpl in |- *; auto with stalmarck.
unfold eqRz in |- *; auto with stalmarck.
intros v H'; rewrite <- H'; case v; auto with stalmarck.
intros a; case a; simpl in |- *; auto with stalmarck.
unfold eqRz in |- *; auto with stalmarck.
intros H' r r0 r1 l H'0 v H'1; Elimc H'1; intros H'1;
 [ Elimc H'1; intros H'1;
    [ rewrite <- H'1 | Elimc H'1; intros H'1; rewrite <- H'1 ]
 | idtac ]; auto with stalmarck; case v; auto with stalmarck.
Qed.

Theorem inTripletsCompInv :
 forall (L : list triplet) (v : rZ),
 inTriplets (rZComp v) L -> inTriplets v L.
Proof.
intros L v H'; rewrite (rZCompInvol v).
apply inTripletsComp; auto with stalmarck.
Qed.

Theorem inTripletsIn :
 forall (t : triplet) (L : list triplet) (v : rZ),
 inTriplet v t -> In t L -> inTriplets v L.
Proof.
intros t L; elim L; simpl in |- *; auto with stalmarck.
intros v H' H'0; elim H'0; auto with stalmarck.
intros a l H' v H'0 H'1; elim H'1; intros H'2; auto with stalmarck; rewrite H'2; auto with stalmarck.
Qed.

(** Compute the list of all signed variable in the list of triplets *)
Fixpoint varTriplets (L : list triplet) : list rZ :=
  match L with
  | nil => rZTrue :: nil
  | Triplet _ p q r :: L' => p :: q :: r :: varTriplets L'
  end.

Lemma varTripletTrue : forall L : list triplet, In rZTrue (varTriplets L).
Proof.
simple induction L; simpl in |- *; auto with stalmarck.
intros t L' HR; case t; simpl in |- *; auto with stalmarck.
Qed.

Lemma varTripletTriplet1 :
 forall (p q r : rZ) (b : rBoolOp) (L : list triplet),
 In (Triplet b p q r) L -> In p (varTriplets L).
Proof.
simple induction L; simpl in |- *; auto with stalmarck.
intros t L' HR Ht; elim Ht; intros Ht1; [ rewrite Ht1 | case t ];
 simpl in |- *; auto with stalmarck.
Qed.

Lemma varTripletTriplet2 :
 forall (p q r : rZ) (b : rBoolOp) (L : list triplet),
 In (Triplet b p q r) L -> In q (varTriplets L).
Proof.
simple induction L; simpl in |- *; auto with stalmarck.
intros t L' HR Ht; elim Ht; intros Ht1; [ rewrite Ht1 | case t ];
 simpl in |- *; auto with stalmarck.
Qed.

Lemma varTripletsTriplet3 :
 forall (p q r : rZ) (b : rBoolOp) (L : list triplet),
 In (Triplet b p q r) L -> In r (varTriplets L).
Proof.
simple induction L; simpl in |- *; auto with stalmarck.
intros t L' HR Ht; elim Ht; intros Ht1; [ rewrite Ht1 | case t ];
 simpl in |- *; auto with stalmarck.
Qed.

Lemma eqRzElim : forall a b : rZ, eqRz a b -> a = b \/ a = rZComp b.
Proof.
intros a b; case a; case b; unfold eqRz in |- *; simpl in |- *;
 intros r r0 H'; rewrite H'; auto with stalmarck.
Qed.

Lemma inTripletsVarTriplet :
 forall (L : list triplet) (a : rZ),
 inTriplets a L -> In a (varTriplets L) \/ In (rZComp a) (varTriplets L).
Proof.
intros L; elim L; simpl in |- *; auto with stalmarck.
intros a H'; case (eqRzElim _ _ H'); intros H'1; rewrite H'1; auto with stalmarck.
intros a; case a; auto with stalmarck.
intros r r0 r1 r2 l H' a0 H'0; Elimc H'0; intros H'0; auto with stalmarck.
simpl in H'0; Casec H'0; intros H'0; [ idtac | Casec H'0; intros H'0 ];
 case (eqRzElim _ _ H'0); intros H'1; rewrite H'1; 
 simpl in |- *; auto with stalmarck.
elim (H' _ H'0); auto with datatypes stalmarck.
Qed.
