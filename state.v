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



(****************************************************************************
                                                                           
          Stalmarck  :   state                                             
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of states as the list of equations, i.e pairs of rZ *)
Require Import List.
Require Export triplet.

Definition State := list (rZ * rZ).

Inductive eqStateRz : State -> rZ -> rZ -> Prop :=
  | eqStateRzRef : forall (a : rZ) (S : State), eqStateRz S a a
  | eqStateRzIn :
      forall (a b : rZ) (S : State), In (a, b) S -> eqStateRz S a b
  | eqStateRzInv :
      forall (a b : rZ) (S : State),
      eqStateRz S a b -> eqStateRz S (rZComp a) (rZComp b)
  | eqStateRzSym :
      forall (a b : rZ) (S : State), eqStateRz S a b -> eqStateRz S b a
  | eqStateRzTrans :
      forall (a b c : rZ) (S : State),
      eqStateRz S a b -> eqStateRz S b c -> eqStateRz S a c
  | eqStateRzContr :
      forall (a b c : rZ) (S : State),
      eqStateRz S a (rZComp a) -> eqStateRz S b c.
Hint Resolve eqStateRzRef eqStateRzIn eqStateRzInv.
(* equality is compatible with the complement *)

Theorem eqStateInvInv :
 forall (S : State) (p q : rZ),
 eqStateRz S (rZComp p) (rZComp q) -> eqStateRz S p q.
intros S p0 q0 H'; rewrite <- (rZCompInv p0); rewrite <- (rZCompInv q0); auto.
Qed.
(* An alternative of eqStateRzContr *)

Lemma eqStateContr :
 forall (S : State) (p q r s : rZ),
 eqStateRz S p q -> eqStateRz S p (rZComp q) -> eqStateRz S r s.
intros S p q r s H' H'0.
apply eqStateRzContr with (a := q); auto.
apply eqStateRzTrans with (b := p); auto.
apply eqStateRzSym; auto.
Qed.
(* Push complement to the right *)

Lemma eqStateContrSimpl1 :
 forall (S : State) (p q : rZ),
 eqStateRz S p (rZComp q) -> eqStateRz S (rZComp p) q.
intros S p q H'.
apply eqStateInvInv; rewrite rZCompInv; auto.
Qed.
Hint Resolve eqStateContrSimpl1.
Hint Immediate eqStateRzSym eqStateInvInv.

(* Adding an equation to a state *)

Definition addEq (p : rZ * rZ) (S : State) : State := p :: S.
Hint Unfold addEq.
(* The added equation is valid *)

Lemma eqStateaddEq1 :
 forall (S : State) (p q : rZ), eqStateRz (addEq (p, q) S) p q.
intros S p q.
apply eqStateRzIn; simpl in |- *; auto.
Qed.
(* All the previous equations are valid *)

Lemma eqStateaddEq2 :
 forall (S : State) (a b p q : rZ),
 eqStateRz S p q -> eqStateRz (addEq (a, b) S) p q.
intros S a b p q H'; generalize a b; Elimc H'; clear a b p q S; auto.
intros a b S H' a0 b0; apply eqStateRzIn; simpl in |- *; auto.
intros a b c S H' H'0 H'1 H'2 a0 b0.
apply eqStateRzTrans with (b := b); auto.
intros a b c S H' H'0 a0 b0.
apply eqStateRzContr with (a := a); auto.
Qed.
Hint Resolve eqStateaddEq1 eqStateaddEq2.

(* We define the fact of being included *)

Definition inclState (S1 S2 : State) : Prop :=
  forall i j : rZ, eqStateRz S1 i j -> eqStateRz S2 i j.

Theorem inclStateRef : forall S : State, inclState S S.
red in |- *; auto.
Qed.
Hint Resolve inclStateRef.
(*Simpler version *)

Theorem inclStateIn :
 forall S1 S2 : State,
 (forall a b : rZ, In (a, b) S1 -> eqStateRz S2 a b) -> inclState S1 S2.
intros S1 S2 H'; red in |- *.
intros i j H'0; generalize H'; elim H'0; auto.
intros a b L0 H'1 H'2 H'3; apply eqStateRzSym; auto.
intros a b c0 L0 H'1 H'2 H'3 H'4 H'5; apply eqStateRzTrans with (b := b);
 auto.
intros a b c0 L0 H'1 H'2 H'3; apply eqStateRzContr with (a := a); auto.
Qed.

(* We define the fact of being equal *)

Definition eqState (S1 S2 : State) : Prop :=
  inclState S1 S2 /\ inclState S2 S1.

Theorem eqStateRef : forall S : State, eqState S S.
intros; red in |- *; split; auto.
Qed.
Hint Resolve eqStateRef.

Theorem eqStateSym : forall S1 S2 : State, eqState S1 S2 -> eqState S2 S1.
intros S1 S2 H'; elim H'; red in |- *; auto.
Qed.
Hint Immediate eqStateSym.

Theorem eqStateInv :
 forall (S1 S2 : State) (a b : rZ),
 eqState S1 S2 -> (eqStateRz S1 a b <-> eqStateRz S2 a b).
intros S1 S2 a b H'; inversion H'; red in |- *; auto.
Qed.

Theorem addEqInclState :
 forall (S : State) (a b : rZ), inclState S (addEq (a, b) S).
intros S a b; red in |- *; auto.
Qed.
Hint Resolve addEqInclState.

Theorem inclStateTrans :
 forall S1 S2 S3 : State,
 inclState S1 S2 -> inclState S2 S3 -> inclState S1 S3.
intros S1 S2 S3 H' H'0; red in |- *; auto.
Qed.

Theorem eqStateIncl :
 forall (S1 S2 : State) (p q : rZ),
 inclState S1 S2 -> eqStateRz S1 p q -> eqStateRz S2 p q.
intros S1 S2 p q H' H'0; auto.
Qed.

Theorem eqStateEq :
 forall (S1 S2 : State) (p q : rZ),
 eqState S1 S2 -> eqStateRz S1 p q -> eqStateRz S2 p q.
intros S1 S2 p q H' H'0.
apply eqStateIncl with (S1 := S1); auto.
inversion H'; auto.
Qed.

Theorem addEqInclState2 :
 forall (S : State) (a b c d : rZ),
 inclState S (addEq (a, b) (addEq (c, d) S)).
intros S a b c d.
apply inclStateTrans with (S2 := addEq (c, d) S); auto.
Qed.
Hint Resolve addEqInclState2.

Theorem inclStateAddEqInv :
 forall (p q : rZ) (S1 S2 : State),
 inclState S1 S2 -> eqStateRz S2 p q -> inclState (addEq (p, q) S1) S2.
intros p0 q0 S1 S2 H' H'0; red in |- *; auto.
intros i j H'1; generalize H'0 H'; auto.
cut (exists S3 : State, S3 = addEq (p0, q0) S1); auto.
intros H'2; Elimc H'2; intros S3 E; rewrite <- E in H'1; auto.
generalize E; elim H'1; auto.
intros a b L H'2 H'3; rewrite H'3 in H'2; simpl in H'2; case H'2; auto.
intros H'4; inversion H'4; auto.
intros a b S H'2 H'3 H'4 H'5 H'6; auto.
apply eqStateRzSym; auto.
intros a b c S H'2 H'3 H'4 H'5 H'6 H'7 H'8.
apply eqStateRzTrans with (b := b); auto.
intros a b c S H'2 H'3 H'4 H'5 H'6.
apply eqStateRzContr with (a := a); auto.
exists (addEq (p0, q0) S1); auto.
Qed.
Hint Resolve inclStateAddEqInv.

Theorem inclStateAddEq :
 forall (S1 S2 : State) (a b : rZ),
 inclState S1 S2 -> inclState (addEq (a, b) S1) (addEq (a, b) S2).
intros S1 S2 a b H'.
apply inclStateAddEqInv; simpl in |- *.
apply inclStateTrans with (S2 := S2); auto.
apply eqStateRzIn; auto.
simpl in |- *.
auto.
Qed.
Hint Resolve inclStateAddEq.

Theorem eqStateAddEq :
 forall (S1 S2 : State) (a b : rZ),
 eqState S1 S2 -> eqState (addEq (a, b) S1) (addEq (a, b) S2).
intros S1 S2 a b H'; inversion H'; red in |- *; auto.
Qed.
Hint Resolve eqStateAddEq.

Theorem inclStateEqStateComp :
 forall S1 S2 S3 S4 : State,
 eqState S1 S2 -> eqState S3 S4 -> inclState S1 S3 -> inclState S2 S4.
intros S1 S2 S3 S4 H' H'0 H'1; inversion H'; inversion H'0.
apply inclStateTrans with (S2 := S3); auto.
apply inclStateTrans with (S2 := S1); auto.
Qed.

Theorem eqStateTrans :
 forall S1 S2 S3 : State, eqState S1 S2 -> eqState S2 S3 -> eqState S1 S3.
intros S1 S2 S3 H' H'0; inversion H'; inversion H'0.
red in |- *; split; apply inclStateTrans with (S2 := S2); auto.
Qed.

Theorem addEqComp :
 forall (a b a' b' : rZ) (S : State),
 eqStateRz S a a' ->
 eqStateRz S b b' -> eqState (addEq (a, b) S) (addEq (a', b') S).
intros a b a' b' S H' H'0.
red in |- *; split; apply inclStateIn; simpl in |- *;
 (intros a0 b0 H'1; Elimc H'1; intros H'1; [ inversion H'1 | idtac ]); 
 auto; rewrite <- H1; rewrite <- H0.
apply eqStateRzTrans with (b := a'); auto.
apply eqStateRzTrans with (b := b'); auto.
apply eqStateRzTrans with (b := a); auto.
apply eqStateRzTrans with (b := b); auto.
Qed.
Hint Resolve addEqComp.

(* A valuation function realizes a state if all its basic equations are true *)

Definition realizeState (f : rNat -> bool) (S : State) : Prop :=
  forall i j : rZ, In (i, j) S -> rZEval f i = rZEval f j.

Theorem realizeStateNil : forall f : rNat -> bool, realizeState f nil.
intros f; red in |- *; simpl in |- *.
intros i j H'; elim H'.
Qed.
Hint Resolve realizeStateNil.

Theorem rZEvalCompInv :
 forall (a : rZ) (f : rNat -> bool), rZEval f (rZComp a) = negb (rZEval f a).
intros a f; case a; simpl in |- *; auto.
intros r; case (f r); auto.
Qed.
(* If a valuation function realizes a state then all its equations are true *)

Theorem realizeStateInv :
 forall (f : rNat -> bool) (S : State),
 realizeState f S ->
 forall i j : rZ, eqStateRz S i j -> rZEval f i = rZEval f j.
intros f S H' i j H'0; generalize H'; elim H'0; auto.
intros a b S0 H'1 H'2 H'3.
rewrite rZEvalCompInv; auto; rewrite rZEvalCompInv; auto.
rewrite H'2; auto.
intros a b S0 H'1 H'2 H'3.
rewrite H'2; auto.
intros a b c S0 H'1 H'2 H'3 H'4 H'5.
rewrite H'2; auto.
intros a b c S0 H'1 H'2 H'3.
absurd (rZEval f a = rZEval f (rZComp a)); auto.
rewrite rZEvalCompInv; case (rZEval f a); simpl in |- *; red in |- *; intros;
 discriminate.
Qed.

Theorem realizeStateInvComp :
 forall (f : rNat -> bool) (S : State),
 realizeState f S ->
 forall i j : rZ, eqStateRz S i (rZComp j) -> rZEval f i = negb (rZEval f j).
intros f S H' i j H'0.
rewrite <- rZEvalCompInv.
apply realizeStateInv with (S := S); auto.
Qed.

Theorem realizeStateAddEq :
 forall (f : rNat -> bool) (S : State),
 realizeState f S ->
 forall i j : rZ, rZEval f i = rZEval f j -> realizeState f (addEq (i, j) S).
intros f S H' i j H'0; red in |- *; simpl in |- *; auto.
intros i0 j0 H'1; elim H'1; intros H'2; clear H'1; [ inversion H'2 | idtac ];
 auto.
rewrite <- H1; auto.
rewrite <- H0; auto.
Qed.
Hint Resolve realizeStateAddEq.

Theorem realizeStateIncl :
 forall (f : rNat -> bool) (S1 S2 : State),
 realizeState f S1 -> inclState S2 S1 -> realizeState f S2.
intros f S1 S2 H' H'0; red in |- *; auto.
intros i j H'1.
apply realizeStateInv with (S := S1); auto.
Qed.

Theorem realizeStateInvAddEq :
 forall (f : rNat -> bool) (S : State) (i j : rZ),
 realizeState f (addEq (i, j) S) -> rZEval f i = rZEval f j.
intros f S i j H'.
apply realizeStateInv with (S := addEq (i, j) S); auto.
Qed.

Theorem realizeStateInvAddEq2 :
 forall (f : rNat -> bool) (S : State) (i j k l : rZ),
 realizeState f (addEq (i, j) (addEq (k, l) S)) ->
 rZEval f k = rZEval f l /\ rZEval f i = rZEval f j.
intros f S i j k l H'; split.
apply realizeStateInvAddEq with (S := S); auto.
apply realizeStateIncl with (S1 := addEq (i, j) (addEq (k, l) S)); auto.
apply realizeStateInvAddEq with (S := addEq (k, l) S); auto.
Qed.

(* What it means for a state to be contradictory *)

Definition contradictory (S : State) : Prop :=
  exists a : rZ, eqStateRz S a (rZComp a).
(* Of course if a state is contradictory it can't be realized *)

Theorem contradictoryNotRealize :
 forall S : State,
 contradictory S -> forall f : rNat -> bool, ~ realizeState f S.
intros S H' f; red in |- *; intros H'0; inversion H'.
absurd (rZEval f x = rZEval f (rZComp x)).
rewrite rZEvalCompInv; case (rZEval f x); auto; red in |- *; intros;
 discriminate.
apply realizeStateInv with (S := S); auto.
Qed.
Hint Resolve contradictoryNotRealize.

Theorem ContrIncl :
 forall S : State, inclState S ((rZPlus zero, rZMinus zero) :: nil).
intros S; red in |- *; auto.
intros i j H'.
apply eqStateRzContr with (a := rZPlus zero); auto with datatypes.
Qed.
Hint Resolve ContrIncl.