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
                                                                           
          Stalmarck  :    interState                                       
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of the intersection of two states *)
Require Import List.
Require Export stateDec.

(* The property of being an intersection *)

Definition interStateP (S1 S2 S3 : State) : Prop :=
  inclState S3 S1 /\
  inclState S3 S2 /\
  (forall S4 : State, inclState S4 S1 -> inclState S4 S2 -> inclState S4 S3).

Theorem interStatePRef : forall S1 : State, interStateP S1 S1 S1.
intros S1; red in |- *; auto with stalmarck.
Qed.

Theorem interStatePIncl :
 forall S1 S2 S3 S4 : State,
 interStateP S1 S2 S3 ->
 inclState S4 S1 -> inclState S4 S2 -> inclState S4 S3.
intros S1 S2 S3 S4 H H1 H2; case H; intros H' H'1; case H'1; auto with stalmarck.
Qed.

Theorem interStatePSym :
 forall S1 S2 S3 : State, interStateP S1 S2 S3 -> interStateP S2 S1 S3.
unfold interStateP in |- *. intuition.
Qed.


Theorem interStatePInclSelf :
 forall S1 S2 : State, inclState S1 S2 -> interStateP S1 S2 S1.
unfold interStateP in |- *. intuition.
Qed.

Theorem interStatePEq :
 forall S1 S2 S'1 S'2 S3 S'3 : State,
 interStateP S1 S2 S3 ->
 interStateP S'1 S'2 S'3 ->
 eqState S1 S'1 -> eqState S2 S'2 -> eqState S3 S'3.
unfold interStateP in |- *.
intros S1 S2 S'1 S'2 S3 S'3 H H1 H2 H3; split.

generalize (interStatePIncl S'1 S'2) (inclStateEqStateComp S3 S3 S1 S'1)
 (inclStateEqStateComp S3 S3 S2 S'2).
intuition.

generalize (interStatePIncl S1 S2) (inclStateEqStateComp S'3 S'3 S'1 S1)
 (inclStateEqStateComp S'3 S'3 S'2 S2).
intuition.
Qed.
(* Given a state, gives the variables that could have non trivial equality *)

Fixpoint stripRz (S : State) : list rZ :=
  match S with
  | nil => nil
  | (a, b) :: S' => a :: rZComp a :: b :: rZComp b :: stripRz S'
  end.
(* The function has the expected property for non contradictory state *)

Theorem eqConstrStateInL :
 forall (S : State) (a b : rZ),
 eqConstrState S a b ->
 a <> b -> ~ (forall a b : rZ, eqStateRz S a b) -> In a (stripRz S).
intros S a b H'; Elimc H'; clear S a b; auto with stalmarck; simpl in |- *.
intros a H'0; case H'0; auto with stalmarck.
intros a b p; case p; intros a' b'; simpl in |- *; auto with stalmarck.
intros S H' H'0 H'1 H'2; right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec a b); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec a c); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec a (rZComp b)); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec a (rZComp c)); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2.
case H'2; intros a0 b0.
apply eqStateRzContr with (a := b); auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
Qed.

Theorem eqConstrStateInR :
 forall (S : State) (a b : rZ),
 eqConstrState S a b ->
 a <> b -> ~ (forall a b : rZ, eqStateRz S a b) -> In b (stripRz S).
intros S a b H'; Elimc H'; clear S a b; auto with stalmarck; simpl in |- *.
intros a H'0; case H'0; auto with stalmarck.
intros a b p; case p; intros a' b'; simpl in |- *; auto with stalmarck.
intros S H' H'0 H'1 H'2; right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec c d); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec b d); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec (rZComp c) d); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2 H'3 H'4.
case (rZDec (rZComp b) d); intros Eq1; auto with stalmarck.
right; right; right; right; auto with stalmarck.
intros a b c d S H' H'0 H'1 H'2.
case H'2; intros a0 b0.
apply eqStateRzContr with (a := b); auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
Qed.
(* Given 2 list of signed variable returns the list of all possible equations *)

Fixpoint prodRz (L1 : list rZ) : list rZ -> State :=
  fun L2 : list rZ =>
  match L1 with
  | nil => nil
  | a :: L'1 => map (fun b : rZ => (a, b)) L2 ++ prodRz L'1 L2
  end.

Theorem prodRzProp :
 forall (a b : rZ) (S1 S2 : list rZ),
 In a S1 -> In b S2 -> In (a, b) (prodRz S1 S2).
intros a b S1; elim S1; simpl in |- *; auto with stalmarck.
intros a0 l H' S2 H'0; Elimc H'0; intros H'0; [ rewrite H'0 | idtac ]; auto with stalmarck.
intros H'1; apply in_or_app; auto with stalmarck.
left.
change (In ((fun b0 : rZ => (a, b0)) b) (map (fun b0 : rZ => (a, b0)) S2))
 in |- *.
apply in_map; auto with stalmarck.
intros H'1; apply in_or_app; auto with stalmarck.
Qed.
(* Every non trivial equal is in the product of the strip *)

Theorem eqConstrStateInDouble :
 forall (S : State) (a b : rZ),
 eqConstrState S a b ->
 a <> b ->
 ~ (forall a b : rZ, eqStateRz S a b) ->
 In (a, b) (prodRz (stripRz S) (stripRz S)).
intros S a b H' H'0 H'1.
apply prodRzProp; auto with stalmarck.
apply eqConstrStateInL with (b := b); auto with stalmarck.
apply eqConstrStateInR with (a := a); auto with stalmarck.
Qed.
(* Now we can compute all the non-trivial equation of a state *)

Fixpoint stripRzDec (S1 S2 : State) {struct S2} : State :=
  match S2 with
  | nil => nil
  | (a, b) :: S'2 =>
      match eqConstrStateDec S1 a b with
      | left _ => (a, b) :: stripRzDec S1 S'2
      | right _ => stripRzDec S1 S'2
      end
  end.

Theorem stripRzDecProp1 :
 forall (S1 S2 : State) (a b : rZ),
 In (a, b) (stripRzDec S1 S2) -> In (a, b) S2.
intros S1 S2; elim S2; simpl in |- *; auto with stalmarck.
intros p; case p; auto with stalmarck.
intros c d l H' a b; case (eqConstrStateDec S1 c d); simpl in |- *; auto with stalmarck.
intros H'0 H'1; Elimc H'1; intros H'1;
 [ generalize H'0; inversion H'1 | idtac ]; auto with stalmarck.
Qed.

Theorem stripRzDecProp2 :
 forall (S1 S2 : State) (a b : rZ),
 In (a, b) (stripRzDec S1 S2) -> eqConstrState S1 a b.
intros S1 S2; elim S2; simpl in |- *; auto with stalmarck.
intros a b H'; Elimc H'; clear a b.
intros p; case p; auto with stalmarck.
intros c d l H' a b; case (eqConstrStateDec S1 c d); simpl in |- *; auto with stalmarck.
intros H'0 H'1; Elimc H'1; intros H'1;
 [ generalize H'0; inversion H'1 | idtac ]; auto with stalmarck.
Qed.

Theorem stripRzDecProp3 :
 forall (S1 S2 : State) (a b : rZ),
 In (a, b) S2 -> eqStateRz S1 a b -> In (a, b) (stripRzDec S1 S2).
intros S1 S2; elim S2; simpl in |- *; auto with stalmarck.
intros p; case p; auto with stalmarck.
intros c d l H' a b; case (eqConstrStateDec S1 c d); simpl in |- *; auto with stalmarck.
intros H'0 H'1; Elimc H'1; intros H'1;
 [ generalize H'0; inversion H'1 | idtac ]; auto with stalmarck.
intros H'0 H'1; Elimc H'1; intros H'1;
 [ generalize H'0; inversion H'1 | idtac ]; auto with stalmarck.
intros H'2 H'3; case H'0; auto with stalmarck.
rewrite H0; rewrite H1; auto with stalmarck.
Qed.

(* We compute the intersection by removing of the non-trivial equalities on S2
     those that are not valid in S1 *)

Definition interState (S1 S2 : State) : State :=
  match eqStateRzContrDec S1 with
  | left _ => S2
  | right _ =>
      stripRzDec S2 (stripRzDec S1 (prodRz (stripRz S1) (stripRz S1)))
  end.

Theorem interMemInL : forall S1 S2 : State, inclState (interState S1 S2) S1.
intros S1 S2; unfold interState in |- *.
case (eqStateRzContrDec S1); auto with stalmarck.
intros H'; apply inclStateIn; auto with stalmarck.
intros H'; apply inclStateIn; auto with stalmarck.
intros a b H'1.
apply eqConstrStateImpeqStateRz.
apply stripRzDecProp2 with (S2 := prodRz (stripRz S1) (stripRz S1)); auto with stalmarck.
apply stripRzDecProp1 with (S1 := S2); auto with stalmarck.
Qed.
#[export] Hint Resolve interMemInL : stalmarck.

Theorem interMemInR : forall S1 S2 : State, inclState (interState S1 S2) S2.
intros S1 S2; unfold interState in |- *.
case (eqStateRzContrDec S1); auto with stalmarck.
intros H'; apply inclStateIn; auto with stalmarck.
intros a b H'1.
apply eqConstrStateImpeqStateRz.
apply
 stripRzDecProp2
  with (S2 := stripRzDec S1 (prodRz (stripRz S1) (stripRz S1))); 
 auto with stalmarck.
Qed.
#[export] Hint Resolve interMemInR : stalmarck.

Theorem interMemEqStateRz :
 forall (S1 S2 : State) (a b : rZ),
 eqStateRz S1 a b -> eqStateRz S2 a b -> eqStateRz (interState S1 S2) a b.
intros S1 S2; unfold interState in |- *.
case (eqStateRzContrDec S1); auto with stalmarck.
intros H' a b H'0 H'1; case (rZDec a b); intros Eqab; auto with stalmarck.
rewrite <- Eqab; auto with stalmarck.
apply eqStateRzIn; auto with stalmarck.
repeat apply stripRzDecProp3; auto with stalmarck.
apply eqConstrStateInDouble; auto with stalmarck.
Qed.

Theorem interMemProp :
 forall S1 S2 : State, interStateP S1 S2 (interState S1 S2).
intros S1 S2; repeat split; auto with stalmarck.
intros S4 H1 H2; red in |- *; intros i j H3.
apply interMemEqStateRz; auto with stalmarck.
Qed.

Theorem interMemMin :
 forall S1 S2 S3 : State,
 inclState S3 S1 -> inclState S3 S2 -> inclState S3 (interState S1 S2).
intros S1 S2 S3 H' H'0.
assert (H'2 := interMemProp S1 S2).
apply (interStatePIncl S1 S2); auto with stalmarck.
Qed.
#[export] Hint Resolve interMemMin : stalmarck.

Theorem interStateEq :
 forall S1 S2 S3 S4 : State,
 eqState S1 S3 ->
 eqState S2 S4 -> eqState (interState S1 S2) (interState S3 S4).
intros S1 S2 S3 S4 H' H'0; red in |- *; split; apply interMemMin; auto with stalmarck.
apply inclStateEqStateComp with (S1 := interState S1 S2) (S3 := S1); auto with stalmarck.
apply inclStateEqStateComp with (S1 := interState S1 S2) (S3 := S2); auto with stalmarck.
apply inclStateEqStateComp with (S1 := interState S3 S4) (S3 := S3); auto with stalmarck.
apply inclStateEqStateComp with (S1 := interState S3 S4) (S3 := S4); auto with stalmarck.
Qed.
#[export] Hint Resolve interStateEq : stalmarck.

Theorem interStateSym :
 forall S1 S2 : State, eqState (interState S1 S2) (interState S2 S1).
red in |- *; split; auto with stalmarck.
Qed.
#[export] Hint Immediate interStateSym : stalmarck.

Theorem interAssoc :
 forall S1 S2 S3 : State,
 eqState (interState S1 (interState S2 S3))
   (interState (interState S1 S2) S3).
intros S1 S2 S3; red in |- *; split; auto with stalmarck.
apply interMemMin; auto with stalmarck.
apply interMemMin; auto with stalmarck; apply inclStateTrans with (S2 := interState S2 S3);
 auto with stalmarck.
apply inclStateTrans with (S2 := interState S2 S3); auto with stalmarck.
apply interMemMin; auto with stalmarck.
apply inclStateTrans with (S2 := interState S1 S2); auto with stalmarck.
apply interMemMin; auto with stalmarck.
apply inclStateTrans with (S2 := interState S1 S2); auto with stalmarck.
Qed.
#[export] Hint Resolve interAssoc : stalmarck.

Theorem ContrInterL :
 forall S : State,
 eqState S (interState S ((rZPlus zero, rZMinus zero) :: nil)).
red in |- *; split; auto with stalmarck.
Qed.
#[export] Hint Resolve ContrInterL : stalmarck.

Theorem ContrInterR :
 forall S : State,
 eqState S (interState ((rZPlus zero, rZMinus zero) :: nil) S).
red in |- *; split; auto with stalmarck.
Qed.
#[export] Hint Resolve ContrInterR : stalmarck.
#[export] Hint Resolve eqConstrStateImpeqStateRz : stalmarck.

Theorem CompInterR :
 forall (S : State) (a b : rZ),
 eqState S (interState (addEq (a, b) S) (addEq (a, rZComp b) S)).
red in |- *; split; auto with stalmarck.
red in |- *.
intros i j H'.
cut (eqStateRz (addEq (a, b) S) i j);
 [ intros Eq1
 | apply (interMemInL (addEq (a, b) S) (addEq (a, rZComp b) S) i j) ]; 
 auto with stalmarck.
cut (eqStateRz (addEq (a, rZComp b) S) i j);
 [ intros Eq2
 | apply (interMemInR (addEq (a, b) S) (addEq (a, rZComp b) S) i j) ]; 
 auto with stalmarck.
clear H'.
cut (eqConstrState ((a, b) :: S) i j); [ intros EqC1; inversion EqC1 | auto with stalmarck ].
auto with stalmarck.
cut (eqConstrState ((a, rZComp b) :: S) i j);
 [ intros EqC2; inversion EqC2 | auto with stalmarck ].
auto with stalmarck.
apply eqStateContr with (p := j) (q := b); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := j); auto with stalmarck.
apply eqStateRzTrans with (b := i); auto with stalmarck.
apply eqStateContr with (p := i) (q := a); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := i); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp j); auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
apply eqStateRzTrans with (b := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
cut (eqConstrState ((a, rZComp b) :: S) i j);
 [ intros EqC2; inversion EqC2 | auto with stalmarck ].
auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := i); auto with stalmarck.
apply eqStateRzTrans with (b := j); auto with stalmarck.
apply eqStateContr with (p := i) (q := b); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := j); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp i); auto with stalmarck.
apply eqStateContr with (p := j) (q := a); auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
apply eqStateRzTrans with (b := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
cut (eqConstrState ((a, rZComp b) :: S) i j);
 [ intros EqC2; inversion EqC2 | auto with stalmarck ].
auto with stalmarck.
apply eqStateContr with (p := i) (q := a); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp i); auto with stalmarck.
apply eqStateRzTrans with (b := j); auto with stalmarck.
apply eqStateContr with (p := j) (q := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp j); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp i); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp a); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp b); auto with stalmarck.
cut (eqConstrState ((a, rZComp b) :: S) i j);
 [ intros EqC2; inversion EqC2 | auto with stalmarck ].
auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp j); auto with stalmarck.
apply eqStateRzTrans with (b := i); auto with stalmarck.
apply eqStateContr with (p := j) (q := a); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp i); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp j); auto with stalmarck.
apply eqStateContr with (p := i) (q := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp a); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp b); auto with stalmarck.
cut (eqConstrState ((a, rZComp b) :: S) i j);
 [ intros EqC2; inversion EqC2 | auto with stalmarck ].
auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp b); auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp a); auto with stalmarck.
apply eqStateRzTrans with (b := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
apply eqStateRzTrans with (b := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
apply eqStateRzTrans with (b := rZComp a); auto with stalmarck.
apply eqStateContr with (p := a) (q := b); auto with stalmarck.
rewrite <- (rZCompInv b); auto with stalmarck.
Qed.
