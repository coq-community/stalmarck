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
                                                                           
          Stalmarck  :   unionState                                        
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of the union of two states *)
Require Import List.
Require Export state.
(* The property of being an union *)

Inductive unionStateP : State -> State -> State -> Prop :=
    unionStatePDef :
      forall S1 S2 S3 : State,
      inclState S1 S3 ->
      inclState S2 S3 ->
      (forall S4 : State,
       inclState S1 S4 -> inclState S2 S4 -> inclState S3 S4) ->
      unionStateP S1 S2 S3.
Global Hint Resolve unionStatePDef : stalmarck.

Theorem unionStatePRef : forall S1 : State, unionStateP S1 S1 S1.
auto with stalmarck.
Qed.

Theorem unionStatePSym :
 forall S1 S2 S3 : State, unionStateP S1 S2 S3 -> unionStateP S2 S1 S3.
intros S1 S2 S3 H'; inversion H'; auto with stalmarck.
Qed.

Theorem unionStatePIncl :
 forall S1 S2 S3 S4 : State,
 unionStateP S1 S2 S3 ->
 inclState S1 S4 -> inclState S2 S4 -> inclState S3 S4.
intros S1 S2 S3 S4 H' H'0 H'1; inversion H'; auto with stalmarck.
Qed.

Theorem unionStatePInclSelf :
 forall S1 S2 : State, inclState S2 S1 -> unionStateP S1 S2 S1.
auto with stalmarck.
Qed.

Theorem unionStatePEq :
 forall S1 S2 S'1 S'2 S3 S'3 : State,
 unionStateP S1 S2 S3 ->
 unionStateP S'1 S'2 S'3 ->
 eqState S1 S'1 -> eqState S2 S'2 -> eqState S3 S'3.
intros S1 S2 S'1 S'2 S3 S'3 H' H'0; inversion H'; inversion H'0; auto with stalmarck.
intros H'1 H'2; red in |- *; split; auto with stalmarck.
apply H1; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S'1) (S3 := S'3); auto with stalmarck.
apply inclStateEqStateComp with (S1 := S'2) (S3 := S'3); auto with stalmarck.
apply H7; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S1) (S3 := S3); auto with stalmarck.
apply inclStateEqStateComp with (S1 := S2) (S3 := S3); auto with stalmarck.
Qed.

Theorem unionStatePEqComp :
 forall S1 S2 S3 S'1 S'2 S'3 : State,
 unionStateP S1 S2 S3 ->
 eqState S1 S'1 ->
 eqState S2 S'2 -> eqState S3 S'3 -> unionStateP S'1 S'2 S'3.
intros S1 S2 S3 S'1 S'2 S'3 H' H'0 H'1 H'2.
apply unionStatePDef; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S1) (S3 := S3); auto with stalmarck.
inversion H'; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S2) (S3 := S3); auto with stalmarck.
inversion H'; auto with stalmarck.
intros S4 H'3 H'4.
apply inclStateEqStateComp with (S1 := S3) (S3 := S4); auto with stalmarck.
inversion H'; auto with stalmarck.
apply H1; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S'1) (S3 := S4); auto with stalmarck.
apply inclStateEqStateComp with (S1 := S'2) (S3 := S4); auto with stalmarck.
Qed.

Theorem unionStateAssoc1 :
 forall S1 S2 S3 S'1 S'2 S'3 : State,
 unionStateP S1 S2 S'1 ->
 unionStateP S'1 S3 S'2 -> unionStateP S2 S3 S'3 -> unionStateP S1 S'3 S'2.
intros S1 S2 S3 S'1 S'2 S'3 H' H'0 H'1.
apply unionStatePDef; auto with stalmarck.
apply inclStateTrans with (S2 := S'1); auto with stalmarck.
inversion H'; auto with stalmarck.
inversion H'0; auto with stalmarck.
apply unionStatePIncl with (1 := H'1); auto with stalmarck.
apply inclStateTrans with (S2 := S'1); auto with stalmarck.
inversion H'; auto with stalmarck.
inversion H'0; auto with stalmarck.
inversion H'0; auto with stalmarck.
intros S4 H'2 H'3.
apply unionStatePIncl with (1 := H'0); auto with stalmarck.
apply unionStatePIncl with (1 := H'); auto with stalmarck.
apply inclStateTrans with (S2 := S'3); auto with stalmarck.
inversion H'1; auto with stalmarck.
apply inclStateTrans with (S2 := S'3); auto with stalmarck.
inversion H'1; auto with stalmarck.
Qed.

Theorem unionStatePAssoc2 :
 forall S1 S2 S3 S'1 S'2 S'3 : State,
 unionStateP S2 S3 S'1 ->
 unionStateP S1 S'1 S'2 -> unionStateP S1 S2 S'3 -> unionStateP S'3 S3 S'2.
intros S1 S2 S3 S'1 S'2 S'3 H' H'0 H'1.
apply unionStatePDef; auto with stalmarck.
apply unionStatePIncl with (1 := H'1); auto with stalmarck.
inversion H'0; auto with stalmarck.
apply inclStateTrans with (S2 := S'1); auto with stalmarck.
inversion H'; auto with stalmarck.
inversion H'0; auto with stalmarck.
apply inclStateTrans with (S2 := S'1); auto with stalmarck.
inversion H'; auto with stalmarck.
inversion H'0; auto with stalmarck.
intros S4 H'2 H'3.
apply unionStatePIncl with (1 := H'0); auto with stalmarck.
apply inclStateTrans with (S2 := S'3); auto with stalmarck.
inversion H'1; auto with stalmarck.
apply unionStatePIncl with (1 := H'); auto with stalmarck.
apply inclStateTrans with (S2 := S'3); auto with stalmarck.
inversion H'1; auto with stalmarck.
Qed.

Theorem addEqUnion :
 forall (S : State) (p q : rZ),
 unionStateP ((p, q) :: nil) S (addEq (p, q) S).
intros S p q.
apply unionStatePDef; auto with stalmarck.
apply inclStateIn; simpl in |- *; auto with stalmarck.
intros a b H'; elim H'; intros H'0; inversion H'0; auto with stalmarck.
Qed.

(* To compute of two states, one simply needs to append the two list of equations *)

Definition unionState (S1 S2 : State) := S1 ++ S2.

Theorem unionStatePunionState :
 forall S1 S2 : State, unionStateP S1 S2 (unionState S1 S2).
intros S1; elim S1; simpl in |- *; auto with stalmarck.
intros S2.
apply unionStatePSym; auto with stalmarck.
apply unionStatePInclSelf; auto with stalmarck.
apply inclStateIn; simpl in |- *; auto with stalmarck.
intros a b H'; elim H'; auto with stalmarck.
intros p l H' S2; case p; intros a b.
apply
 unionStatePAssoc2
  with (S1 := (a, b) :: nil) (S2 := l) (S'1 := unionState l S2); 
 auto with stalmarck.
generalize addEqUnion; unfold addEq in |- *; auto with stalmarck.
generalize addEqUnion; unfold addEq in |- *; auto with stalmarck.
Qed.

Theorem unionStateInclL :
 forall S1 S2 : State, inclState S1 (unionState S1 S2).
intros S1 S2.
destruct (unionStatePunionState S1 S2); auto with stalmarck.
Qed.
Global Hint Resolve unionStateInclL : stalmarck.

Theorem unionStateInclR :
 forall S1 S2 : State, inclState S2 (unionState S1 S2).
intros S1 S2.
destruct (unionStatePunionState S1 S2); auto with stalmarck.
Qed.
Global Hint Resolve unionStateInclR : stalmarck.

Theorem unionStateMin :
 forall S1 S2 S3 : State,
 inclState S1 S3 -> inclState S2 S3 -> inclState (unionState S1 S2) S3.
intros S1 S2 S3 H' H'0.
destruct (unionStatePunionState S1 S2); auto with stalmarck.
Qed.
Global Hint Resolve unionStateMin : stalmarck.

Theorem unionStateSym :
 forall S1 S2 : State, eqState (unionState S1 S2) (unionState S2 S1).
intros S1 S2; red in |- *; split; auto with stalmarck.
Qed.
Global Hint Immediate unionStateSym : stalmarck.

Theorem unionStateEq :
 forall S1 S2 S3 S4 : State,
 eqState S1 S3 ->
 eqState S2 S4 -> eqState (unionState S1 S2) (unionState S3 S4).
intros S1 S2 S3 S4 H' H'0; red in |- *; split; auto with stalmarck.
apply unionStateMin; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S3) (S3 := unionState S3 S4); auto with stalmarck.
apply inclStateEqStateComp with (S1 := S4) (S3 := unionState S3 S4); auto with stalmarck.
apply unionStateMin; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S1) (S3 := unionState S1 S2); auto with stalmarck.
apply inclStateEqStateComp with (S1 := S2) (S3 := unionState S1 S2); auto with stalmarck.
Qed.
Global Hint Resolve unionStateEq : stalmarck.

Theorem unionStateAssoc :
 forall S1 S2 S3 : State,
 eqState (unionState S1 (unionState S2 S3))
   (unionState (unionState S1 S2) S3).
intros S1 S2 S3; red in |- *; split.
apply unionStateMin; auto with stalmarck.
apply inclStateTrans with (S2 := unionState S1 S2); auto with stalmarck.
apply unionStateMin; auto with stalmarck.
apply inclStateTrans with (S2 := unionState S1 S2); auto with stalmarck.
apply unionStateMin; auto with stalmarck.
apply unionStateMin; auto with stalmarck.
apply inclStateTrans with (S2 := unionState S2 S3); auto with stalmarck.
apply inclStateTrans with (S2 := unionState S2 S3); auto with stalmarck.
Qed.
Global Hint Resolve unionStateMin : stalmarck.
