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
Hint Resolve unionStatePDef.

Theorem unionStatePRef : forall S1 : State, unionStateP S1 S1 S1.
auto.
Qed.

Theorem unionStatePSym :
 forall S1 S2 S3 : State, unionStateP S1 S2 S3 -> unionStateP S2 S1 S3.
intros S1 S2 S3 H'; inversion H'; auto.
Qed.

Theorem unionStatePIncl :
 forall S1 S2 S3 S4 : State,
 unionStateP S1 S2 S3 ->
 inclState S1 S4 -> inclState S2 S4 -> inclState S3 S4.
intros S1 S2 S3 S4 H' H'0 H'1; inversion H'; auto.
Qed.

Theorem unionStatePInclSelf :
 forall S1 S2 : State, inclState S2 S1 -> unionStateP S1 S2 S1.
auto.
Qed.

Theorem unionStatePEq :
 forall S1 S2 S'1 S'2 S3 S'3 : State,
 unionStateP S1 S2 S3 ->
 unionStateP S'1 S'2 S'3 ->
 eqState S1 S'1 -> eqState S2 S'2 -> eqState S3 S'3.
intros S1 S2 S'1 S'2 S3 S'3 H' H'0; inversion H'; inversion H'0; auto.
intros H'1 H'2; red in |- *; split; auto.
apply H1; auto.
apply inclStateEqStateComp with (S1 := S'1) (S3 := S'3); auto.
apply inclStateEqStateComp with (S1 := S'2) (S3 := S'3); auto.
apply H7; auto.
apply inclStateEqStateComp with (S1 := S1) (S3 := S3); auto.
apply inclStateEqStateComp with (S1 := S2) (S3 := S3); auto.
Qed.

Theorem unionStatePEqComp :
 forall S1 S2 S3 S'1 S'2 S'3 : State,
 unionStateP S1 S2 S3 ->
 eqState S1 S'1 ->
 eqState S2 S'2 -> eqState S3 S'3 -> unionStateP S'1 S'2 S'3.
intros S1 S2 S3 S'1 S'2 S'3 H' H'0 H'1 H'2.
apply unionStatePDef; auto.
apply inclStateEqStateComp with (S1 := S1) (S3 := S3); auto.
inversion H'; auto.
apply inclStateEqStateComp with (S1 := S2) (S3 := S3); auto.
inversion H'; auto.
intros S4 H'3 H'4.
apply inclStateEqStateComp with (S1 := S3) (S3 := S4); auto.
inversion H'; auto.
apply H1; auto.
apply inclStateEqStateComp with (S1 := S'1) (S3 := S4); auto.
apply inclStateEqStateComp with (S1 := S'2) (S3 := S4); auto.
Qed.

Theorem unionStateAssoc1 :
 forall S1 S2 S3 S'1 S'2 S'3 : State,
 unionStateP S1 S2 S'1 ->
 unionStateP S'1 S3 S'2 -> unionStateP S2 S3 S'3 -> unionStateP S1 S'3 S'2.
intros S1 S2 S3 S'1 S'2 S'3 H' H'0 H'1.
apply unionStatePDef; auto.
apply inclStateTrans with (S2 := S'1); auto.
inversion H'; auto.
inversion H'0; auto.
apply unionStatePIncl with (1 := H'1); auto.
apply inclStateTrans with (S2 := S'1); auto.
inversion H'; auto.
inversion H'0; auto.
inversion H'0; auto.
intros S4 H'2 H'3.
apply unionStatePIncl with (1 := H'0); auto.
apply unionStatePIncl with (1 := H'); auto.
apply inclStateTrans with (S2 := S'3); auto.
inversion H'1; auto.
apply inclStateTrans with (S2 := S'3); auto.
inversion H'1; auto.
Qed.

Theorem unionStatePAssoc2 :
 forall S1 S2 S3 S'1 S'2 S'3 : State,
 unionStateP S2 S3 S'1 ->
 unionStateP S1 S'1 S'2 -> unionStateP S1 S2 S'3 -> unionStateP S'3 S3 S'2.
intros S1 S2 S3 S'1 S'2 S'3 H' H'0 H'1.
apply unionStatePDef; auto.
apply unionStatePIncl with (1 := H'1); auto.
inversion H'0; auto.
apply inclStateTrans with (S2 := S'1); auto.
inversion H'; auto.
inversion H'0; auto.
apply inclStateTrans with (S2 := S'1); auto.
inversion H'; auto.
inversion H'0; auto.
intros S4 H'2 H'3.
apply unionStatePIncl with (1 := H'0); auto.
apply inclStateTrans with (S2 := S'3); auto.
inversion H'1; auto.
apply unionStatePIncl with (1 := H'); auto.
apply inclStateTrans with (S2 := S'3); auto.
inversion H'1; auto.
Qed.

Theorem addEqUnion :
 forall (S : State) (p q : rZ),
 unionStateP ((p, q) :: nil) S (addEq (p, q) S).
intros S p q.
apply unionStatePDef; auto.
apply inclStateIn; simpl in |- *; auto.
intros a b H'; elim H'; intros H'0; inversion H'0; auto.
intros S4 H' H'0.
apply inclStateAddEqInv; auto.
apply eqStateIncl with (S1 := (p, q) :: nil); auto with datatypes.
Qed.

(* To compute of two states, one simply needs to append the two list of equations *)

Definition unionState (S1 S2 : State) := S1 ++ S2.

Theorem unionStatePunionState :
 forall S1 S2 : State, unionStateP S1 S2 (unionState S1 S2).
intros S1; elim S1; simpl in |- *; auto.
intros S2.
apply unionStatePSym; auto.
apply unionStatePInclSelf; auto.
apply inclStateIn; simpl in |- *; auto.
intros a b H'; elim H'; auto.
intros p l H' S2; case p; intros a b.
apply
 unionStatePAssoc2
  with (S1 := (a, b) :: nil) (S2 := l) (S'1 := unionState l S2); 
 auto.
generalize addEqUnion; unfold addEq in |- *; auto.
generalize addEqUnion; unfold addEq in |- *; auto.
Qed.

Theorem unionStateInclL :
 forall S1 S2 : State, inclState S1 (unionState S1 S2).
intros S1 S2.
specialize  2unionStatePunionState with (S1 := S1) (S2 := S2); intros H'0;
 inversion H'0; auto.
Qed.
Hint Resolve unionStateInclL.

Theorem unionStateInclR :
 forall S1 S2 : State, inclState S2 (unionState S1 S2).
intros S1 S2.
specialize  2unionStatePunionState with (S1 := S1) (S2 := S2); intros H'0;
 inversion H'0; auto.
Qed.
Hint Resolve unionStateInclR.

Theorem unionStateMin :
 forall S1 S2 S3 : State,
 inclState S1 S3 -> inclState S2 S3 -> inclState (unionState S1 S2) S3.
intros S1 S2 S3 H' H'0.
specialize  2unionStatePunionState with (S1 := S1) (S2 := S2); intros H'1;
 inversion H'1; auto.
Qed.
Hint Resolve unionStateMin.

Theorem unionStateSym :
 forall S1 S2 : State, eqState (unionState S1 S2) (unionState S2 S1).
intros S1 S2; red in |- *; split; auto.
Qed.
Hint Immediate unionStateSym.

Theorem unionStateEq :
 forall S1 S2 S3 S4 : State,
 eqState S1 S3 ->
 eqState S2 S4 -> eqState (unionState S1 S2) (unionState S3 S4).
intros S1 S2 S3 S4 H' H'0; red in |- *; split; auto.
apply unionStateMin; auto.
apply inclStateEqStateComp with (S1 := S3) (S3 := unionState S3 S4); auto.
apply inclStateEqStateComp with (S1 := S4) (S3 := unionState S3 S4); auto.
apply unionStateMin; auto.
apply inclStateEqStateComp with (S1 := S1) (S3 := unionState S1 S2); auto.
apply inclStateEqStateComp with (S1 := S2) (S3 := unionState S1 S2); auto.
Qed.
Hint Resolve unionStateEq.

Theorem unionStateAssoc :
 forall S1 S2 S3 : State,
 eqState (unionState S1 (unionState S2 S3))
   (unionState (unionState S1 S2) S3).
intros S1 S2 S3; red in |- *; split.
apply unionStateMin; auto.
apply inclStateTrans with (S2 := unionState S1 S2); auto.
apply unionStateMin; auto.
apply inclStateTrans with (S2 := unionState S1 S2); auto.
apply unionStateMin; auto.
apply unionStateMin; auto.
apply inclStateTrans with (S2 := unionState S2 S3); auto.
apply inclStateTrans with (S2 := unionState S2 S3); auto.
Qed.
Hint Resolve unionStateMin.