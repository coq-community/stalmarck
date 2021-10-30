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

(**************************************************************************
                                                                           
          Stalmarck  :  trace                                              
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of trace to represent stalmarck's computation
*)

Require Export stalmarck.

Inductive Trace : Set :=
  | emptyTrace : Trace
  | tripletTrace : triplet -> Trace
  | seqTrace : Trace -> Trace -> Trace
  | dilemmaTrace : rZ -> rZ -> Trace -> Trace -> Trace.

Inductive evalTrace : State -> Trace -> State -> Prop :=
  | emptyTraceEval :
      forall S1 S2 : State, eqState S1 S2 -> evalTrace S1 emptyTrace S2
  | tripletTraceEval :
      forall (t : triplet) (S1 S2 S3 : State),
      doTripletP S1 t S2 -> eqState S2 S3 -> evalTrace S1 (tripletTrace t) S3
  | seqTraceEval :
      forall (t1 t2 : Trace) (S1 S2 S3 : State),
      evalTrace S1 t1 S2 ->
      evalTrace S2 t2 S3 -> evalTrace S1 (seqTrace t1 t2) S3
  | dilemmaTraceEval :
      forall (t1 t2 : Trace) (a b : rZ) (S1 S2 S3 S4 : State),
      evalTrace (addEq (a, b) S1) t1 S2 ->
      evalTrace (addEq (a, rZComp b) S1) t2 S3 ->
      eqState (interState S2 S3) S4 ->
      evalTrace S1 (dilemmaTrace a b t1 t2) S4.
#[export] Hint Resolve emptyTraceEval tripletTraceEval : stalmarck.

Theorem evalTraceEq :
 forall (S1 S2 : State) (t : Trace),
 evalTrace S1 t S2 ->
 forall S3 S4 : State, evalTrace S3 t S4 -> eqState S1 S3 -> eqState S2 S4.
intros S1 S2 t H'; elim H'; clear H' t S2 S1; auto with stalmarck.
intros S1 S2 H' S3 S4 H'0; inversion H'0; auto with stalmarck.
intros H'1.
apply eqStateTrans with (S2 := S1); auto with stalmarck.
apply eqStateTrans with (S2 := S3); auto with stalmarck.
intros t S1 S2 S3 H' H'0 S4 S5 H'1 H'2; inversion H'1; auto with stalmarck.
apply eqStateTrans with (S2 := S2); auto with stalmarck.
apply eqStateTrans with (S2 := S6); auto with stalmarck.
apply doTripletEqComp with (t := t) (S1 := S1) (S2 := S4); auto with stalmarck.
intros t1 t2 S1 S2 S3 H' H'0 H'1 H'2 S0 S4 H'3; inversion H'3; auto with stalmarck.
intros H'4.
apply (H'2 S6); auto with stalmarck.
apply H'0 with (S3 := S0); auto with stalmarck.
intros t1 t2 a b S1 S2 S3 S4 H' H'0 H'1 H'2 H'3 S0 S5 H'4; inversion H'4;
 auto with stalmarck.
intros H'5.
apply eqStateTrans with (S2 := interState S7 S8); auto with stalmarck.
apply eqStateTrans with (S2 := interState S2 S3); auto with stalmarck.
apply interStateEq; auto with stalmarck.
apply H'0 with (S3 := addEq (a, b) S0); auto with stalmarck.
apply (H'2 (addEq (a, rZComp b) S0)); auto with stalmarck.
Qed.

Theorem evalTraceComp :
 forall (S1 S2 : State) (t : Trace),
 evalTrace S1 t S2 ->
 forall S3 S4 : State, eqState S1 S3 -> eqState S2 S4 -> evalTrace S3 t S4.
intros S1 S2 t H'; elim H'; clear H' t S2 S1; auto with stalmarck.
intros S1 S2 H' S3 S4 H'0 H'1.
apply emptyTraceEval; auto with stalmarck.
apply eqStateTrans with (S2 := S1); auto with stalmarck.
apply eqStateTrans with (S2 := S2); auto with stalmarck.
intros t S1 S2 S3 H' H'0 S4 S5 H'1 H'2.
case (doTripletEqCompEx S1 S2 S4 t); auto with stalmarck.
intros S6 H'3; elim H'3; intros H'4 H'5; clear H'3.
apply tripletTraceEval with (S2 := S6); auto with stalmarck.
apply eqStateTrans with (S2 := S2); auto with stalmarck.
apply eqStateTrans with (S2 := S3); auto with stalmarck.
intros t1 t2 S1 S2 S3 H' H'0 H'1 H'2 S4 S5 H'3 H'4.
apply seqTraceEval with (S2 := S2); auto with stalmarck.
intros t1 t2 a b S1 S2 S3 S4 H' H'0 H'1 H'2 H'3 S5 S6 H'4 H'5.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
apply eqStateTrans with (S2 := S4); auto with stalmarck.
Qed.

Fixpoint TraceInList (T : Trace) : list triplet -> Prop :=
  fun L : list triplet =>
  match T with
  | emptyTrace => True
  | tripletTrace t => In t L
  | seqTrace T1 T2 => TraceInList T1 L /\ TraceInList T2 L
  | dilemmaTrace a b T1 T2 => TraceInList T1 L /\ TraceInList T2 L
  end.

Theorem doTripletsExTrace :
 forall (L : list triplet) (S1 S2 : State),
 doTripletsP S1 L S2 ->
 exists t : Trace, evalTrace S1 t S2 /\ TraceInList t L.
intros L S1 S2 H'; elim H'; clear H' S1 S2 L.
intros S1 S2 H' H'0; exists emptyTrace; simpl in |- *; auto with stalmarck.
intros S1 S2 S3 L t H' H'0 H'1 H'2; elim H'2; intros t0 E; elim E;
 intros H'3 H'4; clear E H'2.
exists (seqTrace (tripletTrace t) t0); simpl in |- *; repeat split; auto with stalmarck.
apply seqTraceEval with (S2 := S2); auto with stalmarck.
apply tripletTraceEval with (S2 := S2); auto with stalmarck.
Qed.

Theorem stalmarckExTrace :
 forall (L : list triplet) (S1 S2 : State),
 stalmarckP S1 L S2 -> exists t : Trace, evalTrace S1 t S2 /\ TraceInList t L.
intros L S1 S2 H'; elim H'; clear H' S2 S1 L; auto with stalmarck.
intros S1 S2 L H'; apply doTripletsExTrace with (L := L); auto with stalmarck.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3.
elim H'0; intros t E; elim E; intros H'4 H'5; clear E H'0.
elim H'2; intros t0 E; elim E; intros H'0 H'6; clear E H'2.
exists (dilemmaTrace a b t t0); simpl in |- *; repeat split; auto with stalmarck.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
intros S1 S2 S3 L H' H'0 H'1 H'2.
elim H'0; intros t E; elim E; intros H'4 H'5; clear E H'0.
elim H'2; intros t0 E; elim E; intros H'0 H'6; clear E H'2.
exists (seqTrace t t0); simpl in |- *; repeat split; auto with stalmarck.
apply seqTraceEval with (S2 := S2); auto with stalmarck.
Qed.
