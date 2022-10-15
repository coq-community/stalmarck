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

(** * algoDotriplet

Pierre Letouzey & Laurent Thery

Implement the one step propagation
*)

From Stalmarck Require Export memoryImplement.
From Stalmarck Require Export triplet.
From Stalmarck Require Import interState doTriplet.

Section algo.

(** We simply check the applicability of each rule sequentially,
   the test is made with the miniaml element *)
Definition doTripletF : forall (Ar : rArray vM) (t : triplet), option mbD.
intros Ar t.
case t; intros b p q r.
apply letP with (1 := evalZ Ar p); intros p'.
apply letP with (1 := evalZ Ar q); intros q'.
apply letP with (1 := evalZ Ar r); intros r'.
case b.
case (rZDec p' (rZComp q')); intros Eq1.
exact (Some (addEqMem2 Ar r' rZFalse q' rZTrue)).
case (rZDec p' (rZComp r')); intros Eq2.
exact (Some (addEqMem2 Ar r' rZTrue q' rZFalse)).
case (rZDec q' r'); intros Eq3.
exact (Some (addEqMem Ar p' r')).
case (rZDec q' (rZComp r')); intros Eq4.
exact (Some (addEqMem Ar p' rZFalse)).
case (rZDec p' rZTrue); intros Eq5.
exact (Some (addEqMem2 Ar r' rZTrue q' rZTrue)).
case (rZDec q' rZTrue); intros Eq6.
exact (Some (addEqMem Ar p' r')).
case (rZDec q' rZFalse); intros Eq7.
exact (Some (addEqMem Ar p' rZFalse)).
case (rZDec r' rZTrue); intros Eq8.
exact (Some (addEqMem Ar p' q')).
case (rZDec r' rZFalse); intros Eq9.
exact (Some (addEqMem Ar p' rZFalse)).
exact None.
case (rZDec p' q'); intros Eq1.
exact (Some (addEqMem Ar r' rZTrue)).
case (rZDec p' (rZComp q')); intros Eq2.
exact (Some (addEqMem Ar r' rZFalse)).
case (rZDec p' r'); intros Eq3.
exact (Some (addEqMem Ar q' rZTrue)).
case (rZDec p' (rZComp r')); intros Eq4.
exact (Some (addEqMem Ar q' rZFalse)).
case (rZDec q' r'); intros Eq5.
exact (Some (addEqMem Ar p' rZTrue)).
case (rZDec q' (rZComp r')); intros Eq6.
exact (Some (addEqMem Ar p' rZFalse)).
case (rZDec p' rZTrue); intros Eq7.
exact (Some (addEqMem Ar q' r')).
case (rZDec p' rZFalse); intros Eq8.
exact (Some (addEqMem Ar q' (rZComp r'))).
case (rZDec q' rZTrue); intros Eq9.
exact (Some (addEqMem Ar p' r')).
case (rZDec q' rZFalse); intros Eq10.
exact (Some (addEqMem Ar p' (rZComp r'))).
case (rZDec r' rZTrue); intros Eq11.
exact (Some (addEqMem Ar p' q')).
case (rZDec r' rZFalse); intros Eq12.
exact (Some (addEqMem Ar p' (rZComp q'))).
exact None.
Defined.

Theorem contradictoryEq :
 forall S1 S2 : State, contradictory S1 -> eqState S1 S2 -> contradictory S2.
Proof.
intros S1 S2 H' H'0; inversion H'.
exists x; auto with stalmarck.
apply eqStateEq with (S1 := S1); auto with stalmarck.
Qed.

Theorem eqStateEvalZ :
 forall (Ar : rArray vM) (S : State) (q : rZ),
 wellFormedArray Ar -> rArrayState Ar S -> eqStateRz S (evalZ Ar q) q.
Proof.
intros Ar S q H' H'0.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply evalZInv; auto with stalmarck.
Qed.

Theorem eqStateEq1 :
 forall (S : State) (q r s t : rZ),
 eqStateRz S q s ->
 eqStateRz S r t -> eqState (addEq (q, r) S) (addEq (s, t) S).
Proof.
intros S q r s t Eq1 Eq2; split.
apply inclStateIn; simpl in |- *; auto with stalmarck.
intros a b H'0; Elimc H'0; intros H'0; auto with stalmarck.
inversion H'0; clear H'0; auto with stalmarck.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := s); auto with stalmarck.
apply eqStateRzTrans with (b := t); auto with stalmarck.
apply inclStateIn; simpl in |- *; auto with stalmarck.
intros a b H'0; Elimc H'0; intros H'0; auto with stalmarck.
inversion H'0; clear H'0.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := q); auto with stalmarck.
Qed.

Theorem eqStateEqEvalZ :
 forall (Ar : rArray vM) (S : State) (q r : rZ),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 eqState (addEq (evalZ Ar q, evalZ Ar r) S) (addEq (q, r) S).
Proof.
intros Ar S q r H' H'0.
apply eqStateEq1; auto with stalmarck.
apply eqStateEvalZ; auto with stalmarck.
apply eqStateEvalZ; auto with stalmarck.
Qed.

Theorem eqStateEq2 :
 forall (S : State) (q r s t u v w x : rZ),
 eqStateRz S q s ->
 eqStateRz S r t ->
 eqStateRz S u w ->
 eqStateRz S v x ->
 eqState (addEq (q, r) (addEq (u, v) S)) (addEq (s, t) (addEq (w, x) S)).
Proof.
intros S q r s t u v w x Eq1 Eq2 Eq3 Eq4; split.
apply inclStateIn; simpl in |- *; auto with stalmarck.
intros a b H'0; Elimc H'0; intros H'0; auto with stalmarck.
inversion H'0; clear H'0; auto with stalmarck.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := s); auto with stalmarck.
apply eqStateRzTrans with (b := t); auto with stalmarck.
Elimc H'0; intros H'0; auto with stalmarck.
inversion H'0; clear H'0; auto with stalmarck.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := w); auto with stalmarck.
apply eqStateRzTrans with (b := x); auto with stalmarck.
apply inclStateIn; simpl in |- *; auto with stalmarck.
intros a b H'0; Elimc H'0; intros H'0; auto with stalmarck.
inversion H'0; clear H'0; auto with stalmarck.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := q); auto with stalmarck.
Elimc H'0; intros H'0; auto with stalmarck.
inversion H'0; clear H'0; auto with stalmarck.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := u); auto with stalmarck.
Qed.

Theorem eqStateEq2EvalZ :
 forall (Ar : rArray vM) (S : State) (q r s t : rZ),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 eqState (addEq (evalZ Ar q, evalZ Ar r) (addEq (evalZ Ar s, evalZ Ar t) S))
   (addEq (q, r) (addEq (s, t) S)).
Proof.
intros Ar S q r s t H' H'0.
apply eqStateEq2; auto with stalmarck.
apply eqStateEvalZ; auto with stalmarck.
apply eqStateEvalZ; auto with stalmarck.
apply eqStateEvalZ; auto with stalmarck.
apply eqStateEvalZ; auto with stalmarck.
Qed.

(** The implementation is correct *)
Theorem doTripletFCorrect :
 forall (Ar : rArray vM) (t : triplet) (S : State),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 match doTripletF Ar t with
 | None => forall S' : State, ~ doTripletP S t S'
 | Some (triple Ar' false L) =>
     wellFormedArray Ar' /\
     (exists S' : State, doTripletP S t S' /\ rArrayState Ar' S') /\
     OlistRz L /\
     (forall e : rNat,
      ~ InRz (rZPlus e) L -> rArrayGet _ Ar' e = rArrayGet _ Ar e)
 | Some (triple Ar' true L) =>
     exists S' : State, doTripletP S t S' /\ contradictory S'
 end.
Proof.
intros Ar t S H' H'0; unfold doTripletF, letP in |- *.
case t.
intros b p q r; case b.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar q))); intros Eq0.
generalize (addEqMem2Correct Ar (evalZ Ar r) rZFalse (evalZ Ar q) rZTrue);
 case (addEqMem2 Ar (evalZ Ar r) rZFalse (evalZ Ar q) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZTrue) (addEq (r, rZFalse) S)); 
 split; auto with stalmarck.
apply doTripletAndPpmq; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq2; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, rZTrue) (addEq (r, rZFalse) S)); split; auto with stalmarck.
apply doTripletAndPpmq; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq2; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar r))); intros Eq1.
generalize (addEqMem2Correct Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZFalse);
 case (addEqMem2 Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZFalse) (addEq (r, rZTrue) S)); 
 split; auto with stalmarck.
apply doTripletAndPpmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq2; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, rZFalse) (addEq (r, rZTrue) S)); split; auto with stalmarck.
apply doTripletAndPpmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq2; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) (evalZ Ar r)); intros Eq2.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, r) S);
 split; auto with stalmarck.
apply doTripletAndPqr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, r) S); split; auto with stalmarck.
apply doTripletAndPqr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) (rZComp (evalZ Ar r))); intros Eq3.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletAndPqmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletAndPqmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) rZTrue); intros Eq4.
generalize (addEqMem2Correct Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZTrue);
 case (addEqMem2 Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZTrue) (addEq (r, rZTrue) S)); 
 split; auto with stalmarck.
apply doTripletAndPpT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq2; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, rZTrue) (addEq (r, rZTrue) S)); split; auto with stalmarck.
apply doTripletAndPpT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq2; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) rZTrue); intros Eq5.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, r) S);
 split; auto with stalmarck.
apply doTripletAndPqT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, r) S); split; auto with stalmarck.
apply doTripletAndPqT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) rZFalse); intros Eq6.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletAndPqF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletAndPqF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar r) rZTrue); intros Eq7.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar q));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar q)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, q) S);
 split; auto with stalmarck.
apply doTripletAndPrT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, q) S); split; auto with stalmarck.
apply doTripletAndPrT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar r) rZFalse); intros Eq8.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletAndPrF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletAndPrF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros S'; red in |- *; intros H'1; inversion H'1; auto with stalmarck.
Contradict Eq0; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto with stalmarck.
Contradict Eq1; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto with stalmarck.
Contradict Eq2; apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq3; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto with stalmarck.
Contradict Eq4; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq5; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq6; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq7; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq8; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
case (rZDec (evalZ Ar p) (evalZ Ar q)); intros Eq0.
generalize (addEqMemCorrect Ar (evalZ Ar r) rZTrue);
 case (addEqMem Ar (evalZ Ar r) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (r, rZTrue) S); split; auto with stalmarck.
apply doTripletEqPpq; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (r, rZTrue) S); split; auto with stalmarck.
apply doTripletEqPpq; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar q))); intros Eq1.
generalize (addEqMemCorrect Ar (evalZ Ar r) rZFalse);
 case (addEqMem Ar (evalZ Ar r) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (r, rZFalse) S); split; auto with stalmarck.
apply doTripletEqPpmq; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (r, rZFalse) S); split; auto with stalmarck.
apply doTripletEqPpmq; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) (evalZ Ar r)); intros Eq2.
generalize (addEqMemCorrect Ar (evalZ Ar q) rZTrue);
 case (addEqMem Ar (evalZ Ar q) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZTrue) S); split; auto with stalmarck.
apply doTripletEqPpr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, rZTrue) S); split; auto with stalmarck.
apply doTripletEqPpr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar r))); intros Eq3.
generalize (addEqMemCorrect Ar (evalZ Ar q) rZFalse);
 case (addEqMem Ar (evalZ Ar q) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZFalse) S); split; auto with stalmarck.
apply doTripletEqPpmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, rZFalse) S); split; auto with stalmarck.
apply doTripletEqPpmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) (evalZ Ar r)); intros Eq4.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZTrue);
 case (addEqMem Ar (evalZ Ar p) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZTrue) S); split; auto with stalmarck.
apply doTripletEqPqr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZTrue) S); split; auto with stalmarck.
apply doTripletEqPqr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) (rZComp (evalZ Ar r))); intros Eq5.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletEqPqmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZFalse) S); split; auto with stalmarck.
apply doTripletEqPqmr; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZComp; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) rZTrue); intros Eq6.
generalize (addEqMemCorrect Ar (evalZ Ar q) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar q) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (q, r) S);
 split; auto with stalmarck.
apply doTripletEqPpT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, r) S); split; auto with stalmarck.
apply doTripletEqPpT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar p) rZFalse); intros Eq7.
generalize (addEqMemCorrect Ar (evalZ Ar q) (rZComp (evalZ Ar r)));
 case (addEqMem Ar (evalZ Ar q) (rZComp (evalZ Ar r))).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZComp r) S); split; auto with stalmarck.
apply doTripletEqPpF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; try apply eqStateRzInv; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (q, rZComp r) S); split; auto with stalmarck.
apply doTripletEqPpF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; try apply eqStateRzInv; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) rZTrue); intros Eq8.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, r) S);
 split; auto with stalmarck.
apply doTripletEqPqT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, r) S); split; auto with stalmarck.
apply doTripletEqPqT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar q) rZFalse); intros Eq9.
generalize (addEqMemCorrect Ar (evalZ Ar p) (rZComp (evalZ Ar r)));
 case (addEqMem Ar (evalZ Ar p) (rZComp (evalZ Ar r))).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZComp r) S); split; auto with stalmarck.
apply doTripletEqPqF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; try apply eqStateRzInv; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZComp r) S); split; auto with stalmarck.
apply doTripletEqPqF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; try apply eqStateRzInv; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar r) rZTrue); intros Eq10.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar q));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar q)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, q) S);
 split; auto with stalmarck.
apply doTripletEqPrT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, q) S); split; auto with stalmarck.
apply doTripletEqPrT; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZTrue; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; apply eqStateEvalZ; auto with stalmarck.
case (rZDec (evalZ Ar r) rZFalse); intros Eq11.
generalize (addEqMemCorrect Ar (evalZ Ar p) (rZComp (evalZ Ar q)));
 case (addEqMem Ar (evalZ Ar p) (rZComp (evalZ Ar q))).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZComp q) S); split; auto with stalmarck.
apply doTripletEqPrF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply contradictoryEq with (1 := H'3); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; try apply eqStateRzInv; apply eqStateEvalZ; auto with stalmarck.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto with stalmarck.
split; auto with stalmarck.
split; auto with stalmarck.
exists (addEq (p, rZComp q) S); split; auto with stalmarck.
apply doTripletEqPrF; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
rewrite evalZFalse; auto with stalmarck.
apply rArrayStateEqState with (1 := H'7); auto with stalmarck.
apply eqStateEq1; auto with stalmarck; try apply eqStateRzInv; apply eqStateEvalZ; auto with stalmarck.
intros S'; red in |- *; intros H'1; inversion H'1; auto with stalmarck.
Contradict Eq0; apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq1; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto with stalmarck.
Contradict Eq2; apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq3; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto with stalmarck.
Contradict Eq4; apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq5; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto with stalmarck.
Contradict Eq6; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq7; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq8; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq9; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq10; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Contradict Eq11; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto with stalmarck.
Qed.

End algo.
