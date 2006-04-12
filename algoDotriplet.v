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
                                                                           
          Stalmarck  :   algoDotriplet                                        
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Implement the one step propagation*)
Require Export memoryImplement.
Require Export triplet.
Section algo.
(* We simply check the applicability of each rule sequentially,
    the test is made with the miniaml element *)

Definition doTripletF : forall (Ar : rArray vM) (t : triplet), Option mbD.
intros Ar t.
case t; intros b p q r.
apply letP with (1 := evalZ Ar p); intros p'.
apply letP with (1 := evalZ Ar q); intros q'.
apply letP with (1 := evalZ Ar r); intros r'.
case b.
case (rZDec p' (rZComp q')); intros Eq1.
exact (Some _ (addEqMem2 Ar r' rZFalse q' rZTrue)).
case (rZDec p' (rZComp r')); intros Eq2.
exact (Some _ (addEqMem2 Ar r' rZTrue q' rZFalse)).
case (rZDec q' r'); intros Eq3.
exact (Some _ (addEqMem Ar p' r')).
case (rZDec q' (rZComp r')); intros Eq4.
exact (Some _ (addEqMem Ar p' rZFalse)).
case (rZDec p' rZTrue); intros Eq5.
exact (Some _ (addEqMem2 Ar r' rZTrue q' rZTrue)).
case (rZDec q' rZTrue); intros Eq6.
exact (Some _ (addEqMem Ar p' r')).
case (rZDec q' rZFalse); intros Eq7.
exact (Some _ (addEqMem Ar p' rZFalse)).
case (rZDec r' rZTrue); intros Eq8.
exact (Some _ (addEqMem Ar p' q')).
case (rZDec r' rZFalse); intros Eq9.
exact (Some _ (addEqMem Ar p' rZFalse)).
exact (None mbD).
case (rZDec p' q'); intros Eq1.
exact (Some _ (addEqMem Ar r' rZTrue)).
case (rZDec p' (rZComp q')); intros Eq2.
exact (Some _ (addEqMem Ar r' rZFalse)).
case (rZDec p' r'); intros Eq3.
exact (Some _ (addEqMem Ar q' rZTrue)).
case (rZDec p' (rZComp r')); intros Eq4.
exact (Some _ (addEqMem Ar q' rZFalse)).
case (rZDec q' r'); intros Eq5.
exact (Some _ (addEqMem Ar p' rZTrue)).
case (rZDec q' (rZComp r')); intros Eq6.
exact (Some _ (addEqMem Ar p' rZFalse)).
case (rZDec p' rZTrue); intros Eq7.
exact (Some _ (addEqMem Ar q' r')).
case (rZDec p' rZFalse); intros Eq8.
exact (Some _ (addEqMem Ar q' (rZComp r'))).
case (rZDec q' rZTrue); intros Eq9.
exact (Some _ (addEqMem Ar p' r')).
case (rZDec q' rZFalse); intros Eq10.
exact (Some _ (addEqMem Ar p' (rZComp r'))).
case (rZDec r' rZTrue); intros Eq11.
exact (Some _ (addEqMem Ar p' q')).
case (rZDec r' rZFalse); intros Eq12.
exact (Some _ (addEqMem Ar p' (rZComp q'))).
exact (None mbD).
Defined.
Require Import doTriplet.

Theorem contradictoryEq :
 forall S1 S2 : State, contradictory S1 -> eqState S1 S2 -> contradictory S2.
intros S1 S2 H' H'0; inversion H'.
exists x; auto.
apply eqStateEq with (S1 := S1); auto.
Qed.

Theorem eqStateEvalZ :
 forall (Ar : rArray vM) (S : State) (q : rZ),
 wellFormedArray Ar -> rArrayState Ar S -> eqStateRz S (evalZ Ar q) q.
intros Ar S q H' H'0.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply evalZInv; auto.
Qed.

Theorem eqStateEq1 :
 forall (S : State) (q r s t : rZ),
 eqStateRz S q s ->
 eqStateRz S r t -> eqState (addEq (q, r) S) (addEq (s, t) S).
intros S q r s t Eq1 Eq2; split.
apply inclStateIn; simpl in |- *; auto.
intros a b H'0; Elimc H'0; intros H'0; auto.
inversion H'0; clear H'0; auto.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := s); auto.
apply eqStateRzTrans with (b := t); auto.
apply inclStateIn; simpl in |- *; auto.
intros a b H'0; Elimc H'0; intros H'0; auto.
inversion H'0; clear H'0.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := q); auto.
apply eqStateRzTrans with (b := r); auto.
Qed.

Theorem eqStateEqEvalZ :
 forall (Ar : rArray vM) (S : State) (q r : rZ),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 eqState (addEq (evalZ Ar q, evalZ Ar r) S) (addEq (q, r) S).
intros Ar S q r H' H'0.
apply eqStateEq1; auto.
apply eqStateEvalZ; auto.
apply eqStateEvalZ; auto.
Qed.

Theorem eqStateEq2 :
 forall (S : State) (q r s t u v w x : rZ),
 eqStateRz S q s ->
 eqStateRz S r t ->
 eqStateRz S u w ->
 eqStateRz S v x ->
 eqState (addEq (q, r) (addEq (u, v) S)) (addEq (s, t) (addEq (w, x) S)).
intros S q r s t u v w x Eq1 Eq2 Eq3 Eq4; split.
apply inclStateIn; simpl in |- *; auto.
intros a b H'0; Elimc H'0; intros H'0; auto.
inversion H'0; clear H'0; auto.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := s); auto.
apply eqStateRzTrans with (b := t); auto.
Elimc H'0; intros H'0; auto.
inversion H'0; clear H'0; auto.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := w); auto.
apply eqStateRzTrans with (b := x); auto.
apply inclStateIn; simpl in |- *; auto.
intros a b H'0; Elimc H'0; intros H'0; auto.
inversion H'0; clear H'0; auto.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := q); auto.
apply eqStateRzTrans with (b := r); auto.
Elimc H'0; intros H'0; auto.
inversion H'0; clear H'0; auto.
rewrite <- H0; rewrite <- H1.
apply eqStateRzTrans with (b := u); auto.
apply eqStateRzTrans with (b := v); auto.
Qed.

Theorem eqStateEq2EvalZ :
 forall (Ar : rArray vM) (S : State) (q r s t : rZ),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 eqState (addEq (evalZ Ar q, evalZ Ar r) (addEq (evalZ Ar s, evalZ Ar t) S))
   (addEq (q, r) (addEq (s, t) S)).
intros Ar S q r s t H' H'0.
apply eqStateEq2; auto.
apply eqStateEvalZ; auto.
apply eqStateEvalZ; auto.
apply eqStateEvalZ; auto.
apply eqStateEvalZ; auto.
Qed.
(* The implementation is correct *)

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
intros Ar t S H' H'0; unfold doTripletF, letP in |- *.
case t.
intros b p q r; case b.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar q))); intros Eq0.
generalize (addEqMem2Correct Ar (evalZ Ar r) rZFalse (evalZ Ar q) rZTrue);
 case (addEqMem2 Ar (evalZ Ar r) rZFalse (evalZ Ar q) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZTrue) (addEq (r, rZFalse) S)); 
 split; auto.
apply doTripletAndPpmq; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq2; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, rZTrue) (addEq (r, rZFalse) S)); split; auto.
apply doTripletAndPpmq; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq2; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar r))); intros Eq1.
generalize (addEqMem2Correct Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZFalse);
 case (addEqMem2 Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZFalse) (addEq (r, rZTrue) S)); 
 split; auto.
apply doTripletAndPpmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq2; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, rZFalse) (addEq (r, rZTrue) S)); split; auto.
apply doTripletAndPpmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq2; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) (evalZ Ar r)); intros Eq2.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, r) S);
 split; auto.
apply doTripletAndPqr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, r) S); split; auto.
apply doTripletAndPqr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) (rZComp (evalZ Ar r))); intros Eq3.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto.
apply doTripletAndPqmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZFalse) S); split; auto.
apply doTripletAndPqmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) rZTrue); intros Eq4.
generalize (addEqMem2Correct Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZTrue);
 case (addEqMem2 Ar (evalZ Ar r) rZTrue (evalZ Ar q) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZTrue) (addEq (r, rZTrue) S)); 
 split; auto.
apply doTripletAndPpT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq2; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, rZTrue) (addEq (r, rZTrue) S)); split; auto.
apply doTripletAndPpT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq2; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) rZTrue); intros Eq5.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, r) S);
 split; auto.
apply doTripletAndPqT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, r) S); split; auto.
apply doTripletAndPqT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) rZFalse); intros Eq6.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto.
apply doTripletAndPqF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZFalse) S); split; auto.
apply doTripletAndPqF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar r) rZTrue); intros Eq7.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar q));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar q)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, q) S);
 split; auto.
apply doTripletAndPrT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, q) S); split; auto.
apply doTripletAndPrT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar r) rZFalse); intros Eq8.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto.
apply doTripletAndPrF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZFalse) S); split; auto.
apply doTripletAndPrF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros S'; red in |- *; intros H'1; inversion H'1; auto.
Contradict Eq0; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto.
Contradict Eq1; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto.
Contradict Eq2; apply rArrayStateDef1 with (S := S); auto.
Contradict Eq3; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto.
Contradict Eq4; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq5; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq6; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq7; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq8; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto.
case (rZDec (evalZ Ar p) (evalZ Ar q)); intros Eq0.
generalize (addEqMemCorrect Ar (evalZ Ar r) rZTrue);
 case (addEqMem Ar (evalZ Ar r) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (r, rZTrue) S); split; auto.
apply doTripletEqPpq; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (r, rZTrue) S); split; auto.
apply doTripletEqPpq; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar q))); intros Eq1.
generalize (addEqMemCorrect Ar (evalZ Ar r) rZFalse);
 case (addEqMem Ar (evalZ Ar r) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (r, rZFalse) S); split; auto.
apply doTripletEqPpmq; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (r, rZFalse) S); split; auto.
apply doTripletEqPpmq; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) (evalZ Ar r)); intros Eq2.
generalize (addEqMemCorrect Ar (evalZ Ar q) rZTrue);
 case (addEqMem Ar (evalZ Ar q) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZTrue) S); split; auto.
apply doTripletEqPpr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, rZTrue) S); split; auto.
apply doTripletEqPpr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) (rZComp (evalZ Ar r))); intros Eq3.
generalize (addEqMemCorrect Ar (evalZ Ar q) rZFalse);
 case (addEqMem Ar (evalZ Ar q) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZFalse) S); split; auto.
apply doTripletEqPpmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, rZFalse) S); split; auto.
apply doTripletEqPpmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) (evalZ Ar r)); intros Eq4.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZTrue);
 case (addEqMem Ar (evalZ Ar p) rZTrue).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZTrue) S); split; auto.
apply doTripletEqPqr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZTrue) S); split; auto.
apply doTripletEqPqr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) (rZComp (evalZ Ar r))); intros Eq5.
generalize (addEqMemCorrect Ar (evalZ Ar p) rZFalse);
 case (addEqMem Ar (evalZ Ar p) rZFalse).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZFalse) S); split; auto.
apply doTripletEqPqmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZFalse) S); split; auto.
apply doTripletEqPqmr; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) rZTrue); intros Eq6.
generalize (addEqMemCorrect Ar (evalZ Ar q) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar q) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (q, r) S);
 split; auto.
apply doTripletEqPpT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, r) S); split; auto.
apply doTripletEqPpT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar p) rZFalse); intros Eq7.
generalize (addEqMemCorrect Ar (evalZ Ar q) (rZComp (evalZ Ar r)));
 case (addEqMem Ar (evalZ Ar q) (rZComp (evalZ Ar r))).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (q, rZComp r) S); split; auto.
apply doTripletEqPpF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; try apply eqStateRzInv; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (q, rZComp r) S); split; auto.
apply doTripletEqPpF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; try apply eqStateRzInv; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) rZTrue); intros Eq8.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar r));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar r)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, r) S);
 split; auto.
apply doTripletEqPqT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, r) S); split; auto.
apply doTripletEqPqT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar q) rZFalse); intros Eq9.
generalize (addEqMemCorrect Ar (evalZ Ar p) (rZComp (evalZ Ar r)));
 case (addEqMem Ar (evalZ Ar p) (rZComp (evalZ Ar r))).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZComp r) S); split; auto.
apply doTripletEqPqF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; try apply eqStateRzInv; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZComp r) S); split; auto.
apply doTripletEqPqF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; try apply eqStateRzInv; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar r) rZTrue); intros Eq10.
generalize (addEqMemCorrect Ar (evalZ Ar p) (evalZ Ar q));
 case (addEqMem Ar (evalZ Ar p) (evalZ Ar q)).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3; exists (addEq (p, q) S);
 split; auto.
apply doTripletEqPrT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, q) S); split; auto.
apply doTripletEqPrT; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZTrue; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; apply eqStateEvalZ; auto.
case (rZDec (evalZ Ar r) rZFalse); intros Eq11.
generalize (addEqMemCorrect Ar (evalZ Ar p) (rZComp (evalZ Ar q)));
 case (addEqMem Ar (evalZ Ar p) (rZComp (evalZ Ar q))).
intros Ar' b' L'; case b'.
intros H'2; generalize (H'2 S H' H'0); intros H'3;
 exists (addEq (p, rZComp q) S); split; auto.
apply doTripletEqPrF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply contradictoryEq with (1 := H'3); auto.
apply eqStateEq1; auto; try apply eqStateRzInv; apply eqStateEvalZ; auto.
intros H'2; elim (H'2 S);
 [ intros H'6 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9
 | idtac
 | idtac ]; auto.
split; auto.
split; auto.
exists (addEq (p, rZComp q) S); split; auto.
apply doTripletEqPrF; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZFalse; auto.
apply rArrayStateEqState with (1 := H'7); auto.
apply eqStateEq1; auto; try apply eqStateRzInv; apply eqStateEvalZ; auto.
intros S'; red in |- *; intros H'1; inversion H'1; auto.
Contradict Eq0; apply rArrayStateDef1 with (S := S); auto.
Contradict Eq1; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto.
Contradict Eq2; apply rArrayStateDef1 with (S := S); auto.
Contradict Eq3; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto.
Contradict Eq4; apply rArrayStateDef1 with (S := S); auto.
Contradict Eq5; rewrite <- evalZComp; apply rArrayStateDef1 with (S := S);
 auto.
Contradict Eq6; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq7; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq8; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq9; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq10; rewrite <- (evalZTrue Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Contradict Eq11; rewrite <- (evalZFalse Ar H');
 apply rArrayStateDef1 with (S := S); auto.
Qed.
End algo.