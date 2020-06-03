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
                                                                           
          Stalmarck  :    stalmarck                                        
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of stalmarck as the transitive closure of the dilemma rule *)
Require Export doTriplets.
Require Export interState.
Require Export makeTriplet.
(* stalmarck is simply the reflexive transitive closure of dilemma *)

Inductive stalmarckP : State -> list triplet -> State -> Prop :=
  | stalmarckPref :
      forall (S1 S2 : State) (L : list triplet),
      doTripletsP S1 L S2 -> stalmarckP S1 L S2
  | stalmarckPSplit :
      forall (a b : rZ) (S1 S2 S3 S4 : State) (L : list triplet),
      stalmarckP (addEq (a, b) S1) L S2 ->
      stalmarckP (addEq (a, rZComp b) S1) L S3 ->
      eqState (interState S2 S3) S4 -> stalmarckP S1 L S4
  | stalmarckTrans :
      forall (S1 S2 S3 : State) (L : list triplet),
      stalmarckP S1 L S2 -> stalmarckP S2 L S3 -> stalmarckP S1 L S3.
Hint Resolve stalmarckPref : stalmarck.

Definition boolDec : forall a b : bool, {a = b} + {a <> b}.
intros a b; case a; case b; auto with stalmarck; right; red in |- *; intros; discriminate.
Defined.
(* It is compatible with equality *)

Theorem stalmarckComp :
 forall (S1 S2 S3 S4 : State) (L : list triplet),
 stalmarckP S1 L S2 -> eqState S3 S1 -> eqState S4 S2 -> stalmarckP S3 L S4.
intros S1 S2 S3 S4 L H'; generalize S3 S4; Elimc H'; clear L S1 S2 S3 S4.
intros S1 S2 L H' S3 S4 H'0 H'1.
apply stalmarckPref; auto with stalmarck.
apply doTripletsComp with (1 := H'); auto with stalmarck.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3 S5 S6 H'4 H'5.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S2) (S3 := S3); auto with stalmarck.
apply eqStateTrans with (S2 := S4); auto with stalmarck.
intros S1 S2 S3 L H' H'0 H'1 H'2 S4 S5 H'3 H'4.
apply stalmarckTrans with (S2 := S2); auto with stalmarck.
Qed.
(* It only adds equations *)

Theorem stalmarckUnionEx :
 forall (S1 S2 : State) (L : list triplet),
 stalmarckP S1 L S2 -> exists S3 : State, eqState S2 (unionState S3 S1).
intros S1 S2 L H'; Elimc H'; clear L S1 S2; auto with stalmarck.
exact doTripletsUnionEx.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3; exists S4; auto with stalmarck.
red in |- *; split; auto with stalmarck.
apply unionStateMin; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S1) (S3 := interState S2 S3); auto with stalmarck.
apply interMemMin; auto with stalmarck.
Elimc H'0; intros S5 E.
apply
 inclStateEqStateComp
  with (S1 := S1) (S3 := unionState (unionState S5 (addEq (a, b) nil)) S1);
 auto with stalmarck.
apply
 eqStateTrans with (S2 := unionState S5 (unionState (addEq (a, b) nil) S1));
 auto with stalmarck.
apply eqStateSym; auto with stalmarck.
apply unionStateAssoc; auto with stalmarck.
Elimc H'2; intros S5 E.
apply
 inclStateEqStateComp
  with
    (S1 := S1)
    (S3 := unionState (unionState S5 (addEq (a, rZComp b) nil)) S1); 
 auto with stalmarck.
apply
 eqStateTrans
  with (S2 := unionState S5 (unionState (addEq (a, rZComp b) nil) S1)); 
 auto with stalmarck.
apply eqStateSym; auto with stalmarck.
apply unionStateAssoc; auto with stalmarck.
intros S1 S2 S3 L H' H'0 H'1 H'2.
elim H'0; intros S4 E; clear H'0.
elim H'2; intros S5 E0; clear H'2.
exists (unionState S5 S4); auto with stalmarck.
apply eqStateTrans with (S2 := unionState S5 (unionState S4 S1)); auto with stalmarck.
apply eqStateTrans with (S2 := unionState S5 S2); auto with stalmarck.
apply unionStateAssoc; auto with stalmarck.
Qed.
(* The state only grows *)

Theorem stalmarckIncl :
 forall (S1 S2 : State) (L : list triplet),
 stalmarckP S1 L S2 -> inclState S1 S2.
intros S1 S2 L H'.
elim (stalmarckUnionEx S1 S2 L); [ intros S3 E | idtac ]; auto with stalmarck.
apply inclStateEqStateComp with (S1 := S1) (S3 := unionState S3 S1); auto with stalmarck.
Qed.
(* It is  monotone *)

Theorem stalmarckMonotoneEx :
 forall (S1 S2 S3 : State) (L : list triplet),
 stalmarckP S1 L S3 ->
 inclState S1 S2 -> exists S4 : State, stalmarckP S2 L S4 /\ inclState S3 S4.
intros S1 S2 S3 L H'; generalize S2; Elimc H'; auto with stalmarck; clear L S1 S2 S3.
intros S1 S3 L H' S2 H'0.
elim (doTripletsMonotoneEx S1 S2 S3 L);
 [ intros S4 E; Elimc E; intros H'7 H'8 | idtac | idtac ]; 
 auto with stalmarck.
exists S4; split; auto with stalmarck.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3 S0 H'4.
elim (H'0 (addEq (a, b) S0));
 [ intros S5 E; Elimc E; intros H'7 H'8 | idtac ]; 
 auto with stalmarck.
elim (H'2 (addEq (a, rZComp b) S0));
 [ intros S6 E; Elimc E; intros H'9 H'10 | idtac ]; 
 auto with stalmarck.
exists (interState S5 S6); split; auto with stalmarck.
apply stalmarckPSplit with (1 := H'7) (2 := H'9); auto with stalmarck.
apply
 inclStateEqStateComp with (S1 := interState S2 S3) (S3 := interState S5 S6);
 auto with stalmarck.
apply interMemMin; auto with stalmarck.
apply inclStateTrans with (S2 := S2); auto with stalmarck.
apply inclStateTrans with (S2 := S3); auto with stalmarck.
intros S1 S2 S3 L H' H'0 H'1 H'2 S4 H'3.
elim (H'0 S4); [ intros S6 E; elim E; intros H'6 H'7; clear E | idtac ]; auto with stalmarck.
elim (H'2 S6); [ intros S7 E; elim E; intros H'8 H'9; clear E | idtac ]; auto with stalmarck.
exists S7; split; auto with stalmarck.
apply stalmarckTrans with (S2 := S6); auto with stalmarck.
Qed.
(* We don't loose realizability of states if the triplets are realized *)

Theorem stalmarckRealizeStateEval :
 forall (f : rNat -> bool) (S1 S2 : State) (L : list triplet),
 realizeState f S1 ->
 stalmarckP S1 L S2 ->
 realizeTriplets f L -> f zero = true -> realizeState f S2.
intros f S1 S2 L H' H'0; generalize H'; elim H'0; auto with stalmarck.
intros S3 S4 L0 H'1 H'2 H'3 H'4.
apply doTripletsRealizeStateEval with (S1 := S3) (L := L0); auto with stalmarck.
intros a b S3 S4 S5 S6 L0 H'1 H'2 H'3 H'4 H'5 H'6 H'7 H'8.
case (boolDec (rZEval f a) (rZEval f b)); intros Eqf.
apply realizeStateIncl with (S1 := S4); auto with stalmarck.
inversion H'5; auto with stalmarck.
apply inclStateTrans with (S2 := interState S4 S5); auto with stalmarck.
apply realizeStateIncl with (S1 := S5); auto with stalmarck.
apply H'4; auto with stalmarck.
apply realizeStateAddEq; auto with stalmarck.
rewrite rZEvalCompInv.
generalize Eqf; case (rZEval f a); case (rZEval f b); simpl in |- *; auto with stalmarck;
 intros H'10; case H'10; auto with stalmarck.
apply inclStateEqStateComp with (S1 := interState S4 S5) (S3 := S5); auto with stalmarck.
Qed.

Theorem stalmarckGivesValidEquation :
 forall (L : list triplet) (a b : rZ) (S : State),
 stalmarckP (addEq (a, rZComp b) nil) L S ->
 contradictory S -> validEquation L a b.
intros L a b S H' H'0.
red in |- *; auto with stalmarck.
intros f H'1 H'2; case (boolDec (rZEval f a) (rZEval f b)); auto with stalmarck.
intros H'3; absurd (realizeState f S); auto with stalmarck.
apply stalmarckRealizeStateEval with (S1 := addEq (a, rZComp b) nil) (L := L);
 auto with stalmarck.
apply realizeStateAddEq; auto with stalmarck.
rewrite rZEvalCompInv; generalize H'3; case (rZEval f a); case (rZEval f b);
 auto with stalmarck; intros H'4; case H'4; auto with stalmarck.
Qed.
(* Correctness *)

Theorem stalmarckCorrect :
 forall (e : Expr) (S : State),
 match makeTriplets (norm e) with
 | tRC l s n =>
     stalmarckP (addEq (s, rZFalse) nil) l S ->
     contradictory S -> Tautology e
 end.
intros e S; generalize (refl_equal (makeTriplets (norm e)));
 pattern (makeTriplets (norm e)) at -2 in |- *; case (makeTriplets (norm e)).
intros l r r0 H' H'0 H'1.
apply <- (TautoRTauto e).
apply <- (rTautotTauto (norm e)).
red.
rewrite <- H'; auto with stalmarck.
apply stalmarckGivesValidEquation with (S := S); auto with stalmarck.
Qed.
