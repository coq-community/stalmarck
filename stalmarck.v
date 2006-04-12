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
Hint Resolve stalmarckPref.

Definition boolDec : forall a b : bool, {a = b} + {a <> b}.
intros a b; case a; case b; auto; right; red in |- *; intros; discriminate.
Defined.
(* It is compatible with equality *)

Theorem stalmarckComp :
 forall (S1 S2 S3 S4 : State) (L : list triplet),
 stalmarckP S1 L S2 -> eqState S3 S1 -> eqState S4 S2 -> stalmarckP S3 L S4.
intros S1 S2 S3 S4 L H'; generalize S3 S4; Elimc H'; clear L S1 S2 S3 S4.
intros S1 S2 L H' S3 S4 H'0 H'1.
apply stalmarckPref; auto.
apply doTripletsComp with (1 := H'); auto.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3 S5 S6 H'4 H'5.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S2) (S3 := S3); auto.
apply eqStateTrans with (S2 := S4); auto.
intros S1 S2 S3 L H' H'0 H'1 H'2 S4 S5 H'3 H'4.
apply stalmarckTrans with (S2 := S2); auto.
Qed.
(* It only adds equations *)

Theorem stalmarckUnionEx :
 forall (S1 S2 : State) (L : list triplet),
 stalmarckP S1 L S2 -> exists S3 : State, eqState S2 (unionState S3 S1).
intros S1 S2 L H'; Elimc H'; clear L S1 S2; auto.
exact doTripletsUnionEx.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3; exists S4; auto.
red in |- *; split; auto.
apply unionStateMin; auto.
apply inclStateEqStateComp with (S1 := S1) (S3 := interState S2 S3); auto.
apply interMemMin; auto.
Elimc H'0; intros S5 E.
apply
 inclStateEqStateComp
  with (S1 := S1) (S3 := unionState (unionState S5 (addEq (a, b) nil)) S1);
 auto.
apply
 eqStateTrans with (S2 := unionState S5 (unionState (addEq (a, b) nil) S1));
 auto.
apply eqStateSym; auto.
apply unionStateAssoc; auto.
Elimc H'2; intros S5 E.
apply
 inclStateEqStateComp
  with
    (S1 := S1)
    (S3 := unionState (unionState S5 (addEq (a, rZComp b) nil)) S1); 
 auto.
apply
 eqStateTrans
  with (S2 := unionState S5 (unionState (addEq (a, rZComp b) nil) S1)); 
 auto.
apply eqStateSym; auto.
apply unionStateAssoc; auto.
intros S1 S2 S3 L H' H'0 H'1 H'2.
elim H'0; intros S4 E; clear H'0.
elim H'2; intros S5 E0; clear H'2.
exists (unionState S5 S4); auto.
apply eqStateTrans with (S2 := unionState S5 (unionState S4 S1)); auto.
apply eqStateTrans with (S2 := unionState S5 S2); auto.
apply unionStateAssoc; auto.
Qed.
(* The state only grows *)

Theorem stalmarckIncl :
 forall (S1 S2 : State) (L : list triplet),
 stalmarckP S1 L S2 -> inclState S1 S2.
intros S1 S2 L H'.
elim (stalmarckUnionEx S1 S2 L); [ intros S3 E | idtac ]; auto.
apply inclStateEqStateComp with (S1 := S1) (S3 := unionState S3 S1); auto.
Qed.
(* It is  monotone *)

Theorem stalmarckMonotoneEx :
 forall (S1 S2 S3 : State) (L : list triplet),
 stalmarckP S1 L S3 ->
 inclState S1 S2 -> exists S4 : State, stalmarckP S2 L S4 /\ inclState S3 S4.
intros S1 S2 S3 L H'; generalize S2; Elimc H'; auto; clear L S1 S2 S3.
intros S1 S3 L H' S2 H'0.
elim (doTripletsMonotoneEx S1 S2 S3 L);
 [ intros S4 E; Elimc E; intros H'7 H'8 | idtac | idtac ]; 
 auto.
exists S4; split; auto.
intros a b S1 S2 S3 S4 L H' H'0 H'1 H'2 H'3 S0 H'4.
elim (H'0 (addEq (a, b) S0));
 [ intros S5 E; Elimc E; intros H'7 H'8 | idtac ]; 
 auto.
elim (H'2 (addEq (a, rZComp b) S0));
 [ intros S6 E; Elimc E; intros H'9 H'10 | idtac ]; 
 auto.
exists (interState S5 S6); split; auto.
apply stalmarckPSplit with (1 := H'7) (2 := H'9); auto.
apply
 inclStateEqStateComp with (S1 := interState S2 S3) (S3 := interState S5 S6);
 auto.
apply interMemMin; auto.
apply inclStateTrans with (S2 := S2); auto.
apply inclStateTrans with (S2 := S3); auto.
intros S1 S2 S3 L H' H'0 H'1 H'2 S4 H'3.
elim (H'0 S4); [ intros S6 E; elim E; intros H'6 H'7; clear E | idtac ]; auto.
elim (H'2 S6); [ intros S7 E; elim E; intros H'8 H'9; clear E | idtac ]; auto.
exists S7; split; auto.
apply stalmarckTrans with (S2 := S6); auto.
Qed.
(* We don't loose realizability of states if the triplets are realized *)

Theorem stalmarckRealizeStateEval :
 forall (f : rNat -> bool) (S1 S2 : State) (L : list triplet),
 realizeState f S1 ->
 stalmarckP S1 L S2 ->
 realizeTriplets f L -> f zero = true -> realizeState f S2.
intros f S1 S2 L H' H'0; generalize H'; elim H'0; auto.
intros S3 S4 L0 H'1 H'2 H'3 H'4.
apply doTripletsRealizeStateEval with (S1 := S3) (L := L0); auto.
intros a b S3 S4 S5 S6 L0 H'1 H'2 H'3 H'4 H'5 H'6 H'7 H'8.
case (boolDec (rZEval f a) (rZEval f b)); intros Eqf.
apply realizeStateIncl with (S1 := S4); auto.
inversion H'5; auto.
apply inclStateTrans with (S2 := interState S4 S5); auto.
apply realizeStateIncl with (S1 := S5); auto.
apply H'4; auto.
apply realizeStateAddEq; auto.
rewrite rZEvalCompInv.
generalize Eqf; case (rZEval f a); case (rZEval f b); simpl in |- *; auto;
 intros H'10; case H'10; auto.
apply inclStateEqStateComp with (S1 := interState S4 S5) (S3 := S5); auto.
Qed.

Theorem stalmarckGivesValidEquation :
 forall (L : list triplet) (a b : rZ) (S : State),
 stalmarckP (addEq (a, rZComp b) nil) L S ->
 contradictory S -> validEquation L a b.
intros L a b S H' H'0.
red in |- *; auto.
intros f H'1 H'2; case (boolDec (rZEval f a) (rZEval f b)); auto.
intros H'3; absurd (realizeState f S); auto.
apply stalmarckRealizeStateEval with (S1 := addEq (a, rZComp b) nil) (L := L);
 auto.
apply realizeStateAddEq; auto.
rewrite rZEvalCompInv; generalize H'3; case (rZEval f a); case (rZEval f b);
 auto; intros H'4; case H'4; auto.
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
specialize  1TautoRTauto with (e := e); intros H'2; inversion H'2.
apply H0; auto.
specialize  1rTautotTauto with (e := norm e); intros H'3; inversion H'3.
apply H2; auto.
red in |- *; auto.
rewrite <- H'; auto.
apply stalmarckGivesValidEquation with (S := S); auto.
Qed.