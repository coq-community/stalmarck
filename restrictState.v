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
                                                                           
          Stalmarck  :    restrictState                                    
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Definition of state restriction and we show that only the variables of the triplets
matter*)
Require Import stalmarck.
Require Import ltState.
(* Inversion theorem for contradictory state *)

Theorem contradictoryAddEq :
 forall (S : State) (a b : rZ),
 contradictory (addEq (a, b) S) -> eqStateRz S a (rZComp b).
intros S a b H'; cut (eqConstrState (addEq (a, b) S) a (rZComp a)).
unfold addEq in |- *; intros H'1; inversion H'1; auto;
 try (apply eqStateRzContr with (a := a); auto; fail).
red in H'.
Elimc H'; intros a0 E.
apply eqStateRzPImpeqConstrState.
apply eqStateRzContr with (a := a0); auto.
Qed.
Hint Resolve contradictoryAddEq.

Theorem prodRzInL :
 forall (a b : rZ) (L1 L2 : list rZ), In (a, b) (prodRz L1 L2) -> In a L1.
intros a b L1; elim L1; simpl in |- *; auto.
intros a0 l H' L2 H'0.
case (in_app_or _ _ _ H'0); auto.
elim L2; simpl in |- *; auto.
intros H'1; elim H'1; auto.
intros a1 l0 H'1 H'2; Elimc H'2; intros H'2; [ inversion H'2 | idtac ]; auto.
intros H'1; right; auto.
apply H' with (L2 := L2); auto.
Qed.

Theorem prodRzInR :
 forall (a b : rZ) (L1 L2 : list rZ), In (a, b) (prodRz L1 L2) -> In b L2.
intros a b L1; elim L1; simpl in |- *; auto.
intros L2 H'; elim H'; auto.
intros a0 l H' L2 H'0.
case (in_app_or _ _ _ H'0); auto.
elim L2; simpl in |- *; auto.
intros a1 l0 H'1 H'2; Elimc H'2; intros H'2; [ inversion H'2 | idtac ]; auto.
Qed.
(* We remove in the second list the element that are not in the first *)

Fixpoint stripInRz (L : list rNat) (L1 : list rZ) {struct L1} : 
 list rZ :=
  match L1 with
  | nil => nil
  | a :: L1' =>
      match In_dec rNatDec (valRz a) L with
      | left _ => a :: stripInRz L L1'
      | right _ => stripInRz L L1'
      end
  end.

Theorem stripInRzIn1 :
 forall (L : list rNat) (L1 : list rZ) (a : rZ),
 In a (stripInRz L L1) -> In (valRz a) L.
intros L L1; elim L1; simpl in |- *; auto.
intros a H'; elim H'; auto.
intros a l H' a0.
case (In_dec rNatDec (valRz a) L); simpl in |- *; auto.
intros H'0 H'1; Elimc H'1; intros H'1; [ rewrite <- H'1 | idtac ]; auto.
Qed.

Theorem stripInRzIn :
 forall (L : list rNat) (L1 : list rZ) (a : rZ),
 In a L1 -> In (valRz a) L -> In a (stripInRz L L1).
intros L L1; elim L1; simpl in |- *; auto.
intros a l H' a0 H'0; Elimc H'0; intros H'0; [ rewrite <- H'0 | idtac ];
 case (In_dec rNatDec (valRz a) L); simpl in |- *; 
 auto.
intros H'1 H'2; case H'1; auto.
Qed.

(* The restriction of the state is all the non-trival equation of the state
     whose elements are in the list *)

Definition restrictState (S : State) (L : list rNat) : State :=
  match eqStateRzContrDec S with
  | left _ => (rZTrue, rZFalse) :: nil
  | right _ =>
      stripRzDec S
        (prodRz (stripInRz L (stripRz S)) (stripInRz L (stripRz S)))
  end.
(* It seems that this speeds up Coq *)
Opaque eqStateRzContrDec.

Theorem restrictStateIncl :
 forall (S : State) (L : list rNat), inclState (restrictState S L) S.
intros S L; unfold restrictState in |- *.
case (eqStateRzContrDec S); auto.
intros H'; red in |- *; auto.
intros H'; apply inclStateIn; auto.
intros a b H'0; apply eqConstrStateImpeqStateRz.
apply
 stripRzDecProp2
  with (S2 := prodRz (stripInRz L (stripRz S)) (stripInRz L (stripRz S)));
 auto.
Qed.

Lemma andSym : forall A B : Prop, A /\ B -> B /\ A.
intuition.
Qed.

Theorem InState :
 forall (S : State) (L : list rNat),
 (forall a b : rZ, In (a, b) S -> In (valRz a) L /\ In (valRz b) L) ->
 forall a b : rZ,
 eqStateRz S a b ->
 a <> b -> ~ contradictory S -> In (valRz a) L /\ In (valRz b) L.
intros S L H' a b H'0; generalize H'; Elimc H'0; clear H' S a b; auto.
intros a S H' H'0; case H'0; auto.
intros a b S H' H'0 H'1 H'2 H'3.
repeat rewrite valRzComp; auto.
apply H'0; auto.
red in |- *; intros H'4; case H'2; auto.
rewrite H'4; auto.
intros a b S H' H'0 H'1 H'2 H'3.
apply andSym; auto.
intros a b c S H' H'0 H'1 H'2 H'3 H'4 H'5; split.
case (rZDec a b); intros Eqab.
rewrite Eqab; auto.
Elimc H'2; [ intros H'2 H'6; apply H'2 | idtac | idtac | idtac ]; auto.
rewrite <- Eqab; auto.
Elimc H'0; [ intros H'0 H'6; apply H'0 | idtac | idtac | idtac ]; auto.
case (rZDec b c); intros Eqbc.
rewrite <- Eqbc; auto.
Elimc H'0; [ intros H'0 H'6; apply H'6 | idtac | idtac | idtac ]; auto.
rewrite Eqbc; auto.
Elimc H'2; [ intros H'2 H'6; apply H'6 | idtac | idtac | idtac ]; auto.
intros a b c S H' H'0 H'1 H'2 H'3; case H'3; auto.
red in |- *.
exists a; auto.
Qed.

Theorem restrictContradiction :
 forall (S : State) (L : list rNat),
 contradictory S <-> contradictory (restrictState S L).
intros S L; red in |- *; split; auto.
unfold restrictState in |- *; case (eqStateRzContrDec S); auto.
intros H' H'0; red in |- *; exists rZTrue; auto; auto.
intros H' H'0; case H'; red in H'0.
Elimc H'0; intros a E.
intros a0 b; apply eqStateRzContr with (a := a); auto.
intros H'; red in H'.
Elimc H'; intros a E.
red in |- *; exists a; auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateIncl; auto.
Qed.

Theorem InRestrictState :
 forall (S : State) (L : list rNat) (a b : rZ),
 eqStateRz (restrictState S L) a b ->
 a <> b -> ~ contradictory S -> In (valRz a) L /\ In (valRz b) L.
intros S L a b H' H'0 H'1.
apply InState with (S := restrictState S L); auto.
2: specialize  2restrictContradiction with (S := S) (L := L); intros H'3;
    red in H'3; auto.
2: red in |- *; intros H'2; apply H'1; auto.
2: Elimc H'3; intros H'3 H'4; lapply H'4; clear H'4;
    [ intros H'4; apply H'4 | idtac ]; auto.
intros a0 b0; unfold restrictState in |- *.
case (eqStateRzContrDec S); auto.
intros H'2; case H'1; auto.
red in |- *; exists rZTrue; auto.
intros H'2 H'3; split.
apply stripInRzIn1 with (L1 := stripRz S); auto.
apply prodRzInL with (b := b0) (L2 := stripInRz L (stripRz S)); auto.
apply stripRzDecProp1 with (S1 := S); auto.
apply stripInRzIn1 with (L1 := stripRz S); auto.
apply prodRzInR with (a := a0) (L1 := stripInRz L (stripRz S)); auto.
apply stripRzDecProp1 with (S1 := S); auto.
Qed.

Theorem vallStateLtNEq :
 forall (L : list rNat) (S1 S2 : State),
 inclState S1 S2 ->
 eqState (restrictState S2 L) S2 ->
 ~ contradictory S2 -> ~ eqState S1 S2 -> valState L S2 < valState L S1.
intros L S1 S2 H' H'0 Contr0 H'1.
elim (inclStateDecBis S2 S1); intros H'2; auto.
case H'1; red in |- *; auto.
Elimc H'2; intros a E; Elimc E; intros b E; Elimc E; intros H'2 H'3.
elim (InRestrictState S2 L a b); [ intros H'10 H'11 | idtac | idtac | idtac ];
 auto.
generalize H'2 H'3 H'10; clear H'2 H'3 H'10; Casec a; intros a H'2 H'3 H'4.
apply vallStateLt with (a := rZPlus a) (b := b); auto.
apply vallStateLt with (a := rZMinus a) (b := b); auto.
apply eqStateRzSym; auto.
apply eqStateEq with (S1 := S2); auto.
Contradict H'3; rewrite H'3; auto.
Qed.

Theorem restrictStateComp :
 forall (S : State) (L : list rNat) (a b : rZ),
 In (valRz a) L ->
 In (valRz b) L -> eqStateRz S a b -> eqStateRz (restrictState S L) a b.
intros S L a b H' H'0 H'1.
unfold restrictState in |- *.
case (eqStateRzContrDec S).
intros H'2.
apply eqStateRzContr with (a := rZTrue); auto.
intros H'2.
case (rZDec a b).
intros H'3; rewrite H'3; auto.
intros H'3.
apply eqStateRzIn; auto.
apply stripRzDecProp3; auto.
apply prodRzProp; auto.
apply stripInRzIn; auto.
apply eqConstrStateInL with (b := b); auto.
apply stripInRzIn; auto.
apply eqConstrStateInR with (a := a); auto.
Qed.

(* Gives the variable in a triplet*)

Definition ResTriplet (t : triplet) : list rNat :=
  match t with
  | Triplet _ v1 v2 v3 => valRz v1 :: valRz v2 :: valRz v3 :: zero :: nil
  end.

Theorem RestrictAddEq1 :
 forall (S : State) (L : list rNat) (a b : rZ),
 In (valRz a) L ->
 In (valRz b) L ->
 In zero L ->
 inclState (addEq (a, b) (restrictState S L))
   (restrictState (addEq (a, b) S) L).
intros S L a b H' H'0 H'1.
apply inclStateIn; auto.
simpl in |- *; auto.
intros a0 b0 H'2; Elimc H'2; intros H'2; auto.
inversion H'2; auto.
rewrite <- H0; auto.
rewrite <- H1; auto.
apply restrictStateComp; auto.
apply restrictStateComp; auto.
generalize H'2; unfold restrictState in |- *.
case (eqStateRzContrDec S); simpl in |- *; auto.
intros H'3 H'4; Elimc H'4; intros H'4; auto; inversion H'4; auto.
intros H'3 H'4.
apply stripInRzIn1 with (L1 := stripRz S); auto.
apply prodRzInL with (b := b0) (L2 := stripInRz L (stripRz S)); auto.
apply stripRzDecProp1 with (S1 := S); auto.
generalize H'2; unfold restrictState in |- *.
case (eqStateRzContrDec S); simpl in |- *; auto.
intros H'3 H'4; Elimc H'4; intros H'4; auto; inversion H'4; auto.
intros H'3 H'4.
apply stripInRzIn1 with (L1 := stripRz S); auto.
apply prodRzInR with (a := a0) (L1 := stripInRz L (stripRz S)); auto.
apply stripRzDecProp1 with (S1 := S); auto.
apply eqStateIncl with (S1 := S); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateIncl.
Qed.

Theorem restrictStateInZeroL :
 forall (S : State) (L : list rNat) (a b : rZ),
 In zero L -> In (a, b) (restrictState S L) -> In (valRz a) L.
intros S L a b H'; unfold restrictState in |- *.
case (eqStateRzContrDec S); simpl in |- *; auto.
intros H'0 H'1; Elimc H'1; intros H'1; inversion H'1; auto.
intros H'0 H'1.
apply stripInRzIn1 with (L1 := stripRz S); auto.
apply prodRzInL with (b := b) (L2 := stripInRz L (stripRz S)); auto.
apply stripRzDecProp1 with (S1 := S); auto.
Qed.

Theorem restrictStateInZeroR :
 forall (S : State) (L : list rNat) (a b : rZ),
 In zero L -> In (a, b) (restrictState S L) -> In (valRz b) L.
intros S L a b H'; unfold restrictState in |- *.
case (eqStateRzContrDec S); simpl in |- *; auto.
intros H'0 H'1; Elimc H'1; intros H'1; inversion H'1; auto.
intros H'0 H'1.
apply stripInRzIn1 with (L1 := stripRz S); auto.
apply prodRzInR with (a := a) (L1 := stripInRz L (stripRz S)); auto.
apply stripRzDecProp1 with (S1 := S); auto.
Qed.

Theorem RestrictAddEq2 :
 forall (S : State) (L : list rNat) (a b : rZ),
 In (valRz a) L ->
 In (valRz b) L ->
 In zero L ->
 inclState (restrictState (addEq (a, b) S) L)
   (addEq (a, b) (restrictState S L)).
intros S L a b H' H'0 Eqz; apply inclStateIn; auto.
intros a0 b0 H'1.
cut (eqConstrState (addEq (a, b) S) a0 b0).
cut (In (valRz a0) L);
 [ intros Ina0L
 | apply restrictStateInZeroL with (S := addEq (a, b) S) (b := b0) ]; 
 auto.
cut (In (valRz b0) L);
 [ intros Inb0L
 | apply restrictStateInZeroR with (S := addEq (a, b) S) (a := a0) ]; 
 auto.
intros H'2; unfold addEq in H'2; inversion H'2.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto.
apply eqStateRzTrans with (b := a); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto.
apply eqStateRzTrans with (b := b); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto.
apply eqStateRzTrans with (b := b); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto.
apply eqStateRzTrans with (b := a); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto.
apply eqStateRzTrans with (b := rZComp a); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto; rewrite valRzComp; auto.
apply eqStateRzTrans with (b := rZComp b); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto; rewrite valRzComp; auto.
apply eqStateRzTrans with (b := rZComp b); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto; rewrite valRzComp; auto.
apply eqStateRzTrans with (b := rZComp a); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto; rewrite valRzComp; auto.
apply eqStateContr with (p := a) (q := b); auto.
apply eqStateIncl with (S1 := restrictState S L); auto.
apply restrictStateComp; auto; rewrite valRzComp; auto.
apply eqStateRzPImpeqConstrState; auto.
apply eqStateIncl with (S1 := restrictState (addEq (a, b) S) L); auto.
apply restrictStateIncl; auto.
Qed.
(* If the variable of the addition are in the list restriction commutrs with addition *)

Theorem RestrictAddEq :
 forall (S : State) (L : list rNat) (a b : rZ),
 In (valRz a) L ->
 In (valRz b) L ->
 In zero L ->
 eqState (restrictState (addEq (a, b) S) L)
   (addEq (a, b) (restrictState S L)).
intros S L a b H' H'0 H'1; red in |- *; split.
apply RestrictAddEq2; auto.
apply RestrictAddEq1; auto.
Qed.

Theorem doTripletRestrictAux1 :
 forall (S : State) (t : triplet) (L : list rNat) (p1 q1 p q r s : rZ),
 eqStateRz S p1 q1 ->
 eqStateRz (restrictState S L) p1 q1 ->
 In (valRz p) L ->
 In (valRz q) L ->
 In (valRz r) L ->
 In (valRz s) L ->
 In zero L ->
 (eqStateRz (restrictState S L) p1 q1 ->
  doTripletP (restrictState S L) t
    (addEq (p, q) (addEq (r, s) (restrictState S L)))) ->
 ex
   (fun S' : State =>
    doTripletP (restrictState S L) t S' /\
    eqState (restrictState (addEq (p, q) (addEq (r, s) S)) L) S').
intros S t L p1 q1 p q r s H' H'0 H'1 H'2 H'3 H'4 H'5 H'6;
 exists (addEq (p, q) (addEq (r, s) (restrictState S L))); 
 split; auto.
apply
 eqStateTrans with (S2 := addEq (p, q) (restrictState (addEq (r, s) S) L));
 auto.
apply RestrictAddEq; auto.
apply eqStateAddEq; auto.
apply RestrictAddEq; auto.
Qed.

Theorem doTripletRestrictAux2 :
 forall (S : State) (t : triplet) (L : list rNat) (p1 q1 p q : rZ),
 eqStateRz S p1 q1 ->
 eqStateRz (restrictState S L) p1 q1 ->
 In (valRz p) L ->
 In (valRz q) L ->
 In zero L ->
 (eqStateRz (restrictState S L) p1 q1 ->
  doTripletP (restrictState S L) t (addEq (p, q) (restrictState S L))) ->
 ex
   (fun S' : State =>
    doTripletP (restrictState S L) t S' /\
    eqState (restrictState (addEq (p, q) S) L) S').
intros S t L p1 q1 p q H' H'0 H'1 H'2 H'3 H'4;
 exists (addEq (p, q) (restrictState S L)); split; 
 auto.
apply RestrictAddEq; auto.
Qed.
(* If the variable of the triplet are in L, what we can with a state we can do it with its retriction *)

Theorem doTripletRestrict :
 forall (S1 S2 : State) (t : triplet) (L : list rNat),
 doTripletP S1 t S2 ->
 incl (ResTriplet t) L ->
 exists S3 : State,
   doTripletP (restrictState S1 L) t S3 /\ eqState (restrictState S2 L) S3.
intros S1 S2 t L H' H'0; inversion H';
 apply doTripletRestrictAux1 with (1 := H) ||
   apply doTripletRestrictAux2 with (1 := H); rewrite <- H0 in H'0;
 simpl in H'0; simpl in |- *; repeat rewrite valRzComp; 
 auto with datatypes; apply restrictStateComp; repeat rewrite valRzComp;
 auto with datatypes.
Qed.
(* To restrict is involutive *)

Theorem restrictStateInvol :
 forall (S : State) (L : list rNat),
 In zero L ->
 eqState (restrictState S L) (restrictState (restrictState S L) L).
intros S L H; red in |- *; split; auto.
2: apply restrictStateIncl; auto.
apply inclStateIn; auto.
intros a b H'.
apply restrictStateComp; auto.
apply restrictStateInZeroL with (S := S) (b := b); auto.
apply restrictStateInZeroR with (S := S) (a := a); auto.
Qed.
(* It is monotone *)

Theorem restricMonotone :
 forall (S1 S2 : State) (L1 L2 : list rNat),
 inclState S1 S2 ->
 incl L1 L2 -> inclState (restrictState S1 L1) (restrictState S2 L2).
intros S1 S2 L1 L2 H' H'0.
apply inclStateIn; auto.
intros a b H'1.
unfold restrictState in H'1; generalize H'1; clear H'1.
case (eqStateRzContrDec S1); auto.
intros H'1 H'2; unfold restrictState in |- *.
case (eqStateRzContrDec S2); auto.
intros H'3; case H'3; auto.
intros H'1 H'2.
apply restrictStateComp; auto.
red in H'0.
apply H'0.
apply stripInRzIn1 with (L1 := stripRz S1); auto.
apply prodRzInL with (b := b) (L2 := stripInRz L1 (stripRz S1)); auto.
apply stripRzDecProp1 with (S1 := S1); auto.
red in H'0.
apply H'0.
apply stripInRzIn1 with (L1 := stripRz S1); auto.
apply prodRzInR with (a := a) (L1 := stripInRz L1 (stripRz S1)); auto.
apply stripRzDecProp1 with (S1 := S1); auto.
apply eqStateIncl with (S1 := S1); auto.
apply eqStateIncl with (S1 := restrictState S1 L1); auto.
apply restrictStateIncl; auto.
unfold restrictState in |- *; case (eqStateRzContrDec S1); auto.
Qed.
(* It is compatible with the equality *)

Theorem restrictEqComp :
 forall (S1 S2 : State) (L : list rNat),
 eqState S1 S2 -> eqState (restrictState S1 L) (restrictState S2 L).
intros S1 S2 L H'; red in |- *; split; apply restricMonotone;
 auto with datatypes; red in H'; elim H'; auto.
Qed.

Theorem restrictDoTripletCompAux1 :
 forall (S1 : State) (L : list rNat) (p q r s : rZ),
 In (valRz p) L ->
 In (valRz q) L ->
 In (valRz r) L ->
 In (valRz s) L ->
 In zero L ->
 eqState (addEq (p, q) (addEq (r, s) (restrictState S1 L)))
   (restrictState (addEq (p, q) (addEq (r, s) (restrictState S1 L))) L).
intros S1 L p q r s H' H'0 H'1 H'2 H'3.
apply
 eqStateTrans with (S2 := restrictState (addEq (p, q) (addEq (r, s) S1)) L);
 auto.
apply
 eqStateTrans with (S2 := addEq (p, q) (restrictState (addEq (r, s) S1) L));
 auto.
apply eqStateAddEq; auto.
apply eqStateSym.
apply RestrictAddEq; auto with datatypes.
apply eqStateSym.
apply RestrictAddEq; auto with datatypes.
apply
 eqStateTrans
  with
    (S2 := restrictState (restrictState (addEq (p, q) (addEq (r, s) S1)) L) L);
 auto.
apply restrictStateInvol; auto with datatypes.
apply restrictEqComp; auto.
apply
 eqStateTrans with (S2 := addEq (p, q) (restrictState (addEq (r, s) S1) L));
 auto.
apply RestrictAddEq; auto with datatypes.
apply eqStateAddEq; auto.
apply RestrictAddEq; auto with datatypes.
Qed.

Theorem restrictDoTripletCompAux2 :
 forall (S1 : State) (L : list rNat) (p q : rZ),
 In (valRz p) L ->
 In (valRz q) L ->
 In zero L ->
 eqState (addEq (p, q) (restrictState S1 L))
   (restrictState (addEq (p, q) (restrictState S1 L)) L).
intros S1 L p q H' H'0 H'1.
apply eqStateTrans with (S2 := restrictState (addEq (p, q) S1) L); auto.
apply eqStateTrans with (S2 := addEq (p, q) (restrictState S1 L)); auto.
apply eqStateSym.
apply RestrictAddEq; auto with datatypes.
apply
 eqStateTrans
  with (S2 := restrictState (restrictState (addEq (p, q) S1) L) L); 
 auto.
apply restrictStateInvol; auto with datatypes.
apply restrictEqComp; auto.
apply RestrictAddEq; auto with datatypes.
Qed.
(* If the variables of the triplet are in the restriction, a restricted state stays restricted *)

Theorem restrictDoTripletComp :
 forall (S1 S2 : State) (t : triplet) (L : list rNat),
 incl (ResTriplet t) L ->
 doTripletP (restrictState S1 L) t S2 -> eqState S2 (restrictState S2 L).
intros S1 S2 t L H' H'0; inversion H'0; auto; rewrite <- H0 in H';
 simpl in H';
 apply restrictDoTripletCompAux1 || apply restrictDoTripletCompAux2;
 auto with datatypes; repeat rewrite valRzComp; auto with datatypes.
Qed.
(* What can do the restricted state can be done by the full state *)

Theorem doTripletRestrictInv :
 forall (S1 S2 : State) (t : triplet) (L : list rNat),
 incl (ResTriplet t) L ->
 doTripletP (restrictState S1 L) t S2 ->
 exists S3 : State,
   doTripletP S1 t S3 /\ eqState S3 (unionState (restrictState S2 L) S1).
intros S1 S2 t L H' H'0.
elim (doTripletCongruentEx (restrictState S1 L) S2 S1 t);
 [ intros S4 E; Elimc E; intros H'4 H'5 | idtac ]; 
 auto.
elim (doTripletEqCompEx (unionState S1 (restrictState S1 L)) S4 S1 t);
 [ intros S5 E; Elimc E; intros H'8 H'9 | idtac | idtac ]; 
 auto.
exists S5; split; auto.
apply eqStateTrans with (S2 := S4); auto.
apply eqStateTrans with (S2 := unionState S1 S2); auto.
apply eqStateTrans with (S2 := unionState S1 (restrictState S2 L)); auto.
apply unionStateEq; auto.
apply restrictDoTripletComp with (S1 := S1) (t := t); auto.
red in |- *; split; auto.
apply unionStateMin; auto.
apply restrictStateIncl; auto.
Qed.
(* Returns the list of variables of a list of triplets *)

Fixpoint ResTriplets (L : list triplet) : list rNat :=
  match L with
  | nil => zero :: nil
  | t :: L' => ResTriplet t ++ ResTriplets L'
  end.

Theorem zeroInL : forall L : list triplet, In zero (ResTriplets L).
intros L; elim L; simpl in |- *; auto with datatypes.
Qed.
Hint Resolve zeroInL.

Theorem ResTripletInResTriplets :
 forall (t : triplet) (L : list triplet),
 In t L -> incl (ResTriplet t) (ResTriplets L).
intros t L; elim L; simpl in |- *; auto.
intros H'; elim H'; auto.
intros a l H' H'0; Elimc H'0; intros H'0; [ rewrite <- H'0 | idtac ];
 auto with datatypes.
Qed.
(* What can do a state, it can be done by its reduction *)

Theorem doTripletsRestrict :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP S1 L S2 ->
 doTripletsP (restrictState S1 (ResTriplets L)) L
   (restrictState S2 (ResTriplets L)).
intros S1 S2 L H'; Elimc H'; clear L S1 S2; auto.
intros S1 S2 L H'; apply doTripletsRef; auto.
apply restrictEqComp; auto.
intros S1 S2 S3 L t H' H'0 H'1 H'2.
apply doTripletsRTrans with (S2 := restrictState S2 (ResTriplets L)); auto.
elim (doTripletRestrict S1 S2 t (ResTriplets L));
 [ intros S4 E; Elimc E; intros H'10 H'11 | idtac | idtac ]; 
 auto.
apply doTripletsRTrans with (S2 := restrictState S2 (ResTriplets L)); auto.
apply doTripletsTrans with (S2 := S4) (t := t); auto.
apply ResTripletInResTriplets; auto.
Qed.

Theorem restrictDoTripletsCompAux1 :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP S1 L S2 ->
 forall S3 : State,
 eqState S1 (restrictState S3 (ResTriplets L)) ->
 eqState S2 (restrictState S2 (ResTriplets L)).
intros S1 S2 L H'; Elimc H'; clear L S1 S2; auto.
intros S1 S2 L H' S3 H'0.
apply eqStateTrans with (S2 := S1); auto.
apply eqStateTrans with (S2 := restrictState S3 (ResTriplets L)); auto.
apply
 eqStateTrans
  with
    (S2 := restrictState (restrictState S3 (ResTriplets L)) (ResTriplets L));
 auto.
apply restrictStateInvol; auto.
apply restrictEqComp; auto.
apply eqStateTrans with (S2 := S1); auto.
intros S1 S2 S3 L t H' H'0 H'1 H'2 S0 H'3.
elim (doTripletEqCompEx S1 S2 (restrictState S0 (ResTriplets L)) t);
 [ intros S4 E; Elimc E; intros H'10 H'11 | idtac | idtac ]; 
 auto.
apply H'2 with (S0 := S2); auto.
apply eqStateTrans with (S2 := S4); auto.
apply eqStateTrans with (S2 := restrictState S4 (ResTriplets L)); auto.
apply restrictDoTripletComp with (S1 := S0) (t := t); auto.
apply ResTripletInResTriplets; auto.
apply restrictEqComp; auto.
Qed.
(* A restricted state gives a restricted state by doTripletsP *)

Theorem restrictDoTripletsComp :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP (restrictState S1 (ResTriplets L)) L S2 ->
 eqState S2 (restrictState S2 (ResTriplets L)).
intros S1 S2 L H'.
apply
 restrictDoTripletsCompAux1
  with (S1 := restrictState S1 (ResTriplets L)) (S3 := S1); 
 auto.
Qed.
(* what can be done by a restricted state can be done by the full state *)

Theorem doTripletsRestrictInv :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP (restrictState S1 (ResTriplets L)) L S2 ->
 doTripletsP S1 L (unionState (restrictState S2 (ResTriplets L)) S1).
intros S1 S2 L H'.
lapply (restrictDoTripletsComp S1 S2 L); [ intros H'3 | idtac ]; auto.
apply
 doTripletsComp
  with
    (S1 := unionState S1 (restrictState S1 (ResTriplets L)))
    (S2 := unionState S1 S2); auto.
apply doTripletCongruent; auto.
red in |- *; split; auto.
apply unionStateMin; auto.
apply restrictStateIncl; auto.
apply eqStateTrans with (S2 := unionState S2 S1); auto.
Qed.
(* A restricted state produces always a restricted state *)

Theorem doTripletsRestrictBis :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP S1 L S2 ->
 eqState S1 (restrictState S1 (ResTriplets L)) ->
 eqState S2 (restrictState S2 (ResTriplets L)).
intros S1 S2 L H' H'0.
apply restrictDoTripletsComp with (S1 := S1); auto.
apply doTripletsComp with (S1 := S1) (S2 := S2); auto.
Qed.
Transparent eqStateRzContrDec. 