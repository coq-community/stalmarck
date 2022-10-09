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

(** * interImplement2

Pierre Letouzey & Laurent Thery

Implement the intersection (2 files)
*)

From Stalmarck Require Import rZ.
From Stalmarck Require Import OrderedListEq.
From Stalmarck Require Import LetP.
From Coq Require Import Relation_Definitions.
From Stalmarck Require Import state.
From Stalmarck Require Import restrictState.
From Stalmarck Require Import ltState.
From Stalmarck Require Export memoryImplement.
From Stalmarck Require Export addArray.
From Stalmarck Require Export interImplement.

Section inter.
(* We simply add to an array  all the equation formed from an element of L
    and the minimal element b that are in both equivalent classes *)

Fixpoint addInterAux (Ar1 Ar2 : rArray vM) (L : list rZ) {struct L} :
 rArray vM -> rArray vM * list rZ :=
  fun Ar3 : rArray vM =>
  match L with
  | nil => (Ar3, nil)
  | a :: L1 =>
      match addInterAux Ar1 Ar2 L1 Ar3 with
      | (Ar3', L2) =>
          match
            addEqMem Ar3' (rZPlus (valRz a)) (getEquivMin Ar1 Ar2 (valRz a))
          with
          | triple Ar3'' b L2' => (Ar3'', appendRz L2 L2')
          end
      end
  end.

Theorem rArrayContradictory :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (S : State),
 rArrayState Ar S -> ~ contradictory S.
intros Ar H' S H'0; red in |- *; intros H'1; case H'1.
intros x H'2; absurd (evalZ Ar x = evalZ Ar (rZComp x)).
rewrite evalZComp; auto with stalmarck.
apply rArrayStateDef1 with (S := S); auto with stalmarck.
Qed.
(* I dont like this but it makes Coq run faster *)
Opaque addEqMem.

Theorem addInterAuxProp :
 forall (L : list rZ) (Ar1 Ar2 Ar3 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (War3 : wellFormedArray Ar3)
   (S1 S2 S3 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 rArrayState Ar3 S3 ->
 inclState S1 S2 ->
 inclState S1 S3 ->
 match addInterAux Ar2 Ar3 L Ar1 with
 | (Ar4, L1) =>
     wellFormedArray Ar4 /\
     (exists S4 : State,
        rArrayState Ar4 S4 /\
        inclState S4 S2 /\
        inclState S4 S3 /\
        inclState S1 S4 /\
        (forall a : rNat,
         InRz (rZPlus a) L -> eqStateRz S4 (rZPlus a) (getEquivMin Ar2 Ar3 a))) /\
     (forall e : rNat,
      ~ InRz (rZPlus e) L1 -> rArrayGet _ Ar4 e = rArrayGet _ Ar1 e) /\
     OlistRz L1
 end.
intros L Ar1 Ar2 Ar3 H' H'0 H'1 S1 S2 S3 H'2 H'3 H'4 H'5 H'6.
elim L; simpl in |- *.
split; [ idtac | split; [ exists S1; repeat split | idtac ] ]; auto with stalmarck.
intros H'7; apply rArrayStateDef1 with (S := S1); auto with stalmarck.
intros H'7; apply rArrayStateDef2 with (Ar := Ar1); auto with stalmarck.
intros a H'7; inversion H'7.
split; auto with stalmarck.
red in |- *; apply OlistNil; auto with stalmarck.
intros a l; case (addInterAux Ar2 Ar3 l Ar1).
intros Ar3' L2 H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9;
 Elimc H'8; intros S4 E; Elimc E; intros H'8 H'10; 
 Elimc H'10; intros H'10 H'11; Elimc H'11; intros H'11 H'12; 
 Elimc H'12; intros H'12 H'13.
Elimc H'9; intros H'9 H'14.
generalize
 (addEqMemCorrect Ar3' (rZPlus (valRz a)) (getEquivMin Ar2 Ar3 (valRz a)) S4
    H'7 H'8);
 case (addEqMem Ar3' (rZPlus (valRz a)) (getEquivMin Ar2 Ar3 (valRz a)));
 auto with stalmarck.
intros Ar3'' b L2'; case b.
intros H'15; absurd (contradictory S2).
apply rArrayContradictory with (Ar := Ar2); auto with stalmarck.
case H'15.
intros x H'16; exists x.
apply
 eqStateIncl
  with (S1 := addEq (rZPlus (valRz a), getEquivMin Ar2 Ar3 (valRz a)) S4);
 auto with stalmarck.
apply inclStateAddEqInv; auto with stalmarck.
apply getEquivMinEq1; auto with stalmarck.
intros H'15; Elimc H'15; intros H'15 H'16; Elimc H'16; intros H'16 H'17;
 Elimc H'17; intros H'17 H'18.
split; auto with stalmarck; split; auto with stalmarck.
exists (addEq (rZPlus (valRz a), getEquivMin Ar2 Ar3 (valRz a)) S4);
 repeat split; auto with stalmarck.
intros H'19; apply rArrayStateDef1 with (1 := H'16); auto with stalmarck.
intros H'19; apply rArrayStateDef2 with (1 := H'16); auto with stalmarck.
apply inclStateAddEqInv; auto with stalmarck.
apply getEquivMinEq1; auto with stalmarck.
apply inclStateAddEqInv; auto with stalmarck.
apply getEquivMinEq2; auto with stalmarck.
apply inclStateTrans with S4; auto with stalmarck.
intros a0 H'19; inversion H'19.
case eqRzElim with (1 := H1); auto with stalmarck.
intros H'20; rewrite <- H'20; simpl in |- *; auto with stalmarck.
intros H'20; replace a with (rZComp (rZPlus a0)).
simpl in |- *; auto with stalmarck.
rewrite H'20; rewrite rZCompInv; auto with stalmarck.
apply eqStateaddEq2; auto with stalmarck.
split; auto with stalmarck.
intros e H'19.
rewrite H'18; auto with stalmarck.
apply H'9; auto with stalmarck.
Contradict H'19; auto with stalmarck.
unfold appendRz in |- *.
generalize (appendfInclEq1 _ rZlt eqRz rZltEDec L2 L2'); intros H'22;
 inversion H'22; auto with stalmarck.
apply H; auto with stalmarck.
Contradict H'19; auto with stalmarck.
unfold appendRz in |- *.
generalize (appendfInclEq2 _ rZlt eqRz eqrZSym eqrZTrans rZltEDec L2 L2');
 intros H'20; inversion H'20; auto with stalmarck.
apply H; auto with stalmarck.
red in |- *; unfold appendRz in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
Qed.

(* Ok, now to compute the intersection we simply take the intersection of the diff lists
    that contains the element that have changed in both arrays *)

Definition interMem (Ar1 Ar2 Ar3 : rArray vM) (L1 L2 : list rZ) :=
  addInterAux Ar1 Ar2 (interf _ rZlt eqRz rZltEDec L1 L2) Ar3.

Definition interMemProp :
  forall (Ar1 Ar2 Ar3 : rArray vM) (War1 : wellFormedArray Ar1)
    (War2 : wellFormedArray Ar2) (War3 : wellFormedArray Ar3)
    (L1 L2 : list rZ),
  OlistRz L1 ->
  OlistRz L2 ->
  forall S1 S2 S3 : State,
  rArrayState Ar1 S1 ->
  rArrayState Ar2 S2 ->
  rArrayState Ar3 S3 ->
  inclState S3 S1 ->
  inclState S3 S2 ->
  (forall e : rNat,
   ~ InRz (rZPlus e) L1 -> rArrayGet _ Ar1 e = rArrayGet _ Ar3 e) ->
  (forall e : rNat,
   ~ InRz (rZPlus e) L2 -> rArrayGet _ Ar2 e = rArrayGet _ Ar3 e) ->
  match interMem Ar1 Ar2 Ar3 L1 L2 with
  | (Ar4, L3) =>
      wellFormedArray Ar4 /\
      rArrayState Ar4 (interState S1 S2) /\
      (forall e : rNat,
       ~ InRz (rZPlus e) L3 -> rArrayGet _ Ar4 e = rArrayGet _ Ar3 e) /\
      OlistRz L3
  end.
intros Ar1 Ar2 Ar3 War1 War2 War3 L1 L2 Ol1 Ol2 S1 S2 S3 Sar1 Sar2 Sar3 I1 I2
 D1 D2.
unfold interMem in |- *;
 generalize
  (addInterAuxProp (interf _ rZlt eqRz rZltEDec L1 L2) Ar3 Ar1 Ar2 War3 War1
     War2 S3 S1 S2 Sar3 Sar1 Sar2 I1 I2);
 case (addInterAux Ar1 Ar2 (interf rZ rZlt eqRz rZltEDec L1 L2) Ar3).
intros Ar4 L4 H'; Elimc H'; intros H' H'0; Elimc H'0; intros H'0 H'1;
 Elimc H'1; intros H'1 H'2.
split; [ idtac | split; [ idtac | split ] ]; auto with stalmarck.
Elimc H'0; intros S4 E; Elimc E; intros H'0 H'3; Elimc H'3; intros H'3 H'4;
 Elimc H'4; intros H'4 H'5; Elimc H'5; intros H'5 H'6.
apply rArrayStateEqState with (S := S4); auto with stalmarck.
split; auto with stalmarck.
apply getEquivInter with (Ar1 := Ar1) (Ar2 := Ar2); auto with stalmarck.
intros a.
case (InRzDec (rZPlus a) L1); intros In1.
case (InRzDec (rZPlus a) L2); intros In2.
apply H'6; auto with stalmarck.
cut (InclEq _ eqRz (rZPlus a :: nil) (interf rZ rZlt eqRz rZltEDec L1 L2));
 auto with stalmarck.
intros H'7; inversion H'7.
apply H; apply InEqHead; auto with stalmarck.
apply interfMin; auto with stalmarck.
try exact rZltEqComp.
apply OlistOne; auto with stalmarck.
apply InclEqDef; auto with stalmarck.
intros a0 H'7; inversion H'7; auto with stalmarck.
apply InEqComp with (a := rZPlus a); auto with stalmarck.
inversion H1.
apply InclEqDef; auto with stalmarck.
intros a0 H'7; inversion H'7; auto with stalmarck.
apply InEqComp with (a := rZPlus a); auto with stalmarck.
inversion H1.
rewrite getEquivIdL with (S1 := S1) (S2 := S2); auto with stalmarck.
replace (evalZ Ar2 (rZPlus a)) with (evalZ Ar3 (rZPlus a)).
apply eqStateIncl with (S1 := S3); auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar3); auto with stalmarck.
rewrite evalZInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
unfold evalN in |- *.
rewrite (D2 a); auto with stalmarck.
replace (evalZ Ar2 (rZPlus a)) with (evalZ Ar3 (rZPlus a)).
apply eqStateIncl with (S1 := S3); auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar3); auto with stalmarck.
rewrite evalZInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
unfold evalN in |- *.
rewrite (D2 a); auto with stalmarck.
rewrite getEquivIdR with (S1 := S1) (S2 := S2); auto with stalmarck.
replace (evalZ Ar1 (rZPlus a)) with (evalZ Ar3 (rZPlus a)).
apply eqStateIncl with (S1 := S3); auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar3); auto with stalmarck.
rewrite evalZInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
unfold evalN in |- *.
rewrite (D1 a); auto with stalmarck.
replace (evalZ Ar1 (rZPlus a)) with (evalZ Ar3 (rZPlus a)).
apply eqStateIncl with (S1 := S3); auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar3); auto with stalmarck.
rewrite evalZInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
unfold evalN in |- *.
rewrite (D1 a); auto with stalmarck.
Qed.
Transparent addEqMem.
End inter.
