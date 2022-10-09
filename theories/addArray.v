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

(** * addArray

Pierre Letouzey & Laurent Thery

Addition of an equation to a well-formed array
*)

From Stalmarck Require Export wfArray.

(* We define the simultaneous update of arrays *)

Fixpoint rArraySetList (Ar : rArray vM) (a : rZ) (L : list rZ) {struct L} :
 rArray vM :=
  match L with
  | nil => Ar
  | m :: ml' =>
      rArraySet _ (rArraySetList Ar a ml') (valRz m) (ref (samePolRz m a))
  end.

Theorem rArraySetListInv1 :
 forall (Ar : rArray vM) (a : rZ) (mL : list rZ) (m : rZ),
 ~ InRz m mL ->
 rArrayGet _ (rArraySetList Ar a mL) (valRz m) = rArrayGet _ Ar (valRz m).
intros Ar a mL; generalize Ar; Elimc mL; clear Ar; simpl in |- *; auto with stalmarck.
intros a0 l H' Ar m H'0.
rewrite rArrayDef2; auto with stalmarck.
apply H'; auto with stalmarck.
Contradict H'0; auto with stalmarck.
red in |- *; apply InEqSkip; auto with stalmarck.
Contradict H'0; auto with stalmarck.
red in |- *; apply InEqHead; auto with stalmarck; red in |- *; auto with stalmarck.
Qed.

Theorem rArraySetListInv2 :
 forall (Ar : rArray vM) (a : rZ) (mL : list rZ) (m : rZ),
 OlistRz mL ->
 In m mL ->
 rArrayGet _ (rArraySetList Ar a mL) (valRz m) = ref (samePolRz m a).
intros Ar a mL; generalize Ar; elim mL; simpl in |- *; auto with stalmarck.
intros Ar0 m H' H'0; elim H'0; auto with stalmarck.
intros a0 l H' Ar0 m H'0 H'1; Elimc H'1; intros H'1;
 [ rewrite <- H'1 | idtac ]; auto with stalmarck.
apply rArrayDef1; auto with stalmarck.
rewrite rArrayDef2; auto with stalmarck.
apply H'; auto with stalmarck.
red in |- *; apply OlistInv with (a := a0); auto with stalmarck.
red in |- *; intros H'2; absurd (InEq _ eqRz m l); auto with stalmarck.
apply OlistUniqueEq with (ltA := rZlt) (a := a0); auto with stalmarck.
exact rZltEqComp.
apply inImpInEq; auto with stalmarck.
Qed.
(* a minimal element does not belong to its pointer list *)

Theorem DisjbLb :
 forall (b : rNat) (Lb : list rZ) (Ar : rArray vM) 
   (War : wellFormedArray Ar) (getb : rArrayGet _ Ar b = class Lb),
 DisjointRz (rZPlus b :: nil) Lb.
intros b Lb Ar War getb; red in |- *; simpl in |- *.
apply DisjointDef; simpl in |- *; auto with stalmarck.
intros a H'; inversion_clear H'.
apply NotInEqComp with (a := rZPlus b); auto with stalmarck.
apply wellFormedArrayInImpNotEqSimpl with (1 := War); auto with stalmarck.
inversion H.
Qed.

Definition appendRz := appendf rZ rZlt eqRz rZltEDec.
(* This theorem is needed when we will need to generate the new equivalent class
  after adding an equation, append needs a proof that the two lists that are appended are disjoint *)

Theorem DisjLaLc :
 forall (a b : rNat) (Neqab : a <> b) (La Lb : list rZ) 
   (Ar : rArray vM) (War : wellFormedArray Ar)
   (geta : rArrayGet _ Ar a = class La) (getb : rArrayGet _ Ar b = class Lb),
 DisjointRz La (appendRz (rZPlus b :: nil) Lb).
intros a b ltab La Lb Ar War geta getb.
cut (DisjointRz La Lb);
 [ intros DLaLb | apply wfDisjoint with (3 := geta) (4 := getb); auto with stalmarck ].
red in |- *; auto with stalmarck.
apply DisjointCom; unfold appendRz in |- *; apply appendfDisjoint; auto with stalmarck.
apply DisjbLb with (2 := getb); auto with stalmarck.
apply DisjointDef; simpl in |- *; auto with stalmarck.
intros a0 H'; inversion_clear H'.
apply NotInEqComp with (a := rZPlus b); auto with stalmarck.
apply wellFormedArrayInImpNotEq with (2 := getb) (3 := geta); auto with stalmarck.
inversion_clear H.
apply DisjointCom; auto with stalmarck.
Qed.
Section AaddD.
Variable n a b : rNat.
Variable pol : rZ.
Variable La Lb : list rZ.
Variable Ar : rArray vM.
Hypothesis War : wellFormedArray Ar.
Hypothesis rltab : rlt a b.
Hypothesis geta : rArrayGet _ Ar a = class La.
Hypothesis getb : rArrayGet _ Ar b = class Lb.

(*Append with an auxilary function pol *)

Definition fappendRz := fappendf rZ rZlt eqRz rZltEDec (samePolRz pol).
(* a and b are two minimal elements whose classes are La and Lb
   we know also that a < b
   What we need to do to perform the update a=+/- b where pol gives the polarity:
   1) Take all the element of Lb and make them point to a
   2) Make b  point to a
   3) Update the class of a to La @ [b|Lb] *)

Definition updateArray : rArray vM.
exact
 (rArraySet vM
    (rArraySetList Ar (samePolRz pol (rZPlus a))
       (appendRz (rZPlus b :: nil) Lb)) a
    (class (fappendRz La (appendRz (rZPlus b :: nil) Lb)))).
Defined.
(* a contains the proper equivalence class *)

Theorem updateArraya :
 rArrayGet _ updateArray a =
 class (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold updateArray in |- *; unfold LetP in |- *; simpl in |- *.
rewrite rArrayDef1; auto with stalmarck.
Qed.
(* b is now a pointer *)

Theorem updateArrayb :
 rArrayGet _ updateArray b = ref (samePolRz pol (rZPlus a)).
unfold updateArray in |- *.
cut (a <> b); [ intros Neqab | apply rltDef2; auto with stalmarck ].
rewrite rArrayDef2; auto with stalmarck.
pattern b at 2 in |- *; replace b with (valRz (rZPlus b)); auto with stalmarck.
rewrite rArraySetListInv2; auto with stalmarck.
red in |- *; unfold appendRz in |- *; apply appendfOlist; auto with stalmarck.
exact rZltEqComp.
apply OlistOne; auto with stalmarck.
apply wfOl with (2 := getb); auto with stalmarck.
generalize appendfIncl1; unfold incl in |- *; auto with datatypes stalmarck.
intros H'; unfold appendRz in |- *; apply H'; auto with datatypes stalmarck.
apply DisjbLb with (2 := getb); auto with stalmarck.
Qed.
(* The ones that were pointing to b now point to a *)

Theorem updateArrayInb :
 forall c : rZ,
 In c Lb ->
 rArrayGet _ updateArray (valRz c) =
 ref (samePolRz c (samePolRz pol (rZPlus a))).
intros c InLb; unfold updateArray in |- *.
rewrite rArrayDef2; auto with stalmarck.
rewrite rArraySetListInv2; auto with stalmarck.
red in |- *; unfold appendRz in |- *; apply appendfOlist; auto with stalmarck.
exact rZltEqComp.
apply OlistOne; auto with stalmarck.
apply wfOl with (2 := getb); auto with stalmarck.
generalize appendfIncl2; unfold incl in |- *; auto with datatypes stalmarck.
unfold appendRz in |- *; intros H'; apply H'; auto with stalmarck.
apply DisjbLb with (2 := getb); auto with stalmarck.
red in |- *; intros H'; absurd (InRz (rZPlus a) Lb); auto with stalmarck.
apply wellFormedArrayInImpNotEq with (2 := geta) (3 := getb); auto with stalmarck.
rewrite H'; auto with stalmarck.
red in |- *; apply InEqComp with (a := c); auto with stalmarck.
apply inImpInEq; auto with stalmarck.
Qed.
(* otherwise nothing has changed *)

Theorem updateArrayOtherwise :
 forall c : rNat,
 ~ InRz (rZPlus c) Lb ->
 c <> a -> c <> b -> rArrayGet _ updateArray c = rArrayGet _ Ar c.
intros c NotPInb NotEqca NotEqcb.
unfold updateArray in |- *.
replace c with (valRz (rZPlus c)); auto with stalmarck.
rewrite rArrayDef2; auto with stalmarck.
rewrite rArraySetListInv1; auto with stalmarck.
red in |- *; intros H'.
unfold appendRz in H'.
case appendfInvEq with (1 := H'); auto with stalmarck; intros H'0; inversion_clear H'0;
 inversion H; auto with stalmarck.
Qed.
(* Now we want to show that the resulting array is well formed *)

Definition updateArrayPointerDecrease : pointerDecrease updateArray.
apply pointerDecreaseDef; auto with stalmarck.
intros r s H'.
case (rNatDec r a); intros eqra.
generalize H'; rewrite eqra; rewrite updateArraya; auto with stalmarck; clear H'; intros H';
 discriminate.
case (rNatDec r b); intros eqrb.
generalize H'; rewrite eqrb; auto with stalmarck; rewrite updateArrayb; auto with stalmarck; clear H';
 intros H'; inversion H'.
unfold rZlt in |- *; simpl in |- *; red in |- *.
rewrite samePolRzValRz; simpl in |- *; auto with stalmarck.
case (InRzDec (rZPlus r) Lb); intros inPb.
case (InEqInv (rZPlus r) Lb); auto with stalmarck; intros inPb'.
generalize H'; replace r with (valRz (rZPlus r)); auto with stalmarck;
 rewrite updateArrayInb; auto with stalmarck; clear H'; intros H'; 
 inversion H'.
simpl in |- *; red in |- *; rewrite samePolRzValRz; auto with stalmarck.
apply rltTrans with (y := b); auto with stalmarck.
change (rlt b (valRz (rZPlus r))) in |- *.
apply wellFormedArrayInImpLt with (Ar := Ar) (La := Lb); auto with stalmarck.
generalize H'; replace r with (valRz (rZMinus r)); auto with stalmarck;
 rewrite updateArrayInb; auto with stalmarck; clear H'; intros H'; 
 inversion H'.
simpl in |- *; apply rVltrZComp; auto with stalmarck.
red in |- *; rewrite samePolRzValRz; simpl in |- *; auto with stalmarck.
apply rltTrans with (y := b); auto with stalmarck.
change (rlt b (valRz (rZMinus r))) in |- *.
apply wellFormedArrayInImpLt with (Ar := Ar) (La := Lb); auto with stalmarck.
apply wfPd with (Ar := Ar); auto with stalmarck.
rewrite <- H'.
apply sym_equal.
apply updateArrayOtherwise; auto with stalmarck.
Qed.
(* if we are a minimal element different of a, nothing has changed *)

Theorem updateGetIsClass :
 forall (r : rNat) (Lr : list rZ),
 rArrayGet _ updateArray r = class Lr ->
 r <> a -> rArrayGet _ Ar r = class Lr.
intros r Lr H' H'0.
case (rNatDec r b); intros Eqb; auto with stalmarck.
generalize H'; rewrite Eqb; auto with stalmarck; rewrite updateArrayb; clear H'; intros H';
 discriminate.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto with stalmarck.
case (InEqInv (rZPlus r) Lb); auto with stalmarck; intros InRLb'.
generalize H'; replace r with (valRz (rZPlus r)); auto with stalmarck;
 rewrite updateArrayInb; auto with stalmarck; clear H'; intros H'; 
 discriminate.
generalize H'; replace r with (valRz (rZMinus r)); auto with stalmarck;
 rewrite updateArrayInb; auto with stalmarck; clear H'; intros H'; 
 discriminate.
rewrite <- H'; apply sym_equal.
apply updateArrayOtherwise; auto with stalmarck.
Qed.
(* Classes are ordered *)

Definition updateArrayOlist : OlistArray updateArray.
apply OlistArrayDef; auto with stalmarck.
intros r Lr H'.
case (rNatDec r a); intros Eqt.
generalize H'; rewrite Eqt; auto with stalmarck; rewrite updateArraya; auto with stalmarck; clear H';
 intros H'.
replace Lr with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).


 inversion H'.
red in |- *; unfold fappendRz in |- *; apply fappendfOlist; auto with stalmarck.
intros; apply samePolRzEqRz; auto with stalmarck.
try exact rZltEqComp.
apply wfOl with (2 := geta); auto with stalmarck.
unfold appendRz in |- *; apply appendfOlist; auto with stalmarck.
exact rZltEqComp.
apply OlistOne; auto with stalmarck.
apply wfOl with (2 := getb); auto with stalmarck.
injection H'; trivial.
apply wfOl with (Ar := Ar) (r := r); auto with stalmarck.
apply updateGetIsClass with (1 := H'); auto with stalmarck.
Qed.
(* The ref and the class are properly related *)

Theorem updateArrayPointToRef : pointToClassRef updateArray.
apply pointToClassRefDef; auto with stalmarck.
intros r s t H'1.
case (rNatDec (valRz s) a); intros eqsa.
rewrite eqsa; auto with stalmarck; rewrite updateArraya; red in |- *; intros H'2;
 discriminate.
case (rNatDec r a); intros eqra.
generalize H'1; rewrite eqra; auto with stalmarck; rewrite updateArraya; auto with stalmarck; intros;
 discriminate.
case (rNatDec r b); intros eqrb; auto with stalmarck.
generalize H'1; rewrite eqrb; auto with stalmarck; rewrite updateArrayb; auto with stalmarck; clear H'1;
 intros H'1; case eqsa; inversion H'1.
apply samePolRzValRz; auto with stalmarck.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto with stalmarck.
case (InEqInv (rZPlus r) Lb); auto with stalmarck; intros InRLb'.
generalize H'1; replace r with (valRz (rZPlus r)); auto with stalmarck;
 rewrite updateArrayInb; auto with stalmarck; clear H'1; intros H'1; 
 case eqsa; inversion H'1; simpl in |- *; auto with stalmarck.
apply samePolRzValRz; auto with stalmarck.
generalize H'1; replace r with (valRz (rZMinus r)); auto with stalmarck;
 rewrite updateArrayInb; auto with stalmarck; clear H'1; intros H'1; 
 case eqsa; inversion H'1; simpl in |- *; auto with stalmarck.
simpl in |- *; rewrite valRzComp; rewrite samePolRzValRz; auto with stalmarck.
generalize H'1; auto with stalmarck; rewrite updateArrayOtherwise; auto with stalmarck; clear H'1;
 intros H'1.
case (rNatDec (valRz s) b); intros eqsb; auto with stalmarck.
case InRLb; red in |- *.
apply InEqComp with (a := samePol s r); auto with stalmarck.
apply inImpInEq; auto with stalmarck.
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite eqsb; auto with stalmarck; rewrite updateArrayb; auto with stalmarck.
case s; simpl in |- *; auto with stalmarck.
case (InRzDec s Lb); intros InRLb'; auto with stalmarck.
case (InEqInv s Lb); auto with stalmarck; intros InRLb''.
absurd (rArrayGet _ Ar (valRz s) = ref (samePol s b)); auto with stalmarck.
inversion War.
inversion pR.
apply H0 with (r := r); auto with stalmarck.
inversion War.
inversion pC.
apply H0 with (Lr := Lb); auto with stalmarck.
absurd (rArrayGet _ Ar (valRz (rZComp s)) = ref (samePol (rZComp s) b)).
rewrite valRzComp; auto with stalmarck.
inversion War.
inversion pR.
apply H0 with (r := r); auto with stalmarck.
inversion War.
inversion pC.
apply H0 with (Lr := Lb); auto with stalmarck.
rewrite updateArrayOtherwise; auto with stalmarck.
inversion War.
inversion pR.
apply H0 with (r := r); auto with stalmarck.
red in |- *; intros H'2; case InRLb'; red in |- *.
apply InEqComp with (a := rZPlus (valRz s)); auto with stalmarck.
Qed.

Theorem updatePointToClassClassRef1 :
 forall (r : rNat) (s : rZ) (Lr : list rZ),
 rArrayGet _ updateArray r = class Lr ->
 In s Lr -> rArrayGet _ updateArray (valRz s) = ref (samePol s r).
intros r s Lr.
case (rNatDec r a); intros eqra.
rewrite eqra; auto with stalmarck; rewrite updateArraya; auto with stalmarck; intros H'; inversion H'.
unfold fappendRz in |- *; unfold appendRz in |- *; intros Eqt.
case (fappendfInv rZ) with (6 := Eqt); try exact rZltEqComp; auto with stalmarck.
intro; apply samePolRzEqRz; auto with stalmarck.
intro Eqt'; rewrite updateArrayOtherwise; auto with stalmarck.
apply wfPcc1 with (Lr := La); auto with stalmarck.
red in |- *; intros H'2; absurd (a = b); auto with stalmarck.
red in |- *; intros H'3; absurd (rlt a b); auto with stalmarck.
rewrite <- H'3; auto with stalmarck.
apply
 wellFormedArrayInRzBothImpEq
  with (2 := geta) (3 := getb) (c := rZPlus (valRz s)); 
 auto with stalmarck.
red in |- *.
unfold InRz in |- *.
unfold InRz in |- *; intros; apply InEqComp with (a := s); auto with stalmarck.
apply inImpInEq; auto with stalmarck.
red in |- *; intros H'2; absurd (InRz (rZPlus a) La).
apply wellFormedArrayInImpNotEqSimpl with (2 := geta); auto with stalmarck.
rewrite <- H'2.
unfold InRz in |- *; simpl in |- *; intros; apply InEqComp with (a := s);
 auto with stalmarck.
apply inImpInEq; auto with stalmarck.
red in |- *; intros H'2; absurd (InRz (rZPlus b) La); auto with stalmarck.
apply wellFormedArrayInImpNotEq with (2 := getb) (3 := geta); auto with stalmarck.
rewrite <- H'2.
unfold InRz in |- *; simpl in |- *; intros; apply InEqComp with (a := s);
 auto with stalmarck.
apply inImpInEq; auto with stalmarck.
intro Eqt';
 elim
  (appendfInv rZ rZlt eqRz rZltEDec (rZPlus b :: nil) Lb (samePolRz pol s));
 auto with stalmarck.
simpl in |- *; intros Int.
Elimc Int; intros Int; [ idtac | Elimc Int; clear Int ]; auto with stalmarck.
replace (valRz s) with b.
rewrite updateArrayb; auto with stalmarck.
generalize Int; case s; case pol; simpl in |- *; auto with stalmarck; intros; discriminate.
rewrite <- (samePolRzValRz pol b); rewrite Int; case pol; case s;
 simpl in |- *; auto with stalmarck.
intros Int; replace (valRz s) with (valRz (samePolRz pol s)); auto with stalmarck.
rewrite updateArrayInb; auto with stalmarck.
case pol; case s; simpl in |- *; auto with stalmarck.
case pol; case s; simpl in |- *; auto with stalmarck.
rewrite <-
 (PolyListAux.map_id rZ (samePolRz pol) (samePolRzsamePolRz pol)
    (appendf rZ rZlt eqRz rZltEDec (rZPlus b :: nil) Lb))
 ; auto with stalmarck.
apply in_map; auto with stalmarck.
case (rNatDec r b); intros eqrb.
rewrite eqrb; auto with stalmarck; rewrite updateArrayb; auto with stalmarck; intros H'; discriminate.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto with stalmarck.
case (InEqInv (rZPlus r) Lb); auto with stalmarck; intros InRLb'.
replace r with (valRz (rZPlus r)); auto with stalmarck; rewrite updateArrayInb; auto with stalmarck;
 intros H'; discriminate.
replace r with (valRz (rZMinus r)); auto with stalmarck; rewrite updateArrayInb; auto with stalmarck;
 intros H'; discriminate.
case (rNatDec (valRz s) a); intros eqsa.
intros H' H'0.
absurd (InRz (rZPlus a) Lr); auto with stalmarck.
apply wellFormedArrayInImpNotEq with (Ar := Ar) (b := r) (La := La); auto with stalmarck.
apply updateGetIsClass with (1 := H'); auto with stalmarck.
red in |- *; apply InEqComp with (a := s); auto with stalmarck.
apply inImpInEq; auto with stalmarck.
case (rNatDec (valRz s) b); intros eqsb.
intros H' H'0.
absurd (InRz (rZPlus b) Lr); auto with stalmarck.
apply wellFormedArrayInImpNotEq with (Ar := Ar) (b := r) (La := Lb); auto with stalmarck.
apply updateGetIsClass with (1 := H'); auto with stalmarck.
red in |- *; apply InEqComp with (a := s); auto with stalmarck.
apply inImpInEq; auto with stalmarck.
rewrite updateArrayOtherwise; auto with stalmarck.
intros H' H'0; rewrite updateArrayOtherwise; auto with stalmarck.
apply wfPcc1 with (Lr := Lr); auto with stalmarck.
red in |- *; intros H'2; absurd (r = b); auto with stalmarck.
apply
 wellFormedArrayInRzBothImpEq with (Ar := Ar) (c := s) (La := Lr) (Lb := Lb);
 auto with stalmarck.
red in |- *; apply InEqComp with (a := s); auto with stalmarck.
apply inImpInEq; auto with stalmarck.
red in |- *; apply InEqComp with (a := rZPlus (valRz s)); auto with stalmarck.
Qed.

Theorem updatePointToClassClassRef2 :
 forall (r : rNat) (s : rZ) (Ls : list rZ),
 rArrayGet _ updateArray r = ref s ->
 rArrayGet _ updateArray (valRz s) = class Ls -> In (samePol s r) Ls.
intros r s Ls.
case (rNatDec r a); intros eqra.
rewrite eqra; auto with stalmarck; rewrite updateArraya; auto with stalmarck; intros H'; inversion H'.
case (rNatDec r b); intros eqrb.
rewrite eqrb; auto with stalmarck; rewrite updateArrayb; auto with stalmarck; intros H'; inversion H'.
rewrite samePolRzValRz; auto with stalmarck.
rewrite updateArraya; auto with stalmarck; intros H'2.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl2;
 unfold incl in |- *; intros incl2; apply incl2; auto with stalmarck; 
 clear incl2.
intros; apply samePolRzEqRz; auto with stalmarck.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto with stalmarck.
rewrite <- eqrb; auto with stalmarck.
rewrite samePolSamePolRz; auto with stalmarck.
apply in_map with (A := rZ) (B := rZ); auto with stalmarck.
generalize appendfIncl1; unfold incl in |- *; intros incl1; apply incl1;
 auto with datatypes stalmarck; clear incl1.
apply DisjbLb with (2 := getb); auto with stalmarck.
injection H'2; trivial.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto with stalmarck.
case (InEqInv (rZPlus r) Lb); auto with stalmarck; intros InRLb'.
replace r with (valRz (rZPlus r)); auto with stalmarck.
rewrite updateArrayInb; auto with stalmarck; intros H'2; inversion H'2.
simpl in |- *; rewrite samePolRzValRz.
rewrite updateArraya; auto with stalmarck.
intros H'.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl2;
 unfold incl in |- *; intros incl2; apply incl2; auto with stalmarck; 
 clear incl2.
intros a0; apply samePolRzEqRz; auto with stalmarck.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto with stalmarck.
apply rltDef2; auto with stalmarck.
rewrite samePolSamePolRz; auto with stalmarck.
apply in_map with (A := rZ) (B := rZ); auto with stalmarck.
generalize appendfIncl2; unfold incl in |- *; intros incl1; apply incl1;
 auto with datatypes stalmarck; clear incl1.
apply DisjbLb with (2 := getb); auto with stalmarck.
injection H'; trivial.
replace r with (valRz (rZMinus r)); auto with stalmarck.
rewrite updateArrayInb; auto with stalmarck; intros H'2; inversion H'2.
simpl in |- *; rewrite valRzComp; rewrite samePolRzValRz.
rewrite updateArraya; auto with stalmarck.
intros H'.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl2;
 unfold incl in |- *; intros incl2; apply incl2; auto with stalmarck; 
 clear incl2.
intros a0; apply samePolRzEqRz; auto with stalmarck.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto with stalmarck.
apply rltDef2; auto with stalmarck.
replace (samePol (rZComp (samePolRz pol (rZPlus a))) r) with
 (samePolRz pol (rZMinus r)).
apply in_map with (A := rZ) (B := rZ); auto with stalmarck.
generalize appendfIncl2; unfold incl in |- *; intros incl1; apply incl1;
 auto with datatypes stalmarck; clear incl1.
apply DisjbLb with (2 := getb); auto with stalmarck.
case pol; auto with stalmarck.
injection H'; trivial.
rewrite updateArrayOtherwise; auto with stalmarck; intros Eqr.
case (rNatDec (valRz s) a); intros Eqt.
rewrite Eqt; auto with stalmarck; rewrite updateArraya; auto with stalmarck; intros H'.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl1;
 unfold incl in |- *; intros incl2; apply incl2; auto with stalmarck; 
 clear incl2.
intros a0; apply samePolRzEqRz; auto with stalmarck.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto with stalmarck.
apply rltDef2; auto with stalmarck.
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite Eqt; auto with stalmarck.
injection H'; trivial.
intros Eqs.
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
apply updateGetIsClass with (1 := Eqs); auto with stalmarck.
Qed.

Theorem updateArrayPointToClassClass : pointToClassClass updateArray.
apply pointToClassClassRef; auto with stalmarck.
exact updatePointToClassClassRef1.
exact updatePointToClassClassRef2.
Qed.
(* Finally !!! *)

Theorem updateWellFormed : wellFormedArray updateArray.
apply wellFormedArrayDef; auto with stalmarck.
apply updateArrayPointerDecrease; auto with stalmarck.
apply updateArrayPointToRef; auto with stalmarck.
apply updateArrayPointToClassClass; auto with stalmarck.
apply updateArrayOlist; auto with stalmarck.
Qed.
End AaddD.
