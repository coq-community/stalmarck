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
                                                                           
          Stalmarck  :   addArray                                          
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Addition of an equation to a well-formed array*)
Require Export wfArray.
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
intros Ar a mL; generalize Ar; Elimc mL; clear Ar; simpl in |- *; auto.
intros a0 l H' Ar m H'0.
rewrite rArrayDef2; auto.
apply H'; auto.
Contradict H'0; auto.
red in |- *; apply InEqSkip; auto.
Contradict H'0; auto.
red in |- *; apply InEqHead; auto; red in |- *; auto.
Qed.

Theorem rArraySetListInv2 :
 forall (Ar : rArray vM) (a : rZ) (mL : list rZ) (m : rZ),
 OlistRz mL ->
 In m mL ->
 rArrayGet _ (rArraySetList Ar a mL) (valRz m) = ref (samePolRz m a).
intros Ar a mL; generalize Ar; elim mL; simpl in |- *; auto.
intros Ar0 m H' H'0; elim H'0; auto.
intros a0 l H' Ar0 m H'0 H'1; Elimc H'1; intros H'1;
 [ rewrite <- H'1 | idtac ]; auto.
apply rArrayDef1; auto.
rewrite rArrayDef2; auto.
apply H'; auto.
red in |- *; apply OlistInv with (a := a0); auto.
red in |- *; intros H'2; absurd (InEq _ eqRz m l); auto.
apply OlistUniqueEq with (ltA := rZlt) (a := a0); auto.
exact rZltEqComp.
apply inImpInEq; auto.
Qed.
(* a minimal element does not belong to its pointer list *)

Theorem DisjbLb :
 forall (b : rNat) (Lb : list rZ) (Ar : rArray vM) 
   (War : wellFormedArray Ar) (getb : rArrayGet _ Ar b = class Lb),
 DisjointRz (rZPlus b :: nil) Lb.
intros b Lb Ar War getb; red in |- *; simpl in |- *.
apply DisjointDef; simpl in |- *; auto.
intros a H'; inversion_clear H'.
apply NotInEqComp with (a := rZPlus b); auto.
apply wellFormedArrayInImpNotEqSimpl with (1 := War); auto.
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
 [ intros DLaLb | apply wfDisjoint with (3 := geta) (4 := getb); auto ].
red in |- *; auto.
apply DisjointCom; unfold appendRz in |- *; apply appendfDisjoint; auto.
apply DisjbLb with (2 := getb); auto.
apply DisjointDef; simpl in |- *; auto.
intros a0 H'; inversion_clear H'.
apply NotInEqComp with (a := rZPlus b); auto.
apply wellFormedArrayInImpNotEq with (2 := getb) (3 := geta); auto.
inversion_clear H.
apply DisjointCom; auto.
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
rewrite rArrayDef1; auto.
Qed.
(* b is now a pointer *)

Theorem updateArrayb :
 rArrayGet _ updateArray b = ref (samePolRz pol (rZPlus a)).
unfold updateArray in |- *.
cut (a <> b); [ intros Neqab | apply rltDef2; auto ].
rewrite rArrayDef2; auto.
pattern b at 2 in |- *; replace b with (valRz (rZPlus b)); auto.
rewrite rArraySetListInv2; auto.
red in |- *; unfold appendRz in |- *; apply appendfOlist; auto.
exact rZltEqComp.
apply OlistOne; auto.
apply wfOl with (2 := getb); auto.
generalize appendfIncl1; unfold incl in |- *; auto with datatypes.
intros H'; unfold appendRz in |- *; apply H'; auto with datatypes.
apply DisjbLb with (2 := getb); auto.
Qed.
(* The ones that were pointing to b now point to a *)

Theorem updateArrayInb :
 forall c : rZ,
 In c Lb ->
 rArrayGet _ updateArray (valRz c) =
 ref (samePolRz c (samePolRz pol (rZPlus a))).
intros c InLb; unfold updateArray in |- *.
rewrite rArrayDef2; auto.
rewrite rArraySetListInv2; auto.
red in |- *; unfold appendRz in |- *; apply appendfOlist; auto.
exact rZltEqComp.
apply OlistOne; auto.
apply wfOl with (2 := getb); auto.
generalize appendfIncl2; unfold incl in |- *; auto with datatypes.
unfold appendRz in |- *; intros H'; apply H'; auto.
apply DisjbLb with (2 := getb); auto.
red in |- *; intros H'; absurd (InRz (rZPlus a) Lb); auto.
apply wellFormedArrayInImpNotEq with (2 := geta) (3 := getb); auto.
rewrite H'; auto.
red in |- *; apply InEqComp with (a := c); auto.
apply inImpInEq; auto.
Qed.
(* otherwise nothing has changed *)

Theorem updateArrayOtherwise :
 forall c : rNat,
 ~ InRz (rZPlus c) Lb ->
 c <> a -> c <> b -> rArrayGet _ updateArray c = rArrayGet _ Ar c.
intros c NotPInb NotEqca NotEqcb.
unfold updateArray in |- *.
replace c with (valRz (rZPlus c)); auto.
rewrite rArrayDef2; auto.
rewrite rArraySetListInv1; auto.
red in |- *; intros H'.
unfold appendRz in H'.
case appendfInvEq with (1 := H'); auto; intros H'0; inversion_clear H'0;
 inversion H; auto.
Qed.
(* Now we want to show that the resulting array is well formed *)

Definition updateArrayPointerDecrease : pointerDecrease updateArray.
apply pointerDecreaseDef; auto.
intros r s H'.
case (rNatDec r a); intros eqra.
generalize H'; rewrite eqra; rewrite updateArraya; auto; clear H'; intros H';
 discriminate.
case (rNatDec r b); intros eqrb.
generalize H'; rewrite eqrb; auto; rewrite updateArrayb; auto; clear H';
 intros H'; inversion H'.
unfold rZlt in |- *; simpl in |- *; red in |- *.
rewrite samePolRzValRz; simpl in |- *; auto.
case (InRzDec (rZPlus r) Lb); intros inPb.
case (InEqInv (rZPlus r) Lb); auto; intros inPb'.
generalize H'; replace r with (valRz (rZPlus r)); auto;
 rewrite updateArrayInb; auto; clear H'; intros H'; 
 inversion H'.
simpl in |- *; red in |- *; rewrite samePolRzValRz; auto.
apply rltTrans with (y := b); auto.
change (rlt b (valRz (rZPlus r))) in |- *.
apply wellFormedArrayInImpLt with (Ar := Ar) (La := Lb); auto.
generalize H'; replace r with (valRz (rZMinus r)); auto;
 rewrite updateArrayInb; auto; clear H'; intros H'; 
 inversion H'.
simpl in |- *; apply rVltrZComp; auto.
red in |- *; rewrite samePolRzValRz; simpl in |- *; auto.
apply rltTrans with (y := b); auto.
change (rlt b (valRz (rZMinus r))) in |- *.
apply wellFormedArrayInImpLt with (Ar := Ar) (La := Lb); auto.
apply wfPd with (Ar := Ar); auto.
rewrite <- H'.
apply sym_equal.
apply updateArrayOtherwise; auto.
Qed.
(* if we are a minimal element different of a, nothing has changed *)

Theorem updateGetIsClass :
 forall (r : rNat) (Lr : list rZ),
 rArrayGet _ updateArray r = class Lr ->
 r <> a -> rArrayGet _ Ar r = class Lr.
intros r Lr H' H'0.
case (rNatDec r b); intros Eqb; auto.
generalize H'; rewrite Eqb; auto; rewrite updateArrayb; clear H'; intros H';
 discriminate.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto.
case (InEqInv (rZPlus r) Lb); auto; intros InRLb'.
generalize H'; replace r with (valRz (rZPlus r)); auto;
 rewrite updateArrayInb; auto; clear H'; intros H'; 
 discriminate.
generalize H'; replace r with (valRz (rZMinus r)); auto;
 rewrite updateArrayInb; auto; clear H'; intros H'; 
 discriminate.
rewrite <- H'; apply sym_equal.
apply updateArrayOtherwise; auto.
Qed.
(* Classes are ordered *)

Definition updateArrayOlist : OlistArray updateArray.
apply OlistArrayDef; auto.
intros r Lr H'.
case (rNatDec r a); intros Eqt.
generalize H'; rewrite Eqt; auto; rewrite updateArraya; auto; clear H';
 intros H'.
replace Lr with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).


 inversion H'.
red in |- *; unfold fappendRz in |- *; apply fappendfOlist; auto.
intros; apply samePolRzEqRz; auto.
try exact rZltEqComp.
apply wfOl with (2 := geta); auto.
unfold appendRz in |- *; apply appendfOlist; auto.
exact rZltEqComp.
apply OlistOne; auto.
apply wfOl with (2 := getb); auto.
injection H'; trivial.
apply wfOl with (Ar := Ar) (r := r); auto.
apply updateGetIsClass with (1 := H'); auto.
Qed.
(* The ref and the class are properly related *)

Theorem updateArrayPointToRef : pointToClassRef updateArray.
apply pointToClassRefDef; auto.
intros r s t H'1.
case (rNatDec (valRz s) a); intros eqsa.
rewrite eqsa; auto; rewrite updateArraya; red in |- *; intros H'2;
 discriminate.
case (rNatDec r a); intros eqra.
generalize H'1; rewrite eqra; auto; rewrite updateArraya; auto; intros;
 discriminate.
case (rNatDec r b); intros eqrb; auto.
generalize H'1; rewrite eqrb; auto; rewrite updateArrayb; auto; clear H'1;
 intros H'1; case eqsa; inversion H'1.
apply samePolRzValRz; auto.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto.
case (InEqInv (rZPlus r) Lb); auto; intros InRLb'.
generalize H'1; replace r with (valRz (rZPlus r)); auto;
 rewrite updateArrayInb; auto; clear H'1; intros H'1; 
 case eqsa; inversion H'1; simpl in |- *; auto.
apply samePolRzValRz; auto.
generalize H'1; replace r with (valRz (rZMinus r)); auto;
 rewrite updateArrayInb; auto; clear H'1; intros H'1; 
 case eqsa; inversion H'1; simpl in |- *; auto.
simpl in |- *; rewrite valRzComp; rewrite samePolRzValRz; auto.
generalize H'1; auto; rewrite updateArrayOtherwise; auto; clear H'1;
 intros H'1.
case (rNatDec (valRz s) b); intros eqsb; auto.
case InRLb; red in |- *.
apply InEqComp with (a := samePol s r); auto.
apply inImpInEq; auto.
apply wfPcc2 with (Ar := Ar); auto.
rewrite eqsb; auto; rewrite updateArrayb; auto.
case s; simpl in |- *; auto.
case (InRzDec s Lb); intros InRLb'; auto.
case (InEqInv s Lb); auto; intros InRLb''.
absurd (rArrayGet _ Ar (valRz s) = ref (samePol s b)); auto.
inversion War.
inversion pR.
apply H0 with (r := r); auto.
inversion War.
inversion pC.
apply H0 with (Lr := Lb); auto.
absurd (rArrayGet _ Ar (valRz (rZComp s)) = ref (samePol (rZComp s) b)).
rewrite valRzComp; auto.
inversion War.
inversion pR.
apply H0 with (r := r); auto.
inversion War.
inversion pC.
apply H0 with (Lr := Lb); auto.
rewrite updateArrayOtherwise; auto.
inversion War.
inversion pR.
apply H0 with (r := r); auto.
red in |- *; intros H'2; case InRLb'; red in |- *.
apply InEqComp with (a := rZPlus (valRz s)); auto.
Qed.

Theorem updatePointToClassClassRef1 :
 forall (r : rNat) (s : rZ) (Lr : list rZ),
 rArrayGet _ updateArray r = class Lr ->
 In s Lr -> rArrayGet _ updateArray (valRz s) = ref (samePol s r).
intros r s Lr.
case (rNatDec r a); intros eqra.
rewrite eqra; auto; rewrite updateArraya; auto; intros H'; inversion H'.
unfold fappendRz in |- *; unfold appendRz in |- *; intros Eqt.
case (fappendfInv rZ) with (6 := Eqt); try exact rZltEqComp; auto.
intro; apply samePolRzEqRz; auto.
intro Eqt'; rewrite updateArrayOtherwise; auto.
apply wfPcc1 with (Lr := La); auto.
red in |- *; intros H'2; absurd (a = b); auto.
red in |- *; intros H'3; absurd (rlt a b); auto.
rewrite <- H'3; auto.
apply
 wellFormedArrayInRzBothImpEq
  with (2 := geta) (3 := getb) (c := rZPlus (valRz s)); 
 auto.
red in |- *.
unfold InRz in |- *.
unfold InRz in |- *; intros; apply InEqComp with (a := s); auto.
apply inImpInEq; auto.
red in |- *; intros H'2; absurd (InRz (rZPlus a) La).
apply wellFormedArrayInImpNotEqSimpl with (2 := geta); auto.
rewrite <- H'2.
unfold InRz in |- *; simpl in |- *; intros; apply InEqComp with (a := s);
 auto.
apply inImpInEq; auto.
red in |- *; intros H'2; absurd (InRz (rZPlus b) La); auto.
apply wellFormedArrayInImpNotEq with (2 := getb) (3 := geta); auto.
rewrite <- H'2.
unfold InRz in |- *; simpl in |- *; intros; apply InEqComp with (a := s);
 auto.
apply inImpInEq; auto.
intro Eqt';
 elim
  (appendfInv rZ rZlt eqRz rZltEDec (rZPlus b :: nil) Lb (samePolRz pol s));
 auto.
simpl in |- *; intros Int.
Elimc Int; intros Int; [ idtac | Elimc Int; clear Int ]; auto.
replace (valRz s) with b.
rewrite updateArrayb; auto.
generalize Int; case s; case pol; simpl in |- *; auto; intros; discriminate.
rewrite <- (samePolRzValRz pol b); rewrite Int; case pol; case s;
 simpl in |- *; auto.
intros Int; replace (valRz s) with (valRz (samePolRz pol s)); auto.
rewrite updateArrayInb; auto.
case pol; case s; simpl in |- *; auto.
case pol; case s; simpl in |- *; auto.
rewrite <-
 (map_id rZ (samePolRz pol) (samePolRzsamePolRz pol)
    (appendf rZ rZlt eqRz rZltEDec (rZPlus b :: nil) Lb))
 ; auto.
apply in_map; auto.
case (rNatDec r b); intros eqrb.
rewrite eqrb; auto; rewrite updateArrayb; auto; intros H'; discriminate.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto.
case (InEqInv (rZPlus r) Lb); auto; intros InRLb'.
replace r with (valRz (rZPlus r)); auto; rewrite updateArrayInb; auto;
 intros H'; discriminate.
replace r with (valRz (rZMinus r)); auto; rewrite updateArrayInb; auto;
 intros H'; discriminate.
case (rNatDec (valRz s) a); intros eqsa.
intros H' H'0.
absurd (InRz (rZPlus a) Lr); auto.
apply wellFormedArrayInImpNotEq with (Ar := Ar) (b := r) (La := La); auto.
apply updateGetIsClass with (1 := H'); auto.
red in |- *; apply InEqComp with (a := s); auto.
apply inImpInEq; auto.
case (rNatDec (valRz s) b); intros eqsb.
intros H' H'0.
absurd (InRz (rZPlus b) Lr); auto.
apply wellFormedArrayInImpNotEq with (Ar := Ar) (b := r) (La := Lb); auto.
apply updateGetIsClass with (1 := H'); auto.
red in |- *; apply InEqComp with (a := s); auto.
apply inImpInEq; auto.
rewrite updateArrayOtherwise; auto.
intros H' H'0; rewrite updateArrayOtherwise; auto.
apply wfPcc1 with (Lr := Lr); auto.
red in |- *; intros H'2; absurd (r = b); auto.
apply
 wellFormedArrayInRzBothImpEq with (Ar := Ar) (c := s) (La := Lr) (Lb := Lb);
 auto.
red in |- *; apply InEqComp with (a := s); auto.
apply inImpInEq; auto.
red in |- *; apply InEqComp with (a := rZPlus (valRz s)); auto.
Qed.

Theorem updatePointToClassClassRef2 :
 forall (r : rNat) (s : rZ) (Ls : list rZ),
 rArrayGet _ updateArray r = ref s ->
 rArrayGet _ updateArray (valRz s) = class Ls -> In (samePol s r) Ls.
intros r s Ls.
case (rNatDec r a); intros eqra.
rewrite eqra; auto; rewrite updateArraya; auto; intros H'; inversion H'.
case (rNatDec r b); intros eqrb.
rewrite eqrb; auto; rewrite updateArrayb; auto; intros H'; inversion H'.
rewrite samePolRzValRz; auto.
rewrite updateArraya; auto; intros H'2.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl2;
 unfold incl in |- *; intros incl2; apply incl2; auto; 
 clear incl2.
intros; apply samePolRzEqRz; auto.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto.
rewrite <- eqrb; auto.
rewrite samePolSamePolRz; auto.
apply in_map with (A := rZ) (B := rZ); auto.
generalize appendfIncl1; unfold incl in |- *; intros incl1; apply incl1;
 auto with datatypes; clear incl1.
apply DisjbLb with (2 := getb); auto.
injection H'2; trivial.
case (InRzDec (rZPlus r) Lb); intros InRLb; auto.
case (InEqInv (rZPlus r) Lb); auto; intros InRLb'.
replace r with (valRz (rZPlus r)); auto.
rewrite updateArrayInb; auto; intros H'2; inversion H'2.
simpl in |- *; rewrite samePolRzValRz.
rewrite updateArraya; auto.
intros H'.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl2;
 unfold incl in |- *; intros incl2; apply incl2; auto; 
 clear incl2.
intros a0; apply samePolRzEqRz; auto.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto.
apply rltDef2; auto.
rewrite samePolSamePolRz; auto.
apply in_map with (A := rZ) (B := rZ); auto.
generalize appendfIncl2; unfold incl in |- *; intros incl1; apply incl1;
 auto with datatypes; clear incl1.
apply DisjbLb with (2 := getb); auto.
injection H'; trivial.
replace r with (valRz (rZMinus r)); auto.
rewrite updateArrayInb; auto; intros H'2; inversion H'2.
simpl in |- *; rewrite valRzComp; rewrite samePolRzValRz.
rewrite updateArraya; auto.
intros H'.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl2;
 unfold incl in |- *; intros incl2; apply incl2; auto; 
 clear incl2.
intros a0; apply samePolRzEqRz; auto.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto.
apply rltDef2; auto.
replace (samePol (rZComp (samePolRz pol (rZPlus a))) r) with
 (samePolRz pol (rZMinus r)).
apply in_map with (A := rZ) (B := rZ); auto.
generalize appendfIncl2; unfold incl in |- *; intros incl1; apply incl1;
 auto with datatypes; clear incl1.
apply DisjbLb with (2 := getb); auto.
case pol; auto.
injection H'; trivial.
rewrite updateArrayOtherwise; auto; intros Eqr.
case (rNatDec (valRz s) a); intros Eqt.
rewrite Eqt; auto; rewrite updateArraya; auto; intros H'.
replace Ls with (fappendRz La (appendRz (rZPlus b :: nil) Lb)).
unfold fappendRz in |- *; unfold appendRz in |- *; generalize fappendfIncl1;
 unfold incl in |- *; intros incl2; apply incl2; auto; 
 clear incl2.
intros a0; apply samePolRzEqRz; auto.
try exact rZltEqComp.
apply DisjLaLc with (3 := geta) (4 := getb); auto.
apply rltDef2; auto.
apply wfPcc2 with (Ar := Ar); auto.
rewrite Eqt; auto.
injection H'; trivial.
intros Eqs.
apply wfPcc2 with (Ar := Ar); auto.
apply updateGetIsClass with (1 := Eqs); auto.
Qed.

Theorem updateArrayPointToClassClass : pointToClassClass updateArray.
apply pointToClassClassRef; auto.
exact updatePointToClassClassRef1.
exact updatePointToClassClassRef2.
Qed.
(* Finally !!! *)

Theorem updateWellFormed : wellFormedArray updateArray.
apply wellFormedArrayDef; auto.
apply updateArrayPointerDecrease; auto.
apply updateArrayPointToRef; auto.
apply updateArrayPointToClassClass; auto.
apply updateArrayOlist; auto.
Qed.
End AaddD.