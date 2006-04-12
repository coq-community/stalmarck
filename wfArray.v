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
                                                                           
          Stalmarck  :  wfArray                                                     
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Define a notion of wellformedness of function arrays for our application*)
Require Export rZ.
Require Export OrderedListEq.
Require Export Relation_Definitions.
Require Export LetP.
Require Export PolyListAux.
Require Export List.
Require Export Option.
Require Export sTactic.

(*Definition of well formed array and some properties *)
Section wfArray.

(* Ordered list for list on  rZ *)

Definition OlistRz := Olist rZ rZlt.

(* Disjoint list for list on rZ *)

Definition DisjointRz := Disjoint rZ eqRz.

(* To be in a list for rZ with no sign consideration  *)

Definition InRz := InEq rZ eqRz.

Theorem InEqInv :
 forall (a : rZ) (L : list rZ), InRz a L -> In a L \/ In (rZComp a) L.
intros a L H'; Elimc H'; clear a L; auto.
intros a b L; case a; case b; unfold eqRz in |- *; simpl in |- *;
 intros a' b' Eqt; rewrite Eqt; auto.
intros a b L H' H'0; elim H'0; auto with datatypes.
Qed.

Theorem InRzDec : forall (a : rZ) (L : list rZ), {InRz a L} + {~ InRz a L}.
intros a L; elim L; auto.
right; red in |- *; intros H'; inversion H'.
intros a0 l H'; case H'.
intros H'0; left; auto.
red in |- *; apply InEqSkip; auto.
intros H'0; case (rNatDec (valRz a) (valRz a0)); intros H'1.
left; auto.
red in |- *; apply InEqHead; auto.
right; red in |- *; intros H'2; inversion_clear H'2.
case H'1; auto.
case H'0; auto.
Qed.
(* A vM is either a reference or an equivalence class *)

Inductive vM : Set :=
  | ref : rZ -> vM
  | class : list rZ -> vM.
(*We can decide on list *)

Definition listDec :
  forall (A : Set) (eqDec : forall a b : A, {a = b} + {a <> b})
    (L1 L2 : list A), {L1 = L2} + {L1 <> L2}.
intros A eqDec.
fix 1.
intros L1; case L1.
intros L2; case L2.
left; auto.
intros a l; right; red in |- *; intros H'; discriminate.
intros a l L2; case L2.
right; red in |- *; intros H'; discriminate.
intros a0 l0; case (eqDec a a0); intros Eq0.
case (listDec l l0); intros Eq1.
left; rewrite Eq0; rewrite Eq1; auto.
right; Contradict Eq1; inversion Eq1; auto.
right; Contradict Eq0; inversion Eq0; auto.
Defined.
(* We can decide equality on vM *)

Definition vMDec : forall a b : vM, {a = b} + {a <> b}.
intros a b; case a; case b;
 try (intros; right; red in |- *; intros; discriminate; fail).
intros r r0; case (rZDec r r0); intros Eq1.
rewrite <- Eq1; auto.
right; red in |- *; intros H'; case Eq1; inversion H'; auto.
intros l l0; case (listDec _ rZDec l0 l); intros Eq1.
rewrite <- Eq1; auto.
right; red in |- *; intros H'; case Eq1; inversion H'; auto.
Defined.

Let get := rArrayGet vM.

Let set := rArraySet vM.
(*We point always to something smaller *)

Inductive pointerDecrease : rArray vM -> Prop :=
    pointerDecreaseDef :
      forall Ar : rArray vM,
      (forall (r : rNat) (s : rZ), get Ar r = ref s -> rVlt s r) ->
      pointerDecrease Ar.
(* Value of pointers are not pointers *)

Inductive pointToClassRef : rArray vM -> Prop :=
    pointToClassRefDef :
      forall Ar : rArray vM,
      (forall (r : rNat) (s t : rZ),
       get Ar r = ref s -> get Ar (valRz s) <> ref t) -> 
      pointToClassRef Ar.
(* all the elements of an equivalence classe points to the class,
    and if one element points to an equivalent class it is in the equivalence class *)

Inductive pointToClassClass : rArray vM -> Prop :=
    pointToClassClassRef :
      forall Ar : rArray vM,
      (forall (r : rNat) (s : rZ) (Lr : list rZ),
       get Ar r = class Lr -> In s Lr -> get Ar (valRz s) = ref (samePol s r)) ->
      (forall (r : rNat) (s : rZ) (Ls : list rZ),
       get Ar r = ref s -> get Ar (valRz s) = class Ls -> In (samePol s r) Ls) ->
      pointToClassClass Ar.
(*Equivalent classes are ordered list *)

Inductive OlistArray : rArray vM -> Prop :=
    OlistArrayDef :
      forall Ar : rArray vM,
      (forall (r : rNat) (Lr : list rZ), get Ar r = class Lr -> OlistRz Lr) ->
      OlistArray Ar.
(* A  well formed array has all the previous properties.
 The idea is that we want every non minimal elements to point by  Ref to its minimal element
 and the minimal elment to contain by Class the elements pointing to it
 Example: if we have to represent [2=-3;1=3] we have
           f(1)= Class [-2;3] 
           f(2) = Ref -1
           f(3) = Ref 1 
*)

Inductive wellFormedArray : rArray vM -> Prop :=
    wellFormedArrayDef :
      forall (Ar : rArray vM) (pD : pointerDecrease Ar)
        (pR : pointToClassRef Ar) (pC : pointToClassClass Ar)
        (oC : OlistArray Ar), wellFormedArray Ar.
(* Well formedness is compatible with equality *)

Theorem WarCompEq :
 forall Ar1 Ar2 : rArray vM,
 (forall a : rNat, get Ar1 a = get Ar2 a) ->
 wellFormedArray Ar1 -> wellFormedArray Ar2.
intros Ar1 Ar2 H' War1; inversion War1.
apply wellFormedArrayDef; auto.
apply pointerDecreaseDef; auto.
intros r s; rewrite <- H'; inversion pD; auto.
apply pointToClassRefDef; auto.
intros r s t; repeat rewrite <- H'; auto.
intros H'0; inversion pR; auto.
apply H0 with (r := r); auto.
apply pointToClassClassRef; auto.
intros r s Lr; repeat rewrite <- H'; auto.
intros H'0 H'1; inversion pC; auto.
apply H0 with (Lr := Lr); auto.
intros r s Ls; repeat rewrite <- H'; auto.
intros H'0 H'1; inversion pC; auto.
apply OlistArrayDef; auto.
intros r Lr; repeat rewrite <- H'; auto.
intros H'0; inversion oC; auto.
apply H0 with (r := r); auto.
Qed.
Variable Ar : rArray vM.
Hypothesis War : wellFormedArray Ar.
(*******************************************
  Inversion theorems for WellformedArray 
********************************************)

Theorem wfPd : forall (r : rNat) (t : rZ), get Ar r = ref t -> rVlt t r.
intros r t H'; inversion War.
inversion pD.
apply H0 with (1 := H'); auto.
Qed.

Theorem wfPcr :
 forall (r : rNat) (t u : rZ), get Ar r = ref t -> get Ar (valRz t) <> ref u.
intros r t u H'; inversion War.
inversion pR; apply H0 with (1 := H'); auto.
Qed.

Theorem wfPcc1 :
 forall (r : rNat) (s : rZ) (Lr : list rZ),
 get Ar r = class Lr -> In s Lr -> get Ar (valRz s) = ref (samePol s r).
intros r s Lr H' H'0; inversion War.
inversion pC; apply H0 with (1 := H'); auto.
Qed.

Theorem wfPcc2 :
 forall (r : rNat) (s : rZ) (Ls : list rZ),
 get Ar r = ref s -> get Ar (valRz s) = class Ls -> In (samePol s r) Ls.
intros r s Ls H' H'0; inversion War.
inversion pC; apply H1 with (1 := H') (2 := H'0); auto.
Qed.

Theorem wfOl :
 forall (r : rNat) (Lr : list rZ), get Ar r = class Lr -> OlistRz Lr.
intros r Lr H'; inversion War.
inversion oC; apply H0 with (1 := H'); auto.
Qed.
(*** Equivalence classes are disjoint *)

Theorem refSameEq :
 forall (a b : rZ) (r s : rNat),
 ref (samePol a s) = ref (samePol b r) -> s = r.
intros a b r s; case a; case b; simpl in |- *; intros a1 b1 C1; inversion C1;
 auto.
Qed.

Theorem wfDisjoint :
 forall (r s : rNat) (Lr Ls : list rZ),
 s <> r -> get Ar r = class Lr -> get Ar s = class Ls -> DisjointRz Lr Ls.
intros r s Lr Ls H' H'0 H'1; red in |- *; apply DisjointDef.
intros a H'2; red in |- *; intros H'3; case H'.
case (InEqInv _ _ H'2); intros In1; generalize (wfPcc1 _ _ _ H'0 In1);
 intros get1; case (InEqInv _ _ H'3); intros In2;
 generalize (wfPcc1 _ _ _ H'1 In2); intros get2.
apply refSameEq with (a := a) (b := a); rewrite <- get1; rewrite <- get2;
 auto.
apply refSameEq with (a := rZComp a) (b := a); rewrite <- get1;
 rewrite <- get2; auto.
case a; simpl in |- *; auto.
apply refSameEq with (a := a) (b := rZComp a); rewrite <- get1;
 rewrite <- get2; auto.
case a; simpl in |- *; auto.
apply refSameEq with (a := rZComp a) (b := rZComp a); rewrite <- get1;
 rewrite <- get2; auto.
Qed.
(*There is no loop in the pointers *)

Theorem getNotIdP : forall r : rZ, get Ar (valRz r) <> ref r.
intros r; red in |- *; intros H'.
absurd (rVlt r (valRz r)); auto.
unfold rVlt in |- *; auto.
apply wfPd; auto.
Qed.
(* The element that contains an equivalence classis smaller than all the element 
 of the class *)

Theorem wellFormedArrayInImpLt :
 forall (a : rNat) (b : rZ) (La : list rZ),
 get Ar a = class La -> In b La -> rlt a (valRz b).
intros a b La geta Inb.
replace a with (valRz (samePol b a)).
generalize (wfPd _ _ (wfPcc1 _ _ _ geta Inb)); unfold rVlt in |- *; auto.
case b; case a; simpl in |- *; auto.
Qed.
(* An element that contains an equivalence class can't be in a equivalence class *)

Theorem wellFormedArrayInImpNotEq :
 forall (a b : rNat) (La Lb : list rZ),
 get Ar a = class La -> get Ar b = class Lb -> ~ InRz (rZPlus a) Lb.
intros a b La Lb geta getb; red in |- *; intros H'3.
case (InEqInv (rZPlus a) Lb H'3); intros H'4; auto.
absurd (get Ar (valRz (rZPlus a)) = class La); auto.
rewrite wfPcc1 with (1 := getb); auto.
red in |- *; intro; discriminate.
absurd (get Ar (valRz (rZMinus a)) = class La); auto.
rewrite wfPcc1 with (1 := getb); auto.
red in |- *; intro; discriminate.
Qed.
(*If two elements contains two equivalent classes that are not disjoint these
  elements are equal *)

Theorem wellFormedArrayInBothImpEq :
 forall (a b : rNat) (c d : rZ) (La Lb : list rZ),
 get Ar a = class La ->
 get Ar b = class Lb -> In c La -> In d Lb -> eqRz c d -> a = b.
intros a b c d La Lb geta getb inc1 inc2 eqRz1.
apply refSameEq with (a := c) (b := d).
rewrite <- wfPcc1 with (1 := geta); auto.
rewrite <- wfPcc1 with (1 := getb); auto.
rewrite eqRz1; auto.
Qed.
(* Same as before but with no sign distinction *)

Theorem wellFormedArrayInRzBothImpEq :
 forall (a b : rNat) (c : rZ) (La Lb : list rZ),
 get Ar a = class La ->
 get Ar b = class Lb -> InRz c La -> InRz c Lb -> a = b.
intros a b c La Lb H'0 H'1 H'2 H'3.
case (InEqInv c La H'2); case (InEqInv c Lb H'3); intros H'4 H'5;
 apply
  wellFormedArrayInBothImpEq with (1 := H'0) (2 := H'1) (3 := H'5) (4 := H'4);
 auto.
Qed.
(* An element that contains an equivalence class is  not in the class *)

Theorem wellFormedArrayInImpNotEqSimpl :
 forall (a : rNat) (La : list rZ),
 get Ar a = class La -> ~ InRz (rZPlus a) La.
intros a La H'.
apply wellFormedArrayInImpNotEq with (1 := H') (2 := H'); auto.
Qed.
(*If an element is not in an euqivalent class its value can't be the element
    that contains the equialent class *)

Theorem wellFormedArrayNInImpNotRef :
 forall (a : rNat) (b : rZ) (L : list rZ),
 get Ar a = class L -> ~ In b L -> get Ar (valRz b) <> ref (samePol b a).
intros a b L H' H'0; Contradict H'0.
cut (b = samePol (samePol b a) (valRz b)).
intros H'1; rewrite H'1.
apply (wfPcc2 (valRz b) (samePol b a) L); auto.
rewrite <- H'; unfold get in |- *; auto.
case b; simpl in |- *; auto.
case b; simpl in |- *; auto.
Qed.
End wfArray.