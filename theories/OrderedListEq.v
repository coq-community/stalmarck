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
                                                                           
          Stalmarck  : OrderedListEq                                       
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 A generic module to define concatenation on ordered list,
   we took a special care so that every function can be evaluated
   inside Coq, see OrderedListEq_ex.v  *)
Require Import Arith.
Require Export List.
Require Import Lexicographic_Exponentiation.
Require Export Relation_Definitions.
Require Export Relation_Operators.
Require Export sTactic.
Section OrderedList.

(* All the operation are done over an arbitrary set A with explicit equality, < etc *)
Variable A : Set.
Variable ltA : A -> A -> Prop.
Variable eqA : A -> A -> Prop.
Hypothesis eqARefl : reflexive A eqA.
Hypothesis eqASym : symmetric A eqA.
Hypothesis eqATrans : transitive A eqA.
Hypothesis ltADec : forall a b : A, {ltA a b} + {ltA b a} + {eqA a b}.
Hypothesis ltATrans : transitive A ltA.
Hypothesis ltAAnti : forall a : A, ~ ltA a a.
Hypothesis ltAImpNotEqA : forall a b : A, ltA a b -> ~ eqA a b.
Hypothesis ltAntiSym : forall a b : A, ltA a b -> ~ ltA b a.
Variable f : A -> A.
Hypothesis feqA : forall a : A, eqA (f a) a.
Hypothesis
  ltAeqAComp : forall a b c d : A, ltA a b -> eqA a c -> eqA b d -> ltA c d.

Definition eqADec : forall a b : A, {eqA a b} + {~ eqA a b}.
intros a b; case (ltADec a b); intros Test; auto.
Casec Test; intros Test; auto.
right.
red in |- *; intros H'; absurd (eqA b a); auto.
Qed.
Hypothesis eqADec' : forall a b : A, {eqA a b} + {~ eqA a b}.
(* What is to be ordered for a list *)

Inductive Olist : list A -> Prop :=
  | OlistNil : Olist nil
  | OlistOne : forall a : A, Olist (a :: nil)
  | OlistCons :
      forall (a b : A) (L : list A),
      Olist (b :: L) -> ltA a b -> Olist (a :: b :: L).
Local Hint Resolve OlistNil OlistOne OlistCons : core.
(* Inversion lemma *)

Theorem OlistInv : forall (a : A) (L : list A), Olist (a :: L) -> Olist L.
intros a L H'; inversion H'; auto.
Qed.
(* Useful  short cut taking advantage of the transitivity of < *)

Theorem OlistSkip :
 forall (a b : A) (L : list A), Olist (a :: b :: L) -> Olist (a :: L).
intros a b L; case L.
intros H'.
apply OlistOne; auto.
intros a0 l; case l.
intros H'.
apply OlistCons; auto.
apply ltATrans with (y := b); auto.
inversion H'; auto.
inversion H'; auto.
inversion H1; auto.
intros a1 l0 H'; inversion H'; inversion H1.
apply OlistCons; auto.
apply ltATrans with (y := b); auto.
Qed.
(* The first element is the smallest *)

Theorem OlistSup :
 forall (a : A) (L : list A),
 Olist (a :: L) -> forall b : A, In b L -> ltA a b.
intros a L; elim L; simpl in |- *; auto.
intros H' b H'0; elim H'0.
intros a0 l H' H'0 b H'1; Elimc H'1; intros H'1; [ rewrite <- H'1 | idtac ];
 auto.
inversion H'0; auto.
apply H'; auto.
apply OlistSkip with (b := a0); auto.
Qed.
(* Something equal to the head can't be in the tail *)

Theorem OlistUnique :
 forall (L : list A) (a b : A), Olist (a :: L) -> eqA a b -> ~ In b L.
intros L a b H' H'0; red in |- *; intros H'1; absurd (eqA a b); auto.
apply ltAImpNotEqA; auto.
apply OlistSup with (L := L); auto.
Qed.
(* Two elements equals in an ordered list are structuraly equal *)

Theorem OlistIn :
 forall (L : list A) (a b : A),
 In a L -> In b L -> Olist L -> eqA a b -> a = b.
intros L; elim L; simpl in |- *; auto.
intros a b H'; elim H'; auto.
intros a l H' a0 b H'0; Elimc H'0; intros H'0; [ rewrite <- H'0 | idtac ].
intros H'1; Casec H'1; intros H'1; auto.
intros H'2 H'3; absurd (eqA a b); auto.
apply ltAImpNotEqA; auto.
apply OlistSup with (L := l); auto.
intros H'1; Elimc H'1; intros H'1; [ rewrite <- H'1 | idtac ]; intros H'2 H'3.
absurd (eqA a a0); auto.
apply ltAImpNotEqA; auto.
apply OlistSup with (L := l); auto.
apply H'; auto.
apply OlistInv with (a := a); auto.
Qed.
(* Belonging with respect to InEq *)

Inductive InEq : A -> list A -> Prop :=
  | InEqHead : forall (a b : A) (L : list A), eqA a b -> InEq a (b :: L)
  | InEqSkip : forall (a b : A) (L : list A), InEq a L -> InEq a (b :: L).
Local Hint Resolve InEqHead InEqSkip : core.
(* Is it decidable *)

Definition InEqDec :
  forall (a : A) (L1 : list A), {InEq a L1} + {~ InEq a L1}.
fix InEqDec 2.
intros a L1; case L1.
right; red in |- *; intros H'; inversion H'; auto.
intros a0 l; case (eqADec' a a0); intros Eqaa0.
left; auto.
case (InEqDec a l); intros REc.
left; auto.
right; red in |- *; intros H'0; inversion H'0; auto.
Defined.
(* Weakening lemma *)

Theorem inImpInEq : forall (a : A) (L : list A), In a L -> InEq a L.
intros a L; elim L; simpl in |- *; auto.
intros H'; elim H'.
intros a0 l H' H'0; Elimc H'0; intros H'0; [ rewrite <- H'0 | idtac ]; auto.
Qed.
(* Version of OlistSup for InEq *)

Theorem OlistSupEq :
 forall (a : A) (L : list A),
 Olist (a :: L) -> forall b : A, InEq b L -> ltA a b.
intros a L; elim L; simpl in |- *; auto.
intros H' b H'0; inversion H'0.
intros a0 l H' H'0 b H'1; inversion_clear H'1.
apply ltAeqAComp with (a := a) (b := a0); auto.
apply OlistSup with (L := a0 :: l); simpl in |- *; auto.
apply H'; auto.
apply OlistSkip with (b := a0); auto.
Qed.
(* Version of OlistUnique for InEq *)

Theorem OlistUniqueEq :
 forall (L : list A) (a b : A), Olist (a :: L) -> eqA a b -> ~ InEq b L.
intros L a b H' H'0; red in |- *; intros H'1; absurd (eqA a b); auto.
apply ltAImpNotEqA; auto.
apply OlistSupEq with (L := L); auto.
Qed.
(* It is comptable with equality *)

Theorem InEqComp :
 forall (a b : A) (L : list A), InEq a L -> eqA a b -> InEq b L.
intros a b L H'; generalize b; clear b; elim H'; auto.
intros a0 b L0 H'0 b0 H'1.
apply InEqHead; auto.
apply eqATrans with (y := a0); auto.
Qed.
(* and the converse *)

Theorem NotInEqComp :
 forall (a b : A) (L : list A), ~ InEq a L -> eqA a b -> ~ InEq b L.
intros a b L H' H'0; red in |- *; intros H'1; case H'; auto.
apply InEqComp with (a := b); auto.
Qed.
(* Inclusion with respect to eqA *)

Inductive InclEq : list A -> list A -> Prop :=
    InclEqDef :
      forall L1 L2 : list A,
      (forall a : A, InEq a L1 -> InEq a L2) -> InclEq L1 L2.
Local Hint Resolve InclEqDef : core.
(*  Weakening *)

Theorem inclImpImplEq : forall L1 L2 : list A, incl L1 L2 -> InclEq L1 L2.
intros L1 L2 H'; apply InclEqDef.
intros a H'0; generalize H'; elim H'0; auto.
intros a0 b L H'1 H'2.
apply InEqComp with (a := b); auto.
apply inImpInEq; auto with datatypes core.
intros a0 b L H'1 H'2 H'3.
apply H'2; auto.
apply incl_tran with (A := A) (m := b :: L); auto with datatypes core.
Qed.
(* The empty list is in every list *)

Theorem InclEqNil : forall L : list A, InclEq nil L.
intros L.
apply InclEqDef; auto.
intros a H'; inversion H'.
Qed.
Local Hint Resolve InclEqNil : core.
(* Reflexivity *)

Theorem InclEqRef : forall L : list A, InclEq L L.
intros L.
apply InclEqDef; auto.
Qed.
Local Hint Resolve InclEqRef : core.
(* Transitivity *)

Theorem InclEqTrans : transitive (list A) InclEq.
red in |- *.
intros x y z H' H'0; inversion_clear H'; inversion_clear H'0; auto.
Qed.
(* f Useful lemma *)

Theorem InclEqCons :
 forall (a : A) (L1 L2 : list A),
 InEq a L2 -> InclEq L1 L2 -> InclEq (a :: L1) L2.
intros a L1 L2 H' H'0; inversion H'0; auto.
apply InclEqDef; auto.
intros a0 H'1; inversion H'1; auto.
apply InEqComp with (a := a); auto.
Qed.
Local Hint Resolve InclEqCons : core.
(* Equality with respect to eqA *)

Inductive EqL : list A -> list A -> Prop :=
  | EqLNil : EqL nil nil
  | EqLCons :
      forall (a b : A) (L1 L2 : list A),
      eqA a b -> EqL L1 L2 -> EqL (a :: L1) (b :: L2).
Local Hint Resolve EqLNil EqLCons : core.
(* InEq is compatible with eqL *)

Theorem EqLInv :
 forall (L1 L2 : list A) (a : A), EqL L1 L2 -> InEq a L1 -> InEq a L2.
intros L1 L2 a H'; elim H'; auto.
intros a0 b L3 L4 H'0 H'1 H'2 H'3; inversion H'3; auto.
apply InEqHead; auto.
apply eqATrans with (y := a0); auto.
Qed.
(* Reflexivity *)

Theorem EqLRef : forall L : list A, EqL L L.
intros L; elim L; auto.
Qed.
Local Hint Resolve EqLRef : core.
(* Transitivity *)

Theorem EqLTrans : forall L : list A, transitive (list A) EqL.
intros L; red in |- *.
intros x y z H'; generalize z; Elimc H'; clear z; auto.
intros a b L1 L2 H' H'0 H'1 z H'2; inversion H'2; auto.
apply EqLCons; auto.
apply eqATrans with (y := b); auto.
Qed.
(* Useful inversion lemma *)

Theorem InclEqOlist :
 forall (L1 L2 : list A) (a b : A),
 Olist (a :: L1) ->
 Olist (b :: L2) -> InclEq (a :: L1) (b :: L2) -> InclEq L1 L2.
intros L1 L2 a b H' H'0 H'1.
apply InclEqDef; auto.
intros a0 H'2.
inversion H'1.
lapply (H a0); [ intros H'4; inversion H'4 | try assumption ]; auto.
cut (ltA a a0); auto.
2: apply OlistSupEq with (L := L1); auto.
intros H'3.
lapply (H a); [ intros H'6; inversion H'6 | idtac ]; auto.
absurd (eqA a b); auto.
apply ltAImpNotEqA; auto.
apply ltAeqAComp with (a := a) (b := a0); auto.
absurd (ltA b a); auto.
apply ltAntiSym; auto.
apply ltAeqAComp with (a := a) (b := a0); auto.
apply OlistSupEq with (L := L2); auto.
Qed.
(* As we have to take care of multiplicity, a sufficient condition is
    that lists are ordered *)

Theorem EqLOlist :
 forall L1 L2 : list A,
 Olist L1 -> Olist L2 -> InclEq L1 L2 -> InclEq L2 L1 -> EqL L1 L2.
intros L1; elim L1; auto.
intros L2; case L2; auto.
intros a l H' H'0 H'1 H'2; inversion H'2.
lapply (H a); [ intros H'4; inversion H'4 | idtac ]; auto.
intros a l H' L2; case L2; auto.
intros H'0 H'1 H'2; inversion H'2.
lapply (H a); [ intros H'4; inversion H'4 | idtac ]; auto.
intros a0 l0 H'0 H'1 H'2 H'3; auto.
apply EqLCons; auto.
2: apply H'; auto.
2: apply OlistInv with (a := a); auto.
2: apply OlistInv with (a := a0); auto.
2: apply InclEqOlist with (a := a) (b := a0); auto.
2: apply InclEqOlist with (a := a0) (b := a); auto.
inversion H'3.
lapply (H a0); [ intros H'5; inversion H'5 | idtac ]; auto.
inversion H'2; auto.
lapply (H6 a); [ intros H'6; inversion H'6 | idtac ]; auto.
absurd (ltA a0 a); auto.
apply ltAntiSym; auto.
apply OlistSupEq with (L := l); auto.
apply OlistSupEq with (L := l0); auto.
Qed.
(* Try to find an element in the first list that is not in the second *)

Fixpoint diffElem (L1 : list A) : list A -> option A :=
  fun L2 : list A =>
  match L1 with
  | nil => None
  | a :: L'1 =>
      match InEqDec a L2 with
      | left _ => diffElem L'1 L2
      | right _ => Some a
      end
  end.
(* If we can't find such element there is inclusion *)

Theorem diffElemNone :
 forall L1 L2 : list A, diffElem L1 L2 = None -> InclEq L1 L2.
intros L1; elim L1; simpl in |- *; auto.
intros a l H' L2.
case (InEqDec a L2); auto.
intros H'0 H'1; discriminate.
Qed.
(* If there is an element it belongs to the first *)

Theorem diffElemSomeIn :
 forall (L1 L2 : list A) (a : A), diffElem L1 L2 = Some a -> InEq a L1.
intros L1; elim L1; simpl in |- *; auto.
intros H' a H'0; discriminate.
intros a l H' L2 a0.
case (InEqDec a L2); intros InEq0 Eq0; auto.
apply InEqSkip; auto.
apply H' with (L2 := L2); auto.
inversion Eq0; auto.
Qed.
(* and does not belong to the other *)

Theorem diffElemSomeNIn :
 forall (L1 L2 : list A) (a : A), diffElem L1 L2 = Some a -> ~ InEq a L2.
intros L1; elim L1; simpl in |- *; auto.
intros H' a H'0; discriminate.
intros a l H' L2 a0.
case (InEqDec a L2); intros InEq0 Eq0; auto.
inversion Eq0; auto.
rewrite <- H0; auto.
Qed.
(* If the list are not the same we should find such an element *)

Definition olistDiff :
  forall L1 L2 : list A,
  Olist L1 ->
  Olist L2 ->
  ~ EqL L1 L2 ->
  {a : A | InEq a L1 /\ ~ InEq a L2 \/ ~ InEq a L1 /\ InEq a L2}.
intros L1 L2 H' H'0 H'1.
generalize (refl_equal (diffElem L1 L2));
 pattern (diffElem L1 L2) at -1 in |- *; case (diffElem L1 L2); 
 auto.
intros x H'2; exists x; left; split; auto.
apply diffElemSomeIn with (1 := H'2); auto.
apply diffElemSomeNIn with (1 := H'2); auto.
intros Eq1.
generalize (refl_equal (diffElem L2 L1));
 pattern (diffElem L2 L1) at -1 in |- *; case (diffElem L2 L1); 
 auto.
intros x H'2; exists x; right; split; auto.
apply diffElemSomeNIn with (1 := H'2); auto.
apply diffElemSomeIn with (1 := H'2); auto.
intros Eq2; absurd (EqL L1 L2); auto.
apply EqLOlist; auto.
apply diffElemNone; auto.
apply diffElemNone; auto.
Defined.
(* Two list are disjoint if there are no common element *)

Inductive Disjoint : list A -> list A -> Prop :=
    DisjointDef :
      forall L1 L2 : list A,
      (forall a : A, InEq a L1 -> ~ InEq a L2) -> Disjoint L1 L2.
(* Symmetry *)

Theorem DisjointCom : forall L1 L2 : list A, Disjoint L1 L2 -> Disjoint L2 L1.
intros L1 L2 H'; elim H'; auto.
intros L3 L4 H'0.
apply DisjointDef.
intros a H'1; red in |- *; intros H'2; absurd (InEq a L4); auto.
Qed.
(* First inversion lemma *)

Theorem DisjointInv1 :
 forall (a : A) (L1 L2 : list A), Disjoint L1 (a :: L2) -> Disjoint L1 L2.
intros a L1 L2 H'; inversion H'; apply DisjointDef.
intros a0 H'0; red in |- *; intros H'1.
lapply (H a0); [ intros H'3; apply H'3 | idtac ]; auto.
Qed.
(* Second inversion lemma *)

Theorem DisjointInv2 :
 forall (a : A) (L1 L2 : list A), Disjoint (a :: L1) L2 -> Disjoint L1 L2.
intros a L1 L2 H'.
apply DisjointCom.
apply DisjointInv1 with (a := a); auto.
apply DisjointCom; auto.
Qed.
(* First Destructor  *)

Theorem DisjointCons1 :
 forall (b : A) (L1 L2 : list A),
 Disjoint L1 L2 -> ~ InEq b L1 -> Disjoint L1 (b :: L2).
intros a L1 L2 H' H'0; inversion_clear H'.
apply DisjointDef; simpl in |- *; auto.
intros b H'1; red in |- *; intros H'2; inversion_clear H'2; auto.
case H'0; apply InEqComp with (a := b); auto.
absurd (InEq b L2); auto.
Qed.
(* Second destructor *)

Theorem DisjointCons2 :
 forall (a : A) (L1 L2 : list A),
 Disjoint L1 L2 -> ~ InEq a L2 -> Disjoint (a :: L1) L2.
intros a L1 L2 H' H'0; apply DisjointCom; auto.
apply DisjointCons1; auto.
apply DisjointCom; auto.
Qed.
(* Disjoint is compaatible with inclusion *)

Theorem DisjointInclL :
 forall L1 L2 L3 : list A, Disjoint L1 L2 -> InclEq L3 L1 -> Disjoint L3 L2.
intros L1 L2 L3 H' H'0.
apply DisjointDef; auto.
intros a H'1; inversion H'.
apply H; auto.
inversion H'0; auto.
Qed.

Theorem DisjointInclR :
 forall L1 L2 L3 : list A, Disjoint L1 L2 -> InclEq L3 L2 -> Disjoint L1 L3.
intros L1 L2 L3 H' H'0.
apply DisjointCom.
apply DisjointInclL with (L1 := L2); auto.
apply DisjointCom; auto.
Qed.

Theorem DisjointIncl :
 forall L1 L2 L3 L4 : list A,
 Disjoint L1 L2 -> InclEq L3 L1 -> InclEq L4 L2 -> Disjoint L3 L4.
intros L1 L2 L3 L4 H' H'0 H'1.
apply DisjointInclR with (L2 := L2); auto.
apply DisjointInclL with (L1 := L1); auto.
Qed.
(* Append two list (valid if the two list are ordered ) *)

Inductive append : list A -> list A -> list A -> Prop :=
  | appendNil1 : forall L1 : list A, append L1 nil L1
  | appendNil2 : forall L2 : list A, append nil L2 L2
  | appendEqA :
      forall (a b : A) (L1 L2 L3 : list A),
      eqA a b -> append L1 L2 L3 -> append (a :: L1) (b :: L2) (a :: L3)
  | appendLtA1 :
      forall (a b : A) (L1 L2 L3 : list A),
      ltA a b ->
      append L1 (b :: L2) L3 -> append (a :: L1) (b :: L2) (a :: L3)
  | appendLtA2 :
      forall (a b : A) (L1 L2 L3 : list A),
      ltA b a ->
      append (a :: L1) L2 L3 -> append (a :: L1) (b :: L2) (b :: L3).
Local Hint Resolve appendNil1 appendNil2 appendEqA appendLtA1 appendLtA2 : core.
(* If the two list are disjoint it does not matter how we do the append *)

Theorem appendCom :
 forall L1 L2 L3 : list A,
 append L1 L2 L3 -> Disjoint L1 L2 -> append L2 L1 L3.
intros L1 L2 L3 H'; elim H'; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; inversion_clear H'3.
absurd (InEq a (b :: L5)); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3.
apply appendLtA2; auto.
apply H'2; auto.
apply DisjointInv2 with (a := a); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; apply appendLtA1; auto.
apply H'2; auto.
apply DisjointInv1 with (a := b); auto.
Qed.
(* We get a greater list than the first *)

Theorem appendIncl1 :
 forall L1 L2 L3 : list A, append L1 L2 L3 -> InclEq L1 L3.
intros L1 L2 L3 H'; elim H'; auto with datatypes core.
intros a b L4 L5 L6 H'0 H'1 H'2.
apply InclEqDef; auto.
intros a0 H'3; inversion_clear H'3; auto.
inversion_clear H'2; auto.
intros a b L4 L5 L6 H'0 H'1 H'2; apply InclEqDef; auto.
intros a0 H'3; inversion_clear H'2; inversion_clear H'3; auto.
intros a b L4 L5 L6 H'0 H'1 H'2; apply InclEqDef; auto.
intros a0 H'3; inversion_clear H'2; inversion_clear H'3; auto.
Qed.
(* The condition of the two list is not necessary but we keep it for symmetry with Incl2 *)

Theorem appendDisjIncl1 :
 forall L1 L2 L3 : list A, append L1 L2 L3 -> Disjoint L1 L2 -> incl L1 L3.
intros L1 L2 L3 H'; elim H'; auto with datatypes core.
intros L4 H'0; red in |- *; intros a H'1; inversion H'1.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; inversion_clear H'3.
lapply (H a); [ intros H'4; case H'4 | idtac ]; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; apply incl_cons with (A := A);
 auto with datatypes core; apply incl_tran with (m := L6); 
 auto with datatypes core.
apply H'2; apply DisjointInv2 with (a := a); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; apply incl_tran with (m := L6);
 simpl in |- *; auto with datatypes core.
apply H'2; apply DisjointInv1 with (a := b); auto.
Qed.
(* Same for the second argument *)

Theorem appendIncl2 :
 forall L1 L2 L3 : list A, append L1 L2 L3 -> InclEq L2 L3.
intros L1 L2 L3 H'; elim H'; auto with datatypes core.
intros a b L4 L5 L6 H'0 H'1 H'2; apply InclEqDef.
intros a0 H'3; inversion_clear H'2; inversion_clear H'3; auto.
apply InEqComp with (a := b); auto.
intros a b L4 L5 L6 H'0 H'1 H'2; apply InclEqDef; auto.
intros a0 H'3; inversion_clear H'2; inversion_clear H'3; auto.
intros a b L4 L5 L6 H'0 H'1 H'2; apply InclEqDef; auto.
intros a0 H'3; inversion_clear H'2; inversion_clear H'3; auto.
Qed.
(* Same for the second argument *)

Theorem appendDisjIncl2 :
 forall L1 L2 L3 : list A, append L1 L2 L3 -> Disjoint L1 L2 -> incl L2 L3.
intros L1 L2 L3 H'; elim H'; auto with datatypes core.
intros L4 H'0; red in |- *; intros a H'1; inversion H'1.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; inversion_clear H'3.
lapply (H a); [ intros H'4; case H'4 | idtac ]; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; apply incl_tran with (m := L6);
 auto with datatypes core.
apply H'2; auto.
apply DisjointInv2 with (a := a); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3; apply incl_cons with (A := A);
 auto with datatypes core; apply incl_tran with (m := L6); 
 auto with datatypes core.
apply H'2; apply DisjointInv1 with (a := b); auto.
Qed.
(* The element an append belongs to one of the two list *)

Theorem appendInv :
 forall L1 L2 L3 : list A,
 append L1 L2 L3 -> forall m : A, In m L3 -> In m L1 \/ In m L2.
intros L1 L2 L3 H'; elim H'; simpl in |- *; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 m H'3; Elimc H'3; intros H'3;
 [ rewrite <- H'3 | idtac ]; auto.
elim (H'2 m); [ intros H'6 | intros H'6 | idtac ]; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 m H'3; Elimc H'3; intros H'3; auto.
elim (H'2 m); [ intros H'6 | intros H'6 | idtac ]; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 m H'3; Elimc H'3; intros H'3; auto.
elim (H'2 m); [ intros H'6 | intros H'6 | idtac ]; auto.
Qed.
(* Same but for InEq *)

Theorem appendEqInv :
 forall L1 L2 L3 : list A,
 append L1 L2 L3 -> forall m : A, InEq m L3 -> InEq m L1 \/ InEq m L2.
intros L1 L2 L3 H'; elim H'; simpl in |- *; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 m H'3; inversion_clear H'3; auto.
case (H'2 m H); intros H'5; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 m H'3; inversion_clear H'3; auto.
case (H'2 m H); intros H'5; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 m H'3; inversion_clear H'3; auto.
case (H'2 m H); intros H'5; auto.
Qed.
(* Compatibility with Disjoint *)

Theorem appendDisjoint :
 forall L1 L2 L3 : list A,
 append L1 L2 L3 ->
 forall L4 : list A, Disjoint L1 L4 -> Disjoint L2 L4 -> Disjoint L3 L4.
intros L1 L2 L3 H'; elim H'; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 L7 H'3 H'4.
apply DisjointCons2; auto.
apply H'2; auto.
apply DisjointInv2 with (a := a); auto.
apply DisjointInv2 with (a := b); auto.
inversion_clear H'3; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 L7 H'3 H'4; apply DisjointCons2; auto.
apply H'2; auto.
apply DisjointInv2 with (a := a); auto.
inversion_clear H'3; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 L7 H'3 H'4; apply DisjointCons2; auto.
apply H'2; auto.
apply DisjointInv2 with (a := b); auto.
inversion_clear H'4; auto.
Qed.
(* A mimimun for the two lists is a minimum for the append *)

Theorem appendSup :
 forall L1 L2 L3 : list A,
 append L1 L2 L3 ->
 forall a : A,
 (forall b : A, In b L1 -> ltA a b) ->
 (forall b : A, In b L2 -> ltA a b) -> forall b : A, In b L3 -> ltA a b.
intros L1 L2 L3 H'; elim H'; simpl in |- *; auto;
 intros a b L4 L5 L6 H'0 H'1 H'2 a0 H'3 H'4 b0 H'5;
 (Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]); 
 auto.
Qed.
(* If the two lists are ordered the result is ordered *)

Theorem appendOlist :
 forall L1 L2 L3 : list A,
 append L1 L2 L3 -> Olist L1 -> Olist L2 -> Olist L3.
intros L1 L2 L3 H'; elim H'; auto.
intros a b L4 L5 L6; case L6; auto.
intros a0 l H'0 H'1 H'2 H'3 H'4.
apply OlistCons; auto.
apply H'2; auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := b); auto.
apply appendSup with (L1 := L4) (L2 := L5) (L3 := a0 :: l); auto.
intros b0 H'5.
apply OlistSup with (L := L4); auto.
intros b0 H'5.
apply ltAeqAComp with (a := b) (b := b0); auto.
apply OlistSup with (L := L5); auto.
simpl in |- *; auto.
intros a b L4 L5 L6; case L6; auto.
intros a0 l H'0 H'1 H'2 H'3 H'4.
apply OlistCons; auto.
apply H'2; auto.
apply OlistInv with (a := a); auto.
apply appendSup with (L1 := L4) (L2 := b :: L5) (L3 := a0 :: l); auto.
intros b0 H'5.
apply OlistSup with (L := L4); auto.
intros b0 H'5.
apply OlistSup with (L := b :: L5); auto.
simpl in |- *; auto.
intros a b L4 L5 L6; case L6; auto.
intros a0 l H'0 H'1 H'2 H'3 H'4.
apply OlistCons; auto.
apply H'2; auto.
apply OlistInv with (a := b); auto.
apply appendSup with (L1 := a :: L4) (L2 := L5) (L3 := a0 :: l); auto.
intros b0 H'5.
apply OlistSup with (L := a :: L4); auto.
intros b0 H'5.
apply OlistSup with (L := L5); auto.
simpl in |- *; auto.
Qed.

(* We have a hard time to define this function so it can be evaluated inside Coq !! *)

Definition appendf :=
  (fix aux1 (l1 l2 : list A) {struct l1} : list A :=
     match l1, l2 with
     | a :: t1, b :: t2 =>
         match ltADec a b with
         | inleft (left _) => a :: aux1 t1 (b :: t2)
         | inleft (right _) =>
             (fix aux2 (l3 : list A) : list A :=
                match l3 with
                | c :: t3 =>
                    match ltADec a c with
                    | inleft (left _) => a :: aux1 t1 (c :: t3)
                    | inleft (right _) => c :: aux2 t3
                    | inright _ => a :: aux1 t1 t3
                    end
                | nil => a :: t1
                end) (b :: t2)
         | inright _ => a :: aux1 t1 t2
         end
     | nil, _ => l2
     | _, nil => l1
     end).
(* We simply show that it realize  append *)

Theorem appendfAppend : forall L1 L2 : list A, append L1 L2 (appendf L1 L2).
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; auto with datatypes core.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
intros a0 l0.
case (ltADec a a0); intros s; auto.
Casec s; intros s; auto.
apply appendLtA2; auto.
elim l0; auto.
intros a1 l1 H'0.
case (ltADec a a1); intros s1; auto.
Casec s1; intros s1; auto.
Qed.
Local Hint Resolve appendfAppend : core.
(* and now we simply lift of the propertiers of append to append f *)

Theorem appendfIncl1 :
 forall L1 L2 : list A, Disjoint L1 L2 -> incl L1 (appendf L1 L2).
intros L1 L2 HL1L2.
apply appendDisjIncl1 with (L2 := L2); auto.
Qed.

Theorem appendfIncl2 :
 forall L1 L2 : list A, Disjoint L1 L2 -> incl L2 (appendf L1 L2).
intros L1 L2 HL1L2.
apply appendDisjIncl2 with (L1 := L1); auto.
Qed.

Theorem appendfInv :
 forall (L1 L2 : list A) (m : A), In m (appendf L1 L2) -> In m L1 \/ In m L2.
intros L1 L2 m H'.
apply appendInv with (L3 := appendf L1 L2); auto.
Qed.

Theorem appendfInclEq1 : forall L1 L2 : list A, InclEq L1 (appendf L1 L2).
intros L1 L2.
apply appendIncl1 with (L2 := L2); auto.
Qed.

Theorem appendfInclEq2 : forall L1 L2 : list A, InclEq L2 (appendf L1 L2).
intros L1 L2.
apply appendIncl2 with (L1 := L1); auto.
Qed.

Theorem appendfInvEq :
 forall (L1 L2 : list A) (m : A),
 InEq m (appendf L1 L2) -> InEq m L1 \/ InEq m L2.
intros L1 L2 m H'.
apply appendEqInv with (L3 := appendf L1 L2); auto.
Qed.

Theorem NotInAppendf :
 forall (L1 L2 : list A) (m : A),
 ~ InEq m L1 -> ~ InEq m L2 -> ~ InEq m (appendf L1 L2).
intros L1 L2 m H' H'0; red in |- *; intros H'1.
case (appendfInvEq L1 L2 m H'1); auto.
Qed.

Theorem appendfDisjoint :
 forall L1 L2 : list A,
 Disjoint L1 L2 ->
 forall L3 : list A,
 Disjoint L1 L3 -> Disjoint L2 L3 -> Disjoint (appendf L1 L2) L3.
intros L1 L2 HL1L2 L3 H' H'0.
apply appendDisjoint with (L1 := L1) (L2 := L2); auto.
Qed.

Theorem appendfOlist :
 forall L1 L2 : list A, Olist L1 -> Olist L2 -> Olist (appendf L1 L2).
intros L1 L2 H' H'0.
apply appendOlist with (L1 := L1) (L2 := L2); auto.
Qed.

Theorem Olistf : forall L : list A, Olist L -> Olist (map f L).
intros L H'; elim H'; simpl in |- *; auto.
intros a b L0 H'0 H'1 H'2.
apply OlistCons; auto.
apply ltAeqAComp with (a := a) (b := b); auto.
Qed.

Theorem Disjointf :
 forall L1 L2 : list A, Disjoint L1 L2 -> Disjoint L1 (map f L2).
intros L1 L2 H'; elim H'; auto.
intros L3 L4; elim L4; simpl in |- *; auto.
intros H'0.
apply DisjointDef; simpl in |- *; auto.
intros a l H'0 H'1.
apply DisjointCons1; auto.
apply H'0; auto.
intros a0 H'2; red in |- *; intros H'3.
lapply (H'1 a0); [ intros H'5; case H'5 | idtac ]; auto.
red in |- *; intros H'2.
lapply (H'1 (f a)); [ intros H'5; case H'5 | idtac ]; auto.
Qed.

(* A variant of append when we consider that the second must be seen through a filter f *)

Definition fappendf :=
  (fix aux1 (l1 l2 : list A) {struct l1} : list A :=
     match l1, l2 with
     | a :: t1, b :: t2 =>
         match ltADec a b with
         | inleft (left _) => a :: aux1 t1 (b :: t2)
         | inleft (right _) =>
             (fix aux2 (l3 : list A) : list A :=
                match l3 with
                | c :: t3 =>
                    match ltADec a c with
                    | inleft (left _) => a :: aux1 t1 (c :: t3)
                    | inleft (right _) => f c :: aux2 t3
                    | inright _ => a :: aux1 t1 t3
                    end
                | nil => a :: t1
                end) (b :: t2)
         | inright _ => a :: aux1 t1 t2
         end
     | nil, _ => map f l2
     | _, nil => l1
     end).
(* Show that this filtered append is correct *)

Theorem fappendfAppend :
 forall L1 L2 : list A, append L1 (map f L2) (fappendf L1 L2).
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; auto with datatypes core.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
intros a0 l0.
case (ltADec a a0); intros s; auto.
Casec s; intros s; auto.
apply appendLtA1; auto.
apply ltAeqAComp with (a := a) (b := a0); auto.
generalize (H' (a0 :: l0)); simpl in |- *; auto.
apply appendLtA2; auto.
apply ltAeqAComp with (a := a0) (b := a); auto.
elim l0; auto.
intros a1 l1 H'0.
case (ltADec a a1); intros s1; auto.
Casec s1; intros s1; auto.
simpl in |- *.
apply appendLtA1; auto.
apply ltAeqAComp with (a := a) (b := a1); auto.
generalize (H' (a1 :: l1)); simpl in |- *; auto.
simpl in |- *; auto.
apply appendLtA2; auto.
apply ltAeqAComp with (a := a1) (b := a); auto.
simpl in |- *.
apply appendEqA; auto.
apply eqATrans with a1; auto.
apply appendEqA; auto.
apply eqATrans with a0; auto.
Qed.
Local Hint Resolve fappendfAppend : core.
(* We lift the properties as usual *)

Theorem fappendfIncl1 :
 forall (L1 L2 : list A) (HL1L2 : Disjoint L1 L2), incl L1 (fappendf L1 L2).
intros L1 L2 HL1L2.
apply appendDisjIncl1 with (L2 := map f L2); auto.
apply Disjointf; auto.
Qed.

Theorem fappendfIncl2 :
 forall (L1 L2 : list A) (HL1L2 : Disjoint L1 L2),
 incl (map f L2) (fappendf L1 L2).
intros L1 L2 HL1L2.
apply appendDisjIncl2 with (L1 := L1); auto.
apply Disjointf; auto.
Qed.

Theorem fappendfInv :
 forall (L1 L2 : list A) (m : A),
 In m (fappendf L1 L2) -> In m L1 \/ In m (map f L2).
intros L1 L2 m H'.
apply appendInv with (L3 := fappendf L1 L2); auto.
Qed.

Theorem fappendfInclEq1 : forall L1 L2 : list A, InclEq L1 (fappendf L1 L2).
intros L1 L2.
apply appendIncl1 with (L2 := map f L2); auto.
Qed.

Theorem fappendfInclEq2 :
 forall L1 L2 : list A, InclEq (map f L2) (fappendf L1 L2).
intros L1 L2.
apply appendIncl2 with (L1 := L1); auto.
Qed.

Theorem fappendfInvEq :
 forall (L1 L2 : list A) (m : A),
 InEq m (fappendf L1 L2) -> InEq m L1 \/ InEq m (map f L2).
intros L1 L2 m H'.
apply appendEqInv with (L3 := fappendf L1 L2); auto.
Qed.

Theorem fappendfDisjoint :
 forall (L1 L2 : list A) (HL1L2 : Disjoint L1 L2) (L3 : list A),
 Disjoint L1 L3 -> Disjoint L2 L3 -> Disjoint (fappendf L1 L2) L3.
intros L1 L2 HL1L2 L3 H' H'0.
apply appendDisjoint with (L1 := L1) (L2 := map f L2); auto.
apply DisjointCom.
apply Disjointf.
apply DisjointCom; auto.
Qed.

Theorem fappendfOlist :
 forall L1 L2 : list A, Olist L1 -> Olist L2 -> Olist (fappendf L1 L2).
intros L1 L2 H' H'0.
apply appendOlist with (L1 := L1) (L2 := map f L2); auto.
apply Olistf; auto.
Qed.

(* A test function that is finer that the equality *)
Variable test : A -> A -> Prop.
Variable testDec : forall a b : A, eqA a b -> {test a b} + {~ test a b}.
Variable testEq : forall a b : A, test a b -> eqA a b.

(* Finding the minimum element that verifies test *)

Definition getMin :=
  (fix aux1 (l1 l2 : list A) {struct l1} : option A :=
     match l1, l2 with
     | a :: t1, b :: t2 =>
         match ltADec a b with
         | inleft (left _) => aux1 t1 (b :: t2)
         | inleft (right _) =>
             (fix aux2 (l3 : list A) : option A :=
                match l3 with
                | c :: t3 =>
                    match ltADec a c with
                    | inleft (left _) => aux1 t1 (c :: t3)
                    | inleft (right _) => aux2 t3
                    | inright H =>
                        match testDec a c H with
                        | left _ => Some a
                        | right __ => aux2 t3
                        end
                    end
                | nil => None
                end) (b :: t2)
         | inright H =>
             match testDec a b H with
             | left _ => Some a
             | right _ => aux1 t1 t2
             end
         end
     | nil, _ => None
     | _, nil => None
     end).
(* If there is such elemnt it belongs to the first list *)

Theorem geMinIn :
 forall (L1 L2 : list A) (a : A),
 Olist L1 -> Olist L2 -> getMin L1 L2 = Some a -> In a L1.
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; auto with datatypes core.
intros a H' H'0 H'1; discriminate.
intros a l a0 H' H'0 H'1; discriminate.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
intros a0 H'0 H'1 H'2; discriminate.
intros a0 l0 a1 H'0 H'1.
case (ltADec a a0); intros s; auto.
Casec s; intros s; auto.
intros H'2; right.
apply (H' (a0 :: l0)); auto.
apply OlistInv with (a := a); auto.
generalize H'1; elim l0; auto.
intros H'2 H'3; discriminate.
intros a2 l1 H'2 H'3.
case (ltADec a a2); intros s1; auto.
Casec s1; intros s1; auto.
intros H'4; right.
apply (H' (a2 :: l1)); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
intros H'4; case H'2; auto.
apply OlistSkip with (b := a2); auto.
case (testDec a a2 s1); auto.
intros H'4 H'5; inversion H'5; auto.
intros H'4 H'5; case H'2; auto.
apply OlistSkip with (b := a2); auto.
case (testDec a a0 s); auto.
intros H'2 H'3; inversion H'3; auto.
intros H'2 H'3; right.
apply (H' l0); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
Qed.
(* and there is an element in L2 such that test is satisified *)

Theorem getMinComp :
 forall (L1 L2 : list A) (a : A),
 Olist L1 ->
 Olist L2 -> getMin L1 L2 = Some a -> exists b : A, test a b /\ In b L2.
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; auto with datatypes core.
intros a H' H'0 H'1; discriminate.
intros a l a0 H' H'0 H'1; discriminate.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
intros a0 H'0 H'1 H'2; discriminate.
intros a0 l0 a1 H'0 H'1.
case (ltADec a a0); intros s; auto.
Casec s; intros s; auto.
intros H'2; case (H' (a0 :: l0) a1); auto.
apply OlistInv with (a := a); auto.
intros x H'3; elim H'3; intros H'4 H'5; exists x; auto.
generalize H'1; elim l0; auto.
intros H'2 H'3; discriminate.
intros a2 l1 H'2 H'3.
case (ltADec a a2); intros s1; auto.
Casec s1; intros s1; auto.
intros H'4; case (H' (a2 :: l1) a1); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
intros x H'5; elim H'5; intros H'6 H'7; exists x; auto.
intros H'4; case H'2; auto.
apply OlistSkip with (b := a2); auto.
intros x H'5; elim H'5; intros H'6 H'7; exists x; intuition auto with datatypes.
case (testDec a a2 s1); auto.
intros H'4 H'5; inversion H'5; auto.
exists a2; split; auto with datatypes core.
rewrite <- H0; auto.
intros H'4 H'5; case H'2; auto.
apply OlistSkip with (b := a2); auto.
intros x H'6; elim H'6; intros H'7 H'8; exists x; split; auto with datatypes core;
 case H'8; auto with datatypes core.
case (testDec a a0 s); auto.
intros H'2 H'3; inversion H'3; auto.
exists a0; split; auto with datatypes core.
rewrite <- H0; auto.
intros H'2 H'3; case (H' l0 a1); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
intros x H'4; elim H'4; intros H'5 H'6; exists x; auto.
Qed.
(* and it is the minimal element such that *)

Theorem getMinMin :
 forall (L1 L2 : list A) (a : A),
 Olist L1 ->
 Olist L2 ->
 getMin L1 L2 = Some a ->
 forall b c : A, ltA b a -> In b L1 -> In c L2 -> ~ test b c.
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; auto with datatypes core.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
intros a0 l0 a1 H'0 H'1.
case (ltADec a a0); intros s; auto.
Casec s; intros s; auto.
intros H'2 b c H'3 H'4 H'5; Casec H'4; intros H'4; auto.
rewrite <- H'4; auto.
red in |- *; intros H'6; absurd (In c (a0 :: l0)); auto.
apply OlistUnique with (a := a); auto.
apply (H' (a0 :: l0) a1); auto.
apply OlistInv with (a := a); auto.
generalize H'1; elim l0; auto.
intros H'2 H'3; discriminate.
intros a2 l1 H'2 H'3.
case (ltADec a a2); intros s1; auto.
Casec s1; intros s1; auto.
intros H'4 b c H'5 H'6 H'7; Casec H'6; intros H'6; auto.
rewrite <- H'6; auto.
Elimc H'7; intros H'7; [ rewrite <- H'7 | idtac ]; auto.
red in |- *; intros H'8; absurd (eqA a0 a); auto.
red in |- *; intros H'8; absurd (In c (a2 :: l1)); auto.
apply OlistUnique with (a := a); auto.
apply OlistCons; auto.
apply OlistInv with (a := a0); auto.
Elimc H'7; intros H'7; [ rewrite <- H'7 | idtac ]; auto.
red in |- *; intros H'8; Contradict H'6; auto.
apply OlistUnique with (a := a0); auto.
apply OlistSkip with (b := a); auto.
apply (H' (a2 :: l1) a1); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
simpl in |- *; intros H'4 b c H'5 H'6 H'7; auto.
Casec H'7; intros H'7; auto.
apply (H'2 (OlistSkip _ _ _ H'3) H'4); auto.
Casec H'7; intros H'7; auto.
rewrite <- H'7.
Elimc H'6; intros H'6; [ rewrite <- H'6 | idtac ]; auto.
red in |- *; intros H'8; absurd (eqA a2 a); auto.
Contradict H'6.
apply OlistUnique with (a := a2); auto.
apply OlistSkip with (b := a); auto.
apply (H'2 (OlistSkip _ _ _ H'3) H'4); auto.
case (testDec a a2 s1); auto.
intros H'4 H'5; inversion H'5; auto.
rewrite <- H0.
intros b c H'6 H'7 H'8; absurd (In b (a :: l)); auto.
apply OlistUnique with (a := b); auto.
intros H'4 H'5 b c H'6 H'7 H'8.
Elimc H'8; simpl in |- *; intros H'8.
apply (H'2 (OlistSkip _ _ _ H'3) H'5); auto.
Elimc H'8; simpl in |- *; intros H'8.
rewrite <- H'8.
Elimc H'7; intros H'7; [ rewrite <- H'7 | idtac ]; auto.
Contradict H'7; auto.
apply OlistUnique with (a := a); auto.
apply eqATrans with a2; auto.
apply (H'2 (OlistSkip _ _ _ H'3) H'5); auto.
case (testDec a a0 s); auto.
intros H'2 H'3; inversion H'3.
intros b c H'4 H'5 H'6.
Elimc H'5; intros H'5; [ rewrite <- H'5 in H'4; Contradict H'4 | idtac ];
 auto.
Elimc H'6; intros H'6; [ rewrite <- H'6 | idtac ]; auto.
Contradict H'5.
apply OlistUnique with (a := a); auto.
apply eqATrans with a0; auto.
Contradict H'5.
apply OlistUnique with (a := b); auto.
apply OlistSkip with (b := a1); auto.
apply OlistCons; auto.
rewrite <- H0; auto.
intros H'2 H'3 b c H'4 H'5 H'6.
Elimc H'6; intros H'6; [ rewrite <- H'6 | idtac ]; auto.
Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]; auto.
Contradict H'5.
apply OlistUnique with (a := a); auto.
apply eqATrans with a0; auto.
Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]; auto.
Contradict H'6.
apply OlistUnique with (a := a0); auto.
apply eqATrans with a; auto.
apply (H' l0 a1); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
Qed.
(* If there is not then this mean that there is no couple (a,b) such that (test a b) *)

Theorem getMinNone :
 forall L1 L2 : list A,
 Olist L1 ->
 Olist L2 ->
 getMin L1 L2 = None -> forall a b : A, In a L1 -> In b L2 -> ~ test a b.
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; auto with datatypes core.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
intros a0 l0 a1 H'0.
case (ltADec a a0); intros s; auto.
Casec s; intros s; auto.
intros H'1 a2 b H'2; Elimc H'2; intros H'2; [ rewrite <- H'2 | idtac ]; auto.
intros H'3; red in |- *; intros H'4; absurd (In b (a0 :: l0)); auto.
apply OlistUnique with (a := a); auto.
intros H'3; apply (H' (a0 :: l0)); auto.
apply OlistInv with (a := a); auto.
generalize H'0; elim l0; auto.
intros H'1 H'2 a2 b H'3 H'4; Elimc H'4; intros H'4;
 [ rewrite <- H'4 | idtac ]; auto.
Elimc H'3; intros H'3; [ rewrite <- H'3 | idtac ].
red in |- *; intros H'5; absurd (eqA a0 a); auto.
Contradict H'3; auto.
apply OlistUnique with (a := a0); auto.
apply OlistSkip with (b := a); auto.
intros a2 l1 H'1 H'2.
case (ltADec a a2); intros s1; auto.
Casec s1; intros s1; auto.
intros H'3 a3 b H'4; Elimc H'4; intros H'4; [ rewrite <- H'4 | idtac ]; auto.
intros H'5; Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]; auto.
red in |- *; intros H'6; absurd (eqA a0 a); auto.
Contradict H'5; auto.
apply OlistUnique with (a := a); auto.
apply OlistCons; auto.
apply OlistInv with (a := a0); auto.
intros H'5; Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ].
Contradict H'4; auto.
apply OlistUnique with (a := a0); auto.
apply OlistSkip with (b := a); auto.
apply (H' (a2 :: l1)); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
intros H'3 a3 b H'4 H'5.
Elimc H'5; simpl in |- *; intros H'5; [ rewrite <- H'5 | idtac ]; auto.
apply H'1; auto.
apply OlistSkip with (b := a2); auto.
Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]; auto.
Elimc H'4; intros H'4; [ rewrite <- H'4 | idtac ].
red in |- *; intros H'6; absurd (eqA a2 a); auto.
Contradict H'4.
apply OlistUnique with (a := a2); auto.
apply OlistSkip with (b := a); auto.
apply H'1; auto.
apply OlistSkip with (b := a2); auto.
case (testDec a a2 s1); auto.
intros H'3 H'4; discriminate.
intros H'3 H'4 a3 b H'5 H'6.
Elimc H'6; simpl in |- *; intros H'6; [ rewrite <- H'6 | idtac ].
Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ].
red in |- *; intros H'7; absurd (eqA a0 a); auto.
Contradict H'5.
apply OlistUnique with (a := a0); auto.
apply OlistSkip with (b := a); auto.
Elimc H'6; intros H'6; [ rewrite <- H'6 | idtac ].
Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]; auto.
Contradict H'5.
apply OlistUnique with (a := a); auto.
apply eqATrans with a2; auto.
apply H'1; auto.
apply OlistSkip with (b := a2); auto.
case (testDec a a0 s); auto.
intros H'1 H'2; discriminate.
intros H'1 H'2 a2 b H'3; Elimc H'3; intros H'3; [ rewrite <- H'3 | idtac ];
 auto.
intros H'4; Elimc H'4; intros H'4; [ rewrite <- H'4 | idtac ]; auto.
Contradict H'4; auto.
apply OlistUnique with (a := a0); auto.
apply eqATrans with a; auto.
intros H'4; Elimc H'4; intros H'4; [ rewrite <- H'4 | idtac ].
Contradict H'3; auto.
apply OlistUnique with (a := a); auto.
apply eqATrans with a0; auto.
apply (H' l0); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
Qed.
(* Intersection of 2 list *)

Inductive inter : list A -> list A -> list A -> Prop :=
  | interNil1 : forall L1 : list A, inter L1 nil nil
  | interNil2 : forall L2 : list A, inter nil L2 nil
  | interEqA :
      forall (a b : A) (L1 L2 L3 : list A),
      eqA a b -> inter L1 L2 L3 -> inter (a :: L1) (b :: L2) (a :: L3)
  | interLtA1 :
      forall (a b : A) (L1 L2 L3 : list A),
      ltA a b -> inter L1 (b :: L2) L3 -> inter (a :: L1) (b :: L2) L3
  | interLtA2 :
      forall (a b : A) (L1 L2 L3 : list A),
      ltA b a -> inter (a :: L1) L2 L3 -> inter (a :: L1) (b :: L2) L3.
(* The intersection is included in the first list *)

Theorem interIncl1 : forall L1 L2 L3 : list A, inter L1 L2 L3 -> InclEq L3 L1.
intros L1 L2 L3 H'; elim H'; auto with datatypes core.
intros a b L4 L5 L6 H'0 H'1 H'2.
apply InclEqCons; auto.
apply InclEqTrans with (y := L4); auto.
intros a b L4 L5 L6 H'0 H'1 H'2.
apply InclEqTrans with (y := L4); auto.
Qed.
(* The intersection is included in the second list *)

Theorem interIncl2 : forall L1 L2 L3 : list A, inter L1 L2 L3 -> InclEq L3 L2.
intros L1 L2 L3 H'; elim H'; auto with datatypes core.
intros a b L4 L5 L6 H'0 H'1 H'2.
apply InclEqCons; auto.
apply InclEqTrans with (y := L5); auto.
intros a b L4 L5 L6 H'0 H'1 H'2.
apply InclEqTrans with (y := L5); auto.
Qed.
(* A minimum for the the two list is a minimum for the intersection *)

Theorem interSup :
 forall L1 L2 L3 : list A,
 inter L1 L2 L3 ->
 forall a : A,
 (forall b : A, In b L1 -> ltA a b) ->
 (forall b : A, In b L2 -> ltA a b) -> forall b : A, In b L3 -> ltA a b.
intros L1 L2 L3 H'; elim H'; simpl in |- *; auto;
 intros a b L4 L5 L6 H'0 H'1 H'2 a0 H'3 H'4 b0 H'5;
 (Elimc H'5; intros H'5; [ rewrite <- H'5 | idtac ]); 
 auto.
Qed.
(* Intersection is ordered *)

Theorem interOlist :
 forall L1 L2 L3 : list A, inter L1 L2 L3 -> Olist L1 -> Olist L2 -> Olist L3.
intros L1 L2 L3 H'; elim H'; auto.
intros a b L4 L5 L6; case L6; auto.
intros a0 l H'0 H'1 H'2 H'3 H'4.
apply OlistCons; auto.
apply H'2; auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := b); auto.
apply interSup with (L1 := L4) (L2 := L5) (L3 := a0 :: l); auto.
intros b0 H'5.
apply OlistSup with (L := L4); auto.
intros b0 H'5.
apply ltAeqAComp with (a := b) (b := b0); auto.
apply OlistSup with (L := L5); auto.
simpl in |- *; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3 H'4.
apply H'2; auto.
apply OlistInv with (a := a); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 H'3 H'4.
apply H'2; auto.
apply OlistInv with (a := b); auto.
Qed.
(* An ordered list can't have multiple elements *)

Theorem InEqNList : forall (a : A) (L : list A), InEq a L -> ~ Olist (a :: L).
intros a L; elim L; auto.
intros H'; inversion H'; auto.
intros a0 l H' H'0; inversion H'0; auto.
red in |- *; intros H'1; inversion H'1; auto.
absurd (eqA a a0); auto.
red in |- *; intros H'1; case H'; auto.
apply OlistSkip with (b := a0); auto.
Qed.
(* The head of the list is a minimum *)

Theorem InEqSup :
 forall (a b : A) (L : list A), InEq a L -> Olist (b :: L) -> ltA b a.
intros a b L; elim L; auto.
intros H'; inversion H'; auto.
intros a0 l H' H'0 H'1; inversion H'0; auto.
apply ltAeqAComp with (a := b) (b := a0); auto.
apply OlistSup with (L := a0 :: l); auto with datatypes core.
apply H'; auto.
apply OlistSkip with (b := a0); auto.
Qed.
(* Inversion lemma for inclusion *)

Theorem InEqOlistInv :
 forall (a b : A) (L1 L2 : list A),
 InclEq (a :: L1) (b :: L2) ->
 Olist (a :: L1) ->
 Olist (b :: L2) -> InclEq (a :: L1) L2 \/ eqA a b /\ InclEq L1 L2.
intros a b L1 L2 H' H'0 H'1.
case (ltADec a b); intros Eqab.
Casec Eqab; intros Eqab.
absurd (Olist (a :: b :: L2)); auto.
apply InEqNList; auto.
inversion H'; auto.
left.
inversion H'; auto.
apply InclEqDef; auto.
intros a0 H'2.
lapply (H a0); [ intros H'4 | idtac ]; auto.
inversion H'4; auto.
absurd (Olist (a0 :: a :: L1)); auto.
apply InEqNList; auto.
apply OlistCons; auto.
apply ltAeqAComp with (a := b) (b := a); auto.
right; split; auto.
apply InclEqDef; auto.
intros a0 H'2.
inversion H'.
lapply (H a0); [ intros H'4 | idtac ]; auto.
inversion H'4; auto.
absurd (eqA a a0); auto.
apply ltAImpNotEqA; auto.
apply InEqSup with (L := L1); auto.
apply eqATrans with (y := b); auto.
Qed.
(* The intersection is the maximum list that is included in both *)

Theorem interMin :
 forall L1 L2 L3 L4 : list A,
 inter L1 L2 L3 ->
 Olist L1 ->
 Olist L2 ->
 Olist L3 -> Olist L4 -> InclEq L4 L1 -> InclEq L4 L2 -> InclEq L4 L3.
intros L1 L2 L3 L4 H'; generalize L4; clear L4; elim H'; auto.
intros a b L4 L5 L6 H'0 H'1 H'2 L7; case L7; auto.
intros a0 l H'3 H'4 H'5 H'6 H'7 H'8.
case (eqADec a0 a); auto.
intros H'9.
apply InclEqCons; auto.
apply InclEqTrans with (y := L6); auto.
apply H'2; auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := b); auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := a0); auto.
apply InclEqOlist with (a := a0) (b := a); auto.
apply InclEqOlist with (a := a0) (b := b); auto.
intros H'9.
apply InclEqTrans with (y := L6); auto.
apply H'2; auto.
apply OlistInv with (a := a); auto.
apply OlistInv with (a := b); auto.
apply OlistInv with (a := a); auto.
elim (InEqOlistInv a0 a l L4);
 [ intros H'17; apply H'17
 | intros H'17; elim H'17; intros H'18
 | idtac
 | idtac
 | idtac ]; auto.
case H'9; auto.
elim (InEqOlistInv a0 b l L5);
 [ intros H'17; apply H'17
 | intros H'17; elim H'17; intros H'18
 | idtac
 | idtac
 | idtac ]; auto.
case H'9; auto.
apply eqATrans with (y := b); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 L7; case L7; auto.
intros a0 l H'3 H'4 H'5 H'6 H'7 H'8.
apply H'2; auto.
apply OlistInv with (a := a); auto.
elim (InEqOlistInv a0 a l L4);
 [ intros H'17; apply H'17
 | intros H'17; elim H'17; intros H'18
 | idtac
 | idtac
 | idtac ]; auto.
absurd (Olist (a0 :: b :: L5)); auto.
apply InEqNList; auto.
inversion H'8; auto.
apply OlistCons; auto.
apply ltAeqAComp with (a := a) (b := b); auto.
intros a b L4 L5 L6 H'0 H'1 H'2 L7; case L7; auto.
intros a0 l H'3 H'4 H'5 H'6 H'7 H'8.
apply H'2; auto.
apply OlistInv with (a := b); auto.
elim (InEqOlistInv a0 b l L5);
 [ intros H'17; apply H'17
 | intros H'17; elim H'17; intros H'18
 | idtac
 | idtac
 | idtac ]; auto.
absurd (Olist (a0 :: a :: L4)); auto.
apply InEqNList; auto.
inversion H'7; auto.
apply OlistCons; auto.
apply ltAeqAComp with (a := b) (b := a); auto.
Qed.
(* intersection commutes if the list are ordered *)

Theorem interCom :
 forall L1 L2 L3 L4 : list A,
 inter L1 L2 L3 ->
 inter L2 L1 L4 -> Olist L1 -> Olist L2 -> Olist L3 -> Olist L4 -> EqL L3 L4.
intros L1 L2 L3 L4 H' H'0 H'1 H'2 H'3 H'4.
apply EqLOlist; auto.
apply interMin with (L1 := L2) (L2 := L1); auto.
apply interIncl2 with (L1 := L1); auto.
apply interIncl1 with (L2 := L2); auto.
apply interMin with (L1 := L1) (L2 := L2); auto.
apply interIncl2 with (L1 := L2); auto.
apply interIncl1 with (L2 := L1); auto.
Qed.

(* A function that realizes intersection *)

Definition interf :=
  (fix aux1 (l1 l2 : list A) {struct l1} : list A :=
     match l1, l2 with
     | a :: t1, b :: t2 =>
         match ltADec a b with
         | inleft (left _) => aux1 t1 (b :: t2)
         | inleft (right _) =>
             (fix aux2 (l3 : list A) : list A :=
                match l3 with
                | c :: t3 =>
                    match ltADec a c with
                    | inleft (left _) => aux1 t1 (c :: t3)
                    | inleft (right _) => aux2 t3
                    | inright _ => a :: aux1 t1 t3
                    end
                | nil => nil
                end) (b :: t2)
         | inright _ => a :: aux1 t1 t2
         end
     | nil, _ => nil
     | _, nil => nil
     end).
(* it is correct *)

Theorem interfProp1 : forall L1 L2 : list A, inter L1 L2 (interf L1 L2).
intros L1; elim L1; simpl in |- *.
intros L2; case L2; simpl in |- *; intros; apply interNil2; auto.
intros a l H' L2; case L2; simpl in |- *; auto with datatypes core.
apply interNil1; auto.
intros a0 l0.
case (ltADec a a0); intros s; [ Casec s; intros s | idtac ].
apply interLtA1; auto.
apply interLtA2; auto.
elim l0; auto.
apply interNil1; auto.
intros a1 l1 H'0.
case (ltADec a a1); intros s1; [ Casec s1; intros s1 | idtac ].
apply interLtA1; auto.
apply interLtA2; auto.
apply interEqA; auto.
apply interEqA; auto.
Qed.
Local Hint Resolve interfProp1 : core.
(* Now we can lift the properties *)

Theorem interfIncl1 : forall L1 L2 : list A, InclEq (interf L1 L2) L1.
intros L1 L2.
apply interIncl1 with (L2 := L2); auto.
Qed.

Theorem interfIncl2 : forall L1 L2 : list A, InclEq (interf L1 L2) L2.
intros L1 L2.
apply interIncl2 with (L1 := L1); auto.
Qed.

Theorem interfOlist :
 forall L1 L2 : list A, Olist L1 -> Olist L2 -> Olist (interf L1 L2).
intros L1 L2 H' H'0.
apply interOlist with (L1 := L1) (L2 := L2); auto.
Qed.

Theorem interfMin :
 forall L1 L2 L3 : list A,
 Olist L1 ->
 Olist L2 ->
 Olist L3 -> InclEq L3 L1 -> InclEq L3 L2 -> InclEq L3 (interf L1 L2).
intros L1 L2 L3 H' H'0 H'1 H'2 H'3.
apply interMin with (L1 := L1) (L2 := L2); auto.
apply interfOlist; auto.
Qed.

Theorem interfCom :
 forall L1 L2 : list A,
 Olist L1 -> Olist L2 -> EqL (interf L1 L2) (interf L2 L1).
intros L1 L2 H' H'0.
apply interCom with (L1 := L1) (L2 := L2); auto.
apply interfOlist; auto.
apply interfOlist; auto.
Qed.
End OrderedList.
