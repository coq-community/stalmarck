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
                                                                           
          Stalmarck  :  interImplement                                     
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Implement the intersection (2 files)
 In this file we simply show that to build the intersection, we simply need for
  every a, first find the maller b that is in relation with a in both arrays and
  add the equation a=b*)
Require Export addArray.
Require Export interState.
Require Export memoryImplement.
Section inter.

(* Return the equivalent class of an element plus the polarity *)

Definition getEquiv (Ar : rArray vM) (a : rNat) : list rZ * bool :=
  match rArrayGet vM Ar a with
  | ref r =>
      match r with
      | rZPlus r0 =>
          match rArrayGet vM Ar r0 with
          | ref _ => (nil, true)
          | class L => (rZPlus r0 :: L, false)
          end
      | rZMinus r0 =>
          match rArrayGet vM Ar r0 with
          | ref _ => (nil, true)
          | class L => (rZPlus r0 :: L, true)
          end
      end
  | class L => (rZPlus a :: L, false)
  end.

Definition getEquivProp :
  forall Ar : rArray vM,
  wellFormedArray Ar ->
  forall a : rNat,
  match getEquiv Ar a with
  | (L, true) =>
      OlistRz L /\
      (forall c : rZ, In (rZComp c) L <-> evalZ Ar c = evalZ Ar (rZPlus a))
  | (L, false) =>
      OlistRz L /\
      (forall c : rZ, In c L <-> evalZ Ar c = evalZ Ar (rZPlus a))
  end.
intros Ar War a; unfold getEquiv in |- *; CaseEq (rArrayGet _ Ar a).
intros r; case r.
intros r0 H'; CaseEq (rArrayGet _ Ar r0).
intros r1 H'0; absurd False; auto with stalmarck.
Contradict H'0.
apply wfPcr with (2 := H'); auto with stalmarck.
intros L HL; split; auto with stalmarck.
generalize HL; case L; auto with stalmarck.
intros H'0; red in |- *; apply OlistOne; auto with stalmarck.
intros r1 l H'0.
red in |- *; apply OlistCons; auto with stalmarck.
apply wfOl with (2 := H'0); auto with stalmarck.
red in |- *; apply wellFormedArrayInImpLt with (2 := H'0); simpl in |- *;
 auto with stalmarck.
intros c; case c; simpl in |- *; split.
intros H'0; Elimc H'0; intros H'0.
inversion H'0; rewrite <- H0.
unfold evalN in |- *; rewrite HL; rewrite H'; auto with stalmarck.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto with stalmarck.
unfold evalN in |- *; rewrite H'; auto with stalmarck.
CaseEq (rArrayGet vM Ar r1); auto with stalmarck.
intros r2 H'0 H'1; right.
replace (rZPlus r1) with (samePol (rZPlus r0) r1).
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite <- H'1; auto with stalmarck.
simpl in |- *; auto with stalmarck.
intros H'0; Elimc H'0; intros H'0.
discriminate.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto with stalmarck.
unfold evalN in |- *; rewrite H'; auto with stalmarck.
CaseEq (rArrayGet vM Ar r1); auto with stalmarck.
intros r2 H'0 H'1; right.
replace (rZMinus r1) with (samePol (rZComp (rZPlus r0)) r1).
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite <- H'1; rewrite rZCompInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
intros r0 H'; CaseEq (rArrayGet _ Ar r0).
intros r1 H'0; absurd False; auto with stalmarck.
Contradict H'0.
apply wfPcr with (2 := H'); auto with stalmarck.
intros L HL; split; auto with stalmarck.
generalize HL; case L; auto with stalmarck.
intros H'0; red in |- *; apply OlistOne; auto with stalmarck.
intros r1 l H'0.
red in |- *; apply OlistCons; auto with stalmarck.
apply wfOl with (2 := H'0); auto with stalmarck.
red in |- *; apply wellFormedArrayInImpLt with (2 := H'0); simpl in |- *;
 auto with stalmarck.
intros c; case c; simpl in |- *; split.
intros H'0; Elimc H'0; intros H'0.
discriminate.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto with stalmarck.
unfold evalN in |- *; rewrite H'; auto with stalmarck.
CaseEq (rArrayGet vM Ar r1); auto with stalmarck.
intros r2 H'0 H'1; right.
replace (rZMinus r1) with (samePol (rZMinus r0) r1).
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite <- H'1; auto with stalmarck.
simpl in |- *; auto with stalmarck.
intros l H'0 H'1; discriminate.
intros H'0; Elimc H'0; intros H'0.
inversion H'0; rewrite <- H0.
unfold evalN in |- *; rewrite HL; rewrite H'; auto with stalmarck.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto with stalmarck.
unfold evalN in |- *; rewrite H'; auto with stalmarck.
CaseEq (rArrayGet vM Ar r1); auto with stalmarck.
intros r2 H'0 H'1; right.
replace (rZPlus r1) with (samePol (rZComp (rZMinus r0)) r1).
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite <- H'1; rewrite rZCompInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
simpl in |- *; intros l H'0 H'1; inversion H'1; auto with stalmarck.
intros L H'; split.
generalize H'; case L.
intros H'0; red in |- *; apply OlistOne; auto with stalmarck.
intros r l H'0; red in |- *; apply OlistCons; auto with stalmarck.
apply wfOl with (2 := H'0); auto with stalmarck.
red in |- *; apply wellFormedArrayInImpLt with (2 := H'0); simpl in |- *;
 auto with stalmarck.
intros c; case c; simpl in |- *; split.
intros H'0; Elimc H'0; intros H'0.
inversion H'0; rewrite <- H0; auto with stalmarck.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ H' H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto with stalmarck.
unfold evalN in |- *; rewrite H'; auto with stalmarck.
CaseEq (rArrayGet vM Ar r); auto with stalmarck.
intros r0 H'0 H'1; right.
replace (rZPlus r) with (samePol (rZPlus a) r).
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite <- H'1; auto with stalmarck.
simpl in |- *; auto with stalmarck.
intros H'0; Elimc H'0; intros H'0.
discriminate.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ H' H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto with stalmarck.
unfold evalN in |- *; rewrite H'; auto with stalmarck.
CaseEq (rArrayGet vM Ar r); auto with stalmarck.
intros r0 H'0 H'1; right.
replace (rZMinus r) with (samePol (rZComp (rZPlus a)) r).
apply wfPcc2 with (Ar := Ar); auto with stalmarck.
rewrite <- H'1; rewrite rZCompInv; auto with stalmarck.
simpl in |- *; auto with stalmarck.
Defined.

Theorem getEquivProp1 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rNat) (c : rZ),
 snd (getEquiv Ar a) = true ->
 (In (rZComp c) (fst (getEquiv Ar a)) <-> evalZ Ar c = evalZ Ar (rZPlus a)).
intros Ar War a c; generalize (getEquivProp Ar War a); case (getEquiv Ar a);
 auto with stalmarck.
intros x; case x; auto with stalmarck.
intros b; case b; simpl in |- *; auto with stalmarck.
intros H'; elim H'; auto with stalmarck.
intros H' H'0; discriminate.
intros r l b; case b; simpl in |- *; auto with stalmarck.
intros H'; elim H'; auto with stalmarck.
intros H' H'0; discriminate.
Qed.

Theorem getEquivProp2 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rNat) (c : rZ),
 snd (getEquiv Ar a) = false ->
 (In c (fst (getEquiv Ar a)) <-> evalZ Ar c = evalZ Ar (rZPlus a)).
intros Ar War a c; generalize (getEquivProp Ar War a); case (getEquiv Ar a);
 auto with stalmarck.
intros x; case x; auto with stalmarck.
intros b; case b; simpl in |- *; auto with stalmarck.
intros H' H'0; discriminate.
intros H'; elim H'; auto with stalmarck.
intros r l b; case b; simpl in |- *; auto with stalmarck.
intros H' H'0; discriminate.
intros H'; elim H'; auto with stalmarck.
Qed.

Theorem getEquivProp3 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rNat),
 OlistRz (fst (getEquiv Ar a)).
intros Ar War a; generalize (getEquivProp Ar War a); case (getEquiv Ar a);
 auto with stalmarck.
intros x; case x; auto with stalmarck.
intros b; case b; intros H'; elim H'; auto with stalmarck.
intros r l b; case b; intros H'; elim H'; auto with stalmarck.
Qed.

(* Given an element of rZ compute its equivalent class *)

Definition getEquivList (Ar : rArray vM) (a : rZ) : 
  list rZ :=
  match a with
  | rZPlus a' =>
      match getEquiv Ar a' with
      | (L, true) => map rZComp L
      | (L, false) => L
      end
  | rZMinus a' =>
      match getEquiv Ar a' with
      | (L, true) => L
      | (L, false) => map rZComp L
      end
  end.

Theorem inMapComp :
 forall (a : rZ) (L : list rZ), In (rZComp a) (map rZComp L) -> In a L.
intros a L; elim L; simpl in |- *; auto with stalmarck.
intros a0 l H' H'0; Elimc H'0; auto with stalmarck.
left; apply rZCompEq; auto with stalmarck.
Qed.

Theorem getEquivListProp1 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a c : rZ),
 In c (getEquivList Ar a) <-> evalZ Ar c = evalZ Ar a.
intros Ar War a; unfold getEquivList in |- *; case a; intros a';
 generalize (getEquivProp1 Ar War a'); generalize (getEquivProp2 Ar War a');
 case (getEquiv Ar a'); simpl in |- *; auto with stalmarck; intros l b; 
 case b; auto with stalmarck.
intros H' H'0 c.
lapply (H'0 c); [ intros H'1; red in H'1 | idtac ]; auto with stalmarck.
Elimc H'1; intros H'1 H'2.
red in |- *; split; intros H'3; auto with stalmarck.
apply H'1; auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
rewrite (rZCompInvol c); apply in_map; auto with stalmarck.
intros H' H'0 c.
lapply (H'0 (rZComp c));
 [ rewrite <- rZCompInvol; intros H'1; red in H'1 | idtac ]; 
 auto with stalmarck.
Elimc H'1; intros H'1 H'2.
red in |- *; split; intros H'3; auto with stalmarck.
rewrite <- H'1; auto with stalmarck.
rewrite (evalZComp Ar c); auto with stalmarck.
apply H'2; auto with stalmarck.
rewrite (evalZComp Ar c); auto with stalmarck.
rewrite H'3; auto with stalmarck.
intros H' H'0 c.
lapply (H' (rZComp c)); [ intros H'1; red in H'1 | idtac ]; auto with stalmarck.
Elimc H'1; intros H'1 H'2.
red in |- *; split; intros H'3; auto with stalmarck.
rewrite <- H'1; auto with stalmarck.
rewrite (evalZComp Ar c); auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
rewrite (rZCompInvol c); apply in_map; auto with stalmarck.
apply H'2; auto with stalmarck.
rewrite (evalZComp Ar c); auto with stalmarck.
rewrite H'3; auto with stalmarck.
Qed.

Theorem getEquivListProp2 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rZ),
 OlistRz (getEquivList Ar a).
intros Ar War a; unfold getEquivList in |- *; case a; intros a';
 generalize (getEquivProp3 Ar War a'); case (getEquiv Ar a'); 
 simpl in |- *; auto with stalmarck; intros l b; case b; auto with stalmarck; intros H'; 
 red in |- *; apply Olistf with (eqA := eqRz); auto with stalmarck; 
 exact rZltEqComp.
Qed.

Theorem getEquivListProp3 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rZ),
 In a (getEquivList Ar a).
intros Ar War a.
case (getEquivListProp1 _ War a a); auto with stalmarck.
Qed.

Theorem getEquivListProp4 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (S : State),
 rArrayState Ar S ->
 forall a b : rZ, eqStateRz S a b <-> getEquivList Ar a = getEquivList Ar b.
intros Ar War S Sar a b; red in |- *; split; intros H'1; auto with stalmarck.
cut (EqL _ (eq (A:=rZ)) (getEquivList Ar a) (getEquivList Ar b)).
intros H'; elim H'; simpl in |- *; auto with stalmarck.
intros a0 b0 L1 L2 H'0 H'2 H'3; rewrite H'0; rewrite H'3; auto with stalmarck.
apply EqLOlist with (ltA := rZlt); try (red in |- *; auto with stalmarck; fail); auto with stalmarck.
intros a0 b0 H'; red in |- *; intros H'0; absurd (rZlt a0 b0); auto with stalmarck;
 rewrite H'0; auto with stalmarck.
intros a0 b0 c d H' H'0 H'2; rewrite <- H'0; rewrite <- H'2; auto with stalmarck.
apply getEquivListProp2; auto with stalmarck.
apply getEquivListProp2; auto with stalmarck.
apply InclEqDef; auto with stalmarck.
intros a0 H'; apply inImpInEq; auto with stalmarck.
red in |- *; auto with stalmarck.
case (getEquivListProp1 Ar War b a0).
intros H'0 H'2; apply H'2; auto with stalmarck.
apply trans_equal with (evalZ Ar a).
case (getEquivListProp1 Ar War a a0).
intros H'3 H'4; apply H'3.
elim H'; simpl in |- *; auto with stalmarck.
apply rArrayStateDef1 with (S := S); auto with stalmarck.
apply InclEqDef; auto with stalmarck.
intros a0 H'; apply inImpInEq; auto with stalmarck.
red in |- *; auto with stalmarck.
case (getEquivListProp1 Ar War a a0).
intros H'0 H'2; apply H'2.
apply trans_equal with (evalZ Ar b).
case (getEquivListProp1 Ar War b a0).
intros H'3 H'4; apply H'3.
elim H'; simpl in |- *; auto with stalmarck.
apply rArrayStateDef1 with (S := S); auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar); auto with stalmarck.
case (getEquivListProp1 Ar War b a); auto with stalmarck.
intros H' H'0; apply H'.
rewrite <- H'1.
apply getEquivListProp3; auto with stalmarck.
Qed.

Definition getMinId :=
  getMin _ rZlt eqRz rZltEDec (eq (A:=rZ)) (fun (a b : rZ) _ => rZDec a b).

Theorem getMinIdSym :
 forall L1 L2 : list rZ,
 OlistRz L1 -> OlistRz L2 -> getMinId L1 L2 = getMinId L2 L1.
intros L1 L2 H' H'0; CaseEq (getMinId L1 L2).
CaseEq (getMinId L2 L1).
intros x H'1 x0 H'2.
case (rZltEDec x0 x); auto with stalmarck.
intros H'3; case H'3.
intros H'4.
absurd (x0 = x0); auto with stalmarck.
unfold getMinId in H'1; apply getMinMin with (10 := H'1); auto with stalmarck.
intros a b H'5; rewrite H'5; auto with stalmarck.
unfold getMinId in H'2; case getMinComp with (4 := H'2); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto with stalmarck.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
intros H'4.
absurd (x = x); auto with stalmarck.
unfold getMinId in H'2; apply getMinMin with (10 := H'2); auto with stalmarck.
intros a b H'5; rewrite H'5; auto with stalmarck.
unfold getMinId in H'1; case getMinComp with (4 := H'1); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto with stalmarck.
unfold getMinId in H'1; apply geMinIn with (4 := H'1); auto with stalmarck.
intros H'3; rewrite (OlistIn _ rZlt eqRz) with (L := L1) (7 := H'3); auto with stalmarck.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
unfold getMinId in H'1; case getMinComp with (4 := H'1); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto with stalmarck.
intros H'1 x H'2; absurd (x = x); auto with stalmarck.
unfold getMinId in H'1; apply getMinNone with (8 := H'1); auto with stalmarck.
intros a b H'3; rewrite H'3; auto with stalmarck.
unfold getMinId in H'2; case getMinComp with (4 := H'2); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto with stalmarck.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
intros H'1; CaseEq (getMinId L2 L1); auto with stalmarck.
intros x H'2; absurd (x = x); auto with stalmarck.
unfold getMinId in H'1; apply getMinNone with (8 := H'1); auto with stalmarck.
intros a b H'3; rewrite H'3; auto with stalmarck.
unfold getMinId in H'2; case getMinComp with (4 := H'2); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto with stalmarck.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
Qed.

Definition getMinInv :=
  getMin _ rZlt eqRz rZltEDec (fun a b : rZ => a = rZComp b)
    (fun (a b : rZ) (_ : eqRz a b) => rZDec a (rZComp b)).

Theorem getMinInvSym :
 forall L1 L2 : list rZ,
 OlistRz L1 ->
 OlistRz L2 ->
 match getMinInv L1 L2 with
 | None => getMinInv L2 L1 = None
 | Some a => getMinInv L2 L1 = Some (rZComp a)
 end.
intros L1 L2 H' H'0; CaseEq (getMinInv L1 L2).
CaseEq (getMinInv L2 L1).
intros x H'1 x0 H'2.
case (rZltEDec x0 x); auto with stalmarck.
intros H'3; case H'3.
intros H'4.
absurd (rZComp x0 = rZComp x0); auto with stalmarck.
unfold getMinInv in H'1; apply getMinMin with (10 := H'1); auto with stalmarck.
intros a b H'5; rewrite H'5; auto with stalmarck.
apply rZltEqComp with (a := x0) (b := x); auto with stalmarck.
unfold getMinInv in H'2; case getMinComp with (4 := H'2); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto with stalmarck.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
intros H'4.
absurd (rZComp x = rZComp x); auto with stalmarck.
unfold getMinInv in H'2; apply getMinMin with (10 := H'2); auto with stalmarck.
intros a b H'5; rewrite H'5; auto with stalmarck.
apply rZltEqComp with (a := x) (b := x0); auto with stalmarck.
unfold getMinInv in H'1; case getMinComp with (4 := H'1); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto with stalmarck.
unfold getMinInv in H'1; apply geMinIn with (4 := H'1); auto with stalmarck.
intros H'3;
 rewrite (OlistIn _ rZlt eqRz) with (L := L1) (a := x0) (b := rZComp x); 
 auto using f_equal with stalmarck.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
unfold getMinInv in H'1; case getMinComp with (4 := H'1); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto with stalmarck.
apply eqrZTrans with (1 := H'3); auto with stalmarck.
intros H'1 x H'2; absurd (rZComp x = rZComp x); auto with stalmarck.
unfold getMinInv in H'1; apply getMinNone with (8 := H'1); auto with stalmarck.
intros a b H'3; rewrite H'3; auto with stalmarck.
unfold getMinInv in H'2; case getMinComp with (4 := H'2); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto with stalmarck.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
intros H'1; CaseEq (getMinInv L2 L1); auto with stalmarck.
intros x H'2; absurd (rZComp x = rZComp x); auto with stalmarck.
unfold getMinInv in H'1; apply getMinNone with (8 := H'1); auto with stalmarck.
intros a b H'3; rewrite H'3; auto with stalmarck.
unfold getMinInv in H'2; case getMinComp with (4 := H'2); auto with stalmarck.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto with stalmarck.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto with stalmarck.
Qed.

(* Given two arrays and a rNat find the smallest element that are in
    both equivalent classes of a *)

Definition getEquivMin (Ar1 Ar2 : rArray vM) (a : rNat) : rZ :=
  match getEquiv Ar1 a with
  | (L1, true) =>
      match getEquiv Ar2 a with
      | (L2, true) =>
          match getMinId L1 L2 with
          | Some b => rZComp b
          | None => rZPlus zero
          end
      | (L2, false) =>
          match getMinInv L1 L2 with
          | Some b => rZComp b
          | None => rZPlus zero
          end
      end
  | (L1, false) =>
      match getEquiv Ar2 a with
      | (L2, true) =>
          match getMinInv L1 L2 with
          | Some b => b
          | None => rZPlus zero
          end
      | (L2, false) =>
          match getMinId L1 L2 with
          | Some b => b
          | None => rZPlus zero
          end
      end
  end.

Theorem getEquivMinSym :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rNat),
 getEquivMin Ar1 Ar2 a = getEquivMin Ar2 Ar1 a.
intros Ar1 Ar2 War1 War2 a; unfold getEquivMin in |- *;
 generalize (getEquivProp3 Ar1 War1 a); generalize (getEquivProp3 Ar2 War2 a);
 case (getEquiv Ar1 a); case (getEquiv Ar2 a); simpl in |- *.
intros L1 b1 L2 b2 OL1 OL2; case b1; case b2; auto with stalmarck;
 try rewrite (getMinIdSym L1 L2); auto with stalmarck; generalize (getMinInvSym L1 L2); 
 auto with stalmarck; case (getMinInv L1 L2); auto with stalmarck; case (getMinInv L2 L1); 
 auto with stalmarck; intros x1 x2 Hx1 || intros x1 Hx1; auto with stalmarck; generalize (Hx1 OL1 OL2);
 intros Inv0; inversion Inv0; auto with stalmarck.
Qed.

Theorem rZCompInvolList : forall L : list rZ, L = map rZComp (map rZComp L).
intros L; elim L; simpl in |- *; auto with stalmarck.
intros a l H'; rewrite <- H'; auto with datatypes stalmarck.
rewrite <- rZCompInvol; auto with stalmarck.
Qed.

Theorem getEquivMinIn1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rNat),
 In (getEquivMin Ar1 Ar2 a) (getEquivList Ar1 (rZPlus a)).
intros Ar1 Ar2 War1 War2 a;
 generalize (getEquivListProp2 Ar1 War1 (rZPlus a));
 generalize (getEquivListProp3 Ar1 War1 (rZPlus a));
 generalize (getEquivListProp2 Ar2 War2 (rZPlus a));
 generalize (getEquivListProp3 Ar2 War2 (rZPlus a)); 
 simpl in |- *; unfold getEquivMin in |- *; case (getEquiv Ar1 a); 
 intros l b; case b; case (getEquiv Ar2 a); intros l0 b0; 
 case b0; auto with stalmarck.
CaseEq (getMinId l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3; apply in_map; auto with stalmarck.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZMinus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
apply inMapComp; auto with stalmarck.
CaseEq (getMinInv l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3; apply in_map; auto with stalmarck.
unfold getMinInv in H'; apply geMinIn with (4 := H'); auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZPlus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
CaseEq (getMinInv l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinInv in H'; apply geMinIn with (4 := H'); auto with stalmarck.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZMinus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
CaseEq (getMinId l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZPlus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
Qed.

Theorem getEquivMinIn2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rNat),
 In (getEquivMin Ar1 Ar2 a) (getEquivList Ar2 (rZPlus a)).
intros Ar1 Ar2 War1 War2 a;
 generalize (getEquivListProp2 Ar1 War1 (rZPlus a));
 generalize (getEquivListProp3 Ar1 War1 (rZPlus a));
 generalize (getEquivListProp2 Ar2 War2 (rZPlus a));
 generalize (getEquivListProp3 Ar2 War2 (rZPlus a)); 
 simpl in |- *; unfold getEquivMin in |- *; case (getEquiv Ar1 a); 
 intros l b; case b; case (getEquiv Ar2 a); intros l0 b0; 
 case b0; auto with stalmarck.
CaseEq (getMinId l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3; apply in_map; auto with stalmarck.
unfold getMinId in H'; case getMinComp with (4 := H'); auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZMinus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
apply inMapComp; auto with stalmarck.
CaseEq (getMinInv l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinInv in H'; case getMinComp with (4 := H'); auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5; rewrite rZCompInv; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZPlus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
CaseEq (getMinInv l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinInv in H'; case getMinComp with (4 := H'); auto with stalmarck.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5.
apply inMapComp; rewrite <- (rZCompInvolList l0); rewrite rZCompInv; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZMinus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
CaseEq (getMinId l l0); auto with stalmarck.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinId in H'; case getMinComp with (4 := H'); auto with stalmarck.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZPlus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
Qed.

Theorem getEquivMinMin :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rNat) (c : rZ),
 rZlt c (getEquivMin Ar1 Ar2 a) ->
 ~ (In c (getEquivList Ar1 (rZPlus a)) /\ In c (getEquivList Ar2 (rZPlus a))).
intros Ar1 Ar2 War1 War2 a;
 generalize (getEquivListProp2 Ar1 War1 (rZPlus a));
 generalize (getEquivListProp3 Ar1 War1 (rZPlus a));
 generalize (getEquivListProp2 Ar2 War2 (rZPlus a));
 generalize (getEquivListProp3 Ar2 War2 (rZPlus a)); 
 simpl in |- *; unfold getEquivMin in |- *; case (getEquiv Ar1 a); 
 intros l b; case b; case (getEquiv Ar2 a); intros l0 b0; 
 case b0; auto with stalmarck.
CaseEq (getMinId l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6.
absurd (rZComp c = rZComp c); auto with stalmarck.
unfold getMinId in H'; apply getMinMin with (10 := H'); auto with stalmarck.
intros a0 b1 H'7; rewrite H'7; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply rZltEqComp with (a := c) (b := rZComp x); auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZMinus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
apply inMapComp; auto with stalmarck.
CaseEq (getMinInv l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6; auto with stalmarck.
absurd (rZComp c = rZComp c); auto with stalmarck.
unfold getMinInv in H'; apply getMinMin with (10 := H'); auto with stalmarck.
intros a0 b1 H'7; rewrite H'7; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply rZltEqComp with (a := c) (b := rZComp x); auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZPlus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
CaseEq (getMinInv l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6.
absurd (c = rZComp (rZComp c)); auto with stalmarck.
unfold getMinInv in H'; apply getMinMin with (10 := H'); auto with stalmarck.
intros a0 b1 H'7; rewrite H'7; auto with stalmarck.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZMinus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
rewrite (rZCompInvolList l0); auto with stalmarck.
apply Olistf with (eqA := eqRz); auto with stalmarck.
try exact rZltEqComp.
apply inMapComp; auto with stalmarck.
CaseEq (getMinId l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6.
absurd (c = c); auto with stalmarck.
unfold getMinId in H'; apply getMinMin with (10 := H'); auto with stalmarck.
intros a0 b1 H'7; rewrite H'7; auto with stalmarck.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZPlus a); 
 auto with stalmarck.
intros a0 b1 H'4; rewrite H'4; auto with stalmarck.
Qed.

Theorem getEquivMinEq1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar1 S ->
 forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a.
apply rArrayStateDef2 with (Ar := Ar1); auto with stalmarck.
case (getEquivListProp1 Ar1 War1 (rZPlus a) (getEquivMin Ar1 Ar2 a)).
intros H'0; rewrite H'0; auto with stalmarck.
apply getEquivMinIn1; auto with stalmarck.
Qed.

Theorem getEquivMinEq2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar2 S ->
 forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a.
apply rArrayStateDef2 with (Ar := Ar2); auto with stalmarck.
case (getEquivListProp1 Ar2 War2 (rZPlus a) (getEquivMin Ar1 Ar2 a)).
intros H'0; rewrite H'0; auto with stalmarck.
rewrite getEquivMinSym; auto with stalmarck.
apply getEquivMinIn1; auto with stalmarck.
Qed.

Theorem getEquivMinMinEq :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S1 S2 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 forall (a : rNat) (c : rZ),
 rZlt c (getEquivMin Ar1 Ar2 a) ->
 ~ (eqStateRz S1 (rZPlus a) c /\ eqStateRz S2 (rZPlus a) c).
intros Ar1 Ar2 War1 War2 S1 S2 H' H'0 a c H'1; red in |- *; intros H'2;
 Elimc H'2; intros H'2 H'3; auto with stalmarck.
absurd
 (In c (getEquivList Ar1 (rZPlus a)) /\ In c (getEquivList Ar2 (rZPlus a)));
 auto with stalmarck.
apply getEquivMinMin; auto with stalmarck.
split; auto with stalmarck.
case (getEquivListProp1 Ar1 War1 (rZPlus a) c).
intros H'4 H'5; apply H'5; auto with stalmarck.
apply rArrayStateDef1 with (S := S1); auto with stalmarck.
case (getEquivListProp1 Ar2 War2 (rZPlus a) c).
intros H'4 H'5; apply H'5; auto with stalmarck.
apply rArrayStateDef1 with (S := S2); auto with stalmarck.
Qed.

Theorem eqNotltRz : forall a b : rZ, rZlt a b -> a <> b.
intros a b H'; red in |- *; intros H'0; absurd (rZlt a b); auto with stalmarck.
rewrite H'0; auto with stalmarck.
Qed.
Local Hint Resolve eqNotltRz : stalmarck.

Theorem evalZMin :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (S : State),
 rArrayState Ar S ->
 forall a c : rZ, rZlt c (evalZ Ar a) -> ~ eqStateRz S a c.
intros Ar War S H'0 a c H'1; red in |- *; intros H'2.
absurd (evalZ Ar c = evalZ Ar a); auto with stalmarck.
generalize H'1 H'2; clear H'1 H'2.
case c; case a; simpl in |- *; intros a' c'; unfold evalN in |- *;
 CaseEq (rArrayGet vM Ar a'); CaseEq (rArrayGet vM Ar c'); 
 auto with stalmarck; intros r H' r0 H'1 H'2 H'3; red in |- *; intros H'4;
 (absurd (rVlt r c'); [ idtac | apply wfPd with (Ar := Ar) ]); 
 auto with stalmarck; try (rewrite H'4; unfold rVlt in |- *; apply rltAntiSym; auto with stalmarck);
 rewrite (rZCompInvol r); rewrite H'4; unfold rVlt in |- *; 
 apply rltAntiSym; generalize H'2; case r0; simpl in |- *; 
 auto with stalmarck.
apply rArrayStateDef1 with (S := S); auto with stalmarck.
Qed.

Theorem getEquivIdR :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S1 S2 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 forall a : rNat,
 eqStateRz S2 (rZPlus a) (evalZ Ar1 (rZPlus a)) ->
 getEquivMin Ar1 Ar2 a = evalZ Ar1 (rZPlus a).
intros Ar1 Ar2 War1 War2 S1 S2 Sar1 Sar2 a H'0;
 case (rZltEDec (getEquivMin Ar1 Ar2 a) (evalZ Ar1 (rZPlus a))); 
 intros s; [ Casec s; intros s | idtac ].
case evalZMin with (3 := s) (S := S1); auto with stalmarck.
apply getEquivMinEq1; auto with stalmarck.
case getEquivMinMinEq with (5 := s) (S1 := S1) (S2 := S2); auto with stalmarck; split; auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar1); auto with stalmarck.
rewrite evalZInv; auto with stalmarck.
case (eqRzElim _ _ s); auto with stalmarck.
intros H'1; absurd (contradictory S1); auto with stalmarck.
red in |- *; intros H'; elim H'.
intros x H'2; absurd (evalZ Ar1 x = evalZ Ar1 (rZComp x)).
rewrite evalZComp; auto with stalmarck.
apply rArrayStateDef1 with (S := S1); auto with stalmarck.
red in |- *; auto with stalmarck.
exists (rZPlus a); auto with stalmarck.
apply eqStateRzTrans with (b := evalZ Ar1 (rZPlus a)); auto with stalmarck.
apply rArrayStateDef2 with (Ar := Ar1); auto with stalmarck.
rewrite evalZInv; auto with stalmarck.
apply eqStateInvInv; auto with stalmarck.
rewrite <- H'1; auto with stalmarck.
rewrite <- rZCompInvol; auto with stalmarck.
apply eqStateRzSym.
apply getEquivMinEq1; auto with stalmarck.
Qed.

Theorem getEquivIdL :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S1 S2 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 forall a : rNat,
 eqStateRz S1 (rZPlus a) (evalZ Ar2 (rZPlus a)) ->
 getEquivMin Ar1 Ar2 a = evalZ Ar2 (rZPlus a).
intros Ar1 Ar2 War1 War2 S1 S2 H' H'0 a H'1.
rewrite getEquivMinSym; auto with stalmarck.
apply getEquivIdR with (S1 := S2) (S2 := S1); auto with stalmarck.
Qed.

Theorem getMinInvInd :
 forall L1 L2 : list rZ,
 OlistRz L1 -> OlistRz L2 -> getMinInv L1 (map rZComp L2) = getMinId L1 L2.
intros L1 L2 Ol1 Ol2; auto with stalmarck.
cut (OlistRz (map rZComp L2));
 [ intros Ol2'
 | red in |- *; apply Olistf with (eqA := eqRz); auto with stalmarck; exact rZltEqComp ].
CaseEq (getMinInv L1 (map rZComp L2)); auto with stalmarck.
CaseEq (getMinId L1 L2); auto with stalmarck.
intros x H' x0 H'0.
case (rZltEDec x0 x); intros s; [ Casec s; intros s | idtac ].
absurd (x0 = x0); auto with stalmarck.
unfold getMinId in H'; apply getMinMin with (10 := H'); auto with stalmarck.
intros a b H'1; rewrite H'1; auto with stalmarck.
unfold getMinInv in H'0; apply geMinIn with (4 := H'0); auto with stalmarck.
unfold getMinInv in H'0; elim getMinComp with (4 := H'0); auto with stalmarck.
intros x1 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
absurd (x = rZComp (rZComp x)); auto with stalmarck.
unfold getMinInv in H'0; apply getMinMin with (10 := H'0); auto with stalmarck.
intros a b H'1; rewrite H'1; auto with stalmarck.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto with stalmarck.
apply in_map; auto with stalmarck.
unfold getMinId in H'; elim getMinComp with (4 := H'); auto with stalmarck.
intros x1 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1; auto with stalmarck.
rewrite (OlistIn _ rZlt eqRz) with (a := x0) (b := x) (L := L1); auto with stalmarck.
unfold getMinInv in H'0; apply geMinIn with (4 := H'0); auto with stalmarck.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto with stalmarck.
intros H' x H'0; absurd (x = x); auto with stalmarck.
unfold getMinId in H'; apply getMinNone with (8 := H'); auto with stalmarck.
intros a b H'1; rewrite H'1; auto with stalmarck.
unfold getMinInv in H'0; apply geMinIn with (4 := H'0); auto with stalmarck.
apply inMapComp; auto with stalmarck.
unfold getMinInv in H'0; elim getMinComp with (4 := H'0); auto with stalmarck.
intros x0 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1; rewrite <- rZCompInvol;
 auto with stalmarck.
CaseEq (getMinId L1 L2); auto with stalmarck.
intros x H' H'0.
absurd (x = rZComp (rZComp x)); auto with stalmarck.
unfold getMinInv in H'0; apply getMinNone with (8 := H'0); auto with stalmarck.
intros a b H'1; rewrite H'1; auto with stalmarck.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto with stalmarck.
apply in_map; auto with stalmarck.
unfold getMinId in H'; elim getMinComp with (4 := H'); auto with stalmarck.
intros x0 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1; auto with stalmarck.
Qed.

(* List the function getEquivMin to rZ *)

Definition getRzMin (Ar1 Ar2 : rArray vM) (a : rZ) : rZ :=
  match a with
  | rZPlus a' => getEquivMin Ar1 Ar2 a'
  | rZMinus a' => rZComp (getEquivMin Ar1 Ar2 a')
  end.

Theorem getRzMinSym :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rZ),
 getRzMin Ar1 Ar2 a = getRzMin Ar2 Ar1 a.
intros Ar1 Ar2 War1 War2 a; case a; simpl in |- *; intros a';
 rewrite getEquivMinSym; auto with stalmarck.
Qed.

Theorem getRzMinIn1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rZ),
 In (getRzMin Ar1 Ar2 a) (getEquivList Ar1 a).
intros Ar1 Ar2 War1 War2 a; case a; intros a';
 generalize (getEquivMinIn1 Ar1 Ar2 War1 War2 a'); 
 simpl in |- *; auto with stalmarck.
case (getEquiv Ar1 a'); auto with stalmarck.
intros l b; case b; intros H'; auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
apply in_map; auto with stalmarck.
Qed.

Theorem getRzMinIn2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rZ),
 In (getRzMin Ar1 Ar2 a) (getEquivList Ar2 a).
intros Ar1 Ar2 War1 War2 a; case a; intros a';
 generalize (getEquivMinIn2 Ar1 Ar2 War1 War2 a'); 
 simpl in |- *; auto with stalmarck.
case (getEquiv Ar2 a'); auto with stalmarck.
intros l b; case b; intros H'; auto with stalmarck.
apply inMapComp; rewrite <- rZCompInvol; auto with stalmarck.
apply in_map; auto with stalmarck.
Qed.

Theorem getRzMinMin :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a c : rZ),
 rZlt c (getRzMin Ar1 Ar2 a) ->
 ~ (In c (getEquivList Ar1 a) /\ In c (getEquivList Ar2 a)).
intros Ar1 Ar2 War1 War2 a c; case a; intros a';
 generalize (getEquivMinMin Ar1 Ar2 War1 War2 a'); 
 simpl in |- *; auto with stalmarck.
case (getEquiv Ar1 a'); case (getEquiv Ar2 a'); intros l b l0 b0; case b;
 case b0; simpl in |- *; intros H' H'0; red in |- *; 
 intros H'1; Elimc H'1; intros H'1 H'2;
 (case (H' (rZComp c)); [ apply rZltEqComp with (1 := H'0); auto with stalmarck | idtac ]);
 split; try apply in_map; auto with stalmarck; apply inMapComp; rewrite <- rZCompInvol; 
 auto with stalmarck.
Qed.

Theorem getRzMinEq1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar1 S -> forall a : rZ, eqStateRz S a (getRzMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a; case a; intros a';
 generalize (getEquivMinEq1 Ar1 Ar2 War1 War2 S H' a'); 
 simpl in |- *; auto with stalmarck.
Qed.

Theorem getRzMinEq2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar2 S -> forall a : rZ, eqStateRz S a (getRzMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a; case a; intros a';
 generalize (getEquivMinEq2 Ar1 Ar2 War1 War2 S H' a'); 
 simpl in |- *; auto with stalmarck.
Qed.

Theorem getRzMinMinEq :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S1 S2 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 forall a c : rZ,
 rZlt c (getRzMin Ar1 Ar2 a) -> ~ (eqStateRz S1 a c /\ eqStateRz S2 a c).
intros Ar1 Ar2 War1 War2 S1 S2 H' H'0 a c; case a; intros a';
 generalize (getEquivMinMinEq Ar1 Ar2 War1 War2 S1 S2 H' H'0 a').
auto with stalmarck.
intros H'1 H'2; red in |- *; intros H'3; Elimc H'3; intros H'3 H'4.
case (H'1 (rZComp c));
 [ apply rZltEqComp with (1 := H'2); simpl in |- *; auto with stalmarck | idtac ]; 
 split; auto with stalmarck.
Qed.

Theorem getRzMinUnique :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S1 S2 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 forall a b : rZ,
 eqStateRz S1 a b ->
 eqStateRz S2 a b -> getRzMin Ar1 Ar2 a = getRzMin Ar1 Ar2 b.
intros Ar1 Ar2 War1 War2 S1 S2 H' H'0 a b H'1 H'2.
cut (getEquivList Ar1 a = getEquivList Ar1 b);
 [ intros Eq1 | case (getEquivListProp4 Ar1 War1 S1 H' a b) ]; 
 auto with stalmarck.
cut (getEquivList Ar2 a = getEquivList Ar2 b);
 [ intros Eq2 | case (getEquivListProp4 Ar2 War2 S2 H'0 a b) ]; 
 auto with stalmarck.
case (rZltEDec (getRzMin Ar1 Ar2 a) (getRzMin Ar1 Ar2 b)); intros s;
 [ Casec s; intros s | idtac ].
case getRzMinMinEq with (5 := s) (S1 := S1) (S2 := S2); auto with stalmarck; split; auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
apply getRzMinEq1; auto with stalmarck.
apply eqStateRzTrans with (b := a); auto with stalmarck.
apply getRzMinEq2; auto with stalmarck.
case getRzMinMinEq with (5 := s) (S1 := S1) (S2 := S2); auto with stalmarck; split; auto with stalmarck.
apply eqStateRzTrans with (b := b); auto with stalmarck.
apply getRzMinEq1; auto with stalmarck.
apply eqStateRzTrans with (b := b); auto with stalmarck.
apply getRzMinEq2; auto with stalmarck.
apply OlistIn with (ltA := rZlt) (eqA := eqRz) (L := getEquivList Ar1 b);
 auto with stalmarck.
rewrite <- Eq1.
apply getRzMinIn1; auto with stalmarck.
apply getRzMinIn1; auto with stalmarck.
apply getEquivListProp2; auto with stalmarck.
Qed.

Theorem forallgetEquivgetRzMin :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 (forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a)) ->
 forall a : rZ, eqStateRz S a (getRzMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a; case a; intros a'; simpl in |- *; auto with stalmarck.
apply eqStateRzInv with (1 := H' a'); auto with stalmarck.
Qed.
(* here where we wanted to arrive a state S that is included is S1 and S2
   and for every a, a is in relation with the intersection of the equivalent classes,
  then S is the intersection *)

Theorem getEquivInter :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S S1 S2 : State),
 rArrayState Ar1 S1 ->
 rArrayState Ar2 S2 ->
 (forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a)) ->
 inclState (interState S1 S2) S.
intros Ar1 Ar2 War1 War2 S S1 S2 H' H'0 H'1.
red in |- *; auto with stalmarck.
intros i j H'2.
cut (eqStateRz S1 i j); [ intros Em1 | apply eqStateIncl with (2 := H'2) ];
 auto with stalmarck.
cut (eqStateRz S2 i j); [ intros Em2 | apply eqStateIncl with (2 := H'2) ];
 auto with stalmarck.
case (rZDec i j); intros Eqij; auto with stalmarck.
rewrite Eqij; auto with stalmarck.
apply eqStateRzTrans with (b := getRzMin Ar1 Ar2 i).
apply forallgetEquivgetRzMin; auto with stalmarck.
rewrite (getRzMinUnique Ar1 Ar2 War1 War2 S1 S2 H' H'0 i j); auto with stalmarck.
apply eqStateRzSym; auto with stalmarck.
apply forallgetEquivgetRzMin; auto with stalmarck.
Qed.
End inter.
