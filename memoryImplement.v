
(****************************************************************************
                                                                           
          Stalmarck  :   memoryImplement                                   
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Define how to perform the addition of an equation*)
Require Export state.
Require Export restrictState.
Require Export ltState.
Require Export wfArray.
Require Export addArray.

(*Definition of well formed array and some properties *)
Section Deval.

(* Ordered list for list on  rZ *)

Definition OlistRz := Olist rZ rZlt.

(* Disjoint list for list on rZ *)

Definition DisjointRz := Disjoint rZ eqRz.

(* To be in a list for rZ with no sign consideration  *)

Definition InRz := InEq rZ eqRz.
Variable Ar : rArray vM.
Hypothesis War : wellFormedArray Ar.

(* Given a rNat n returns the smaller rZ p such that +a = p *)

Definition evalN (v : rNat) : rZ :=
  match rArrayGet _ Ar v with
  | ref p => p
  | class _ => rZPlus v
  end.

(* Lift evalMnat to rZ *)

Definition evalZ (v : rZ) : rZ := samePolRz v (evalN (valRz v)).

Theorem EqrZComp : forall a b : rZ, a = b -> rZComp a = rZComp b.
intros a b H'; rewrite H'; auto.
Qed.
Hint Resolve EqrZComp.
(* We can't be smaller than zero *)

Theorem notrltzero : forall r : rZ, ~ rVlt r zero.
intros r; red in |- *; intros H'; absurd (rlt (valRz r) (valRz r)); auto.
apply rltTransRnext2 with (m := zero); auto.
Qed.
Hint Resolve notrltzero.
(* True evaluate to true *)

Theorem evalZTrue : evalZ rZTrue = rZTrue.
simpl in |- *; unfold evalN in |- *.
generalize (fun s : rZ => wfPd _ War zero s); case (rArrayGet vM Ar zero);
 auto.
intros r H'; absurd (rVlt r zero); auto.
Qed.
(* False evaluate to false *)

Theorem evalZFalse : evalZ rZFalse = rZFalse.
simpl in |- *; unfold evalN in |- *.
generalize (fun s : rZ => wfPd _ War zero s); case (rArrayGet vM Ar zero);
 auto.
intros r H'; absurd (rVlt r zero); auto.
Qed.
(* Evaluation is compatible with the complement *)

Theorem evalZComp : forall v : rZ, evalZ (rZComp v) = rZComp (evalZ v).
intros v; case v; simpl in |- *; auto.
Qed.
(* Evaluate an element returns something smaller or equal *)

Theorem evalZltOr : forall v : rZ, evalZ v = v \/ rZlt (evalZ v) v.
intros v; case v; simpl in |- *; auto; intros a; unfold evalN in |- *;
 generalize (fun s : rZ => wfPd _ War a s); case (rArrayGet _ Ar a);
 intros r H'; auto; right.
lapply (H' r); auto.
apply rZltEqComp with (a := r) (b := rZMinus a); auto.
lapply (H' r); auto.
Qed.
(* The result of an evaluation evaluates to itself *)

Theorem evalZInv : forall v : rZ, evalZ (evalZ v) = evalZ v.
intros v; case v; intros a; simpl in |- *; unfold evalN in |- *;
 CaseEq (rArrayGet _ Ar a); simpl in |- *; auto.
intros r; case r; simpl in |- *; intros r0 H'; unfold evalN in |- *;
 CaseEq (rArrayGet _ Ar r0); auto; intros r1 H'1; Contradict H'1;
 apply wfPcr with (2 := H'); auto.
intros l H'; unfold evalN in |- *; rewrite H'; auto.
intros r; case r; simpl in |- *; intros r0 H'; unfold evalN in |- *;
 CaseEq (rArrayGet _ Ar r0); auto; intros r1 H'1; Contradict H'1;
 apply wfPcr with (2 := H'); auto.
intros l H'; unfold evalN in |- *; rewrite H'; auto.
Qed.
(* Every element smaller than the evaluation is not in the same equivalent class *)

Theorem evalZMin :
 forall (a : rNat) (b c : rZ), evalN a = b -> rZlt c b -> evalN a <> evalZ c.
intros a b c H' H'0; Contradict H'0.
rewrite <- H'; rewrite H'0.
case (evalZltOr c); auto.
intros H'1; rewrite H'1; auto.
Qed.
End Deval.
(* Relation between Get et evalN *)

Theorem rArrayGetEvalN :
 forall Ar Ar' : rArray vM,
 (forall e : rNat, rArrayGet vM Ar' e = rArrayGet vM Ar e) ->
 forall e : rNat, evalN Ar e = evalN Ar' e.
intros Ar Ar' H' e; unfold evalN in |- *.
rewrite (H' e); auto.
Qed.
(* relation between evalN et evanZ *)

Theorem evalNEvalZ :
 forall Ar Ar' : rArray vM,
 (forall e : rNat, evalN Ar e = evalN Ar' e) ->
 forall e : rZ, evalZ Ar e = evalZ Ar' e.
intros Ar Ar' H' e; case e; simpl in |- *; auto.
intros r; rewrite H'; auto.
Qed.
(* relation between get et evalZ *)

Theorem rArrayGetEvalZ :
 forall Ar Ar' : rArray vM,
 (forall e : rNat, rArrayGet vM Ar' e = rArrayGet vM Ar e) ->
 forall e : rZ, evalZ Ar e = evalZ Ar' e.
intros Ar Ar' H' e; apply evalNEvalZ; auto.
intros e'; apply rArrayGetEvalN; auto.
Qed.
Section Dprop.
Variable Ar : rArray vM.
Hypothesis War : wellFormedArray Ar.
Variable a b : rNat.
Variable pol : rZ.
Variable La Lb : list rZ.
Hypothesis rltab : rlt a b.
Hypothesis geta : rArrayGet _ Ar a = class La.
Hypothesis getb : rArrayGet _ Ar b = class Lb.
Variable S : State.
Hypothesis
  SisAr : forall c d : rZ, eqStateRz S c d <-> evalZ Ar c = evalZ Ar d.
(* We first need to prove some properties of update with respect to evalN and evalZ 

First if before evalN was giving b, it now gives a,  samePolRz is used to ensure
that the rule of sign is followed *)

Theorem updateEvalNb :
 forall c : rNat,
 valRz (evalN Ar c) = b ->
 evalN (updateArray a b pol La Lb Ar) c =
 samePolRz (evalN Ar c) (samePolRz pol (rZPlus a)).
intros c; unfold evalN in |- *.
CaseEq (rArrayGet vM Ar c); simpl in |- *.
intros r; case r; simpl in |- *.
intros r0 H' H'0; replace c with (valRz (rZPlus c)); auto.
rewrite (updateArrayInb a b pol La Lb Ar) with (c := rZPlus c); auto.
replace (rZPlus c) with (samePol (rZPlus r0) c); auto.
apply wfPcc2 with (Ar := Ar); auto.
rewrite H'0; auto.
intros r0 H' H'0; replace c with (valRz (rZMinus c)); auto.
rewrite (updateArrayInb a b pol La Lb Ar) with (c := rZMinus c); auto.
replace (rZMinus c) with (samePol (rZMinus r0) c); auto.
apply wfPcc2 with (Ar := Ar); auto.
rewrite H'0; auto.
intros l H' H'0; rewrite H'0.
rewrite (updateArrayb a b pol La Lb Ar); auto.
Qed.
(* If evalN is not b the value is not changed *)

Theorem updateEvalNO :
 forall c : rNat,
 valRz (evalN Ar c) <> b ->
 evalN (updateArray a b pol La Lb Ar) c = evalN Ar c.
intros c; unfold evalN in |- *.
case (rNatDec c a); intros Eqa; auto.
rewrite Eqa; auto; rewrite (updateArraya a b pol La Lb Ar); rewrite geta;
 auto.
case (rNatDec c b); intros Eqb; auto.
rewrite Eqb; auto; rewrite (updateArrayb a b pol La Lb Ar); auto;
 rewrite getb; simpl in |- *; intros H'; Contradict H'; 
 auto.
case (InRzDec (rZPlus c) Lb); intros InRLb; auto.
case (InEqInv (rZPlus c) Lb); auto; intros InRLb'.
replace c with (valRz (rZPlus c)); auto;
 rewrite (wfPcc1 _ War b (rZPlus c) Lb); simpl in |- *; 
 auto.
intros H'; case H'; auto.
replace c with (valRz (rZMinus c)); auto;
 rewrite (wfPcc1 _ War b (rZMinus c) Lb); simpl in |- *; 
 auto.
intros H'; case H'; auto.
rewrite (updateArrayOtherwise a b pol La Lb Ar c); auto.
Qed.
(* Equations that were valid before are still valid *)

Theorem updateEvalN2 :
 forall c d : rNat,
 evalN Ar c = evalN Ar d ->
 evalN (updateArray a b pol La Lb Ar) c =
 evalN (updateArray a b pol La Lb Ar) d.
intros c d; case (rNatDec (valRz (evalN Ar c)) b); intros Eqt.
rewrite updateEvalNb; auto.
case (rNatDec (valRz (evalN Ar d)) b); intros Eqt'.
rewrite updateEvalNb; auto.
intros H'; rewrite H'; auto.
intros H'; Contradict Eqt'; rewrite <- H'; auto.
rewrite updateEvalNO; auto.
case (rNatDec (valRz (evalN Ar d)) b); intros Eqt'.
intros H'; Contradict Eqt; rewrite H'; auto.
rewrite updateEvalNO; auto.
Qed.
(* Same as before but with complement *)

Theorem updateEvalN2Comp :
 forall c d : rNat,
 evalN Ar c = rZComp (evalN Ar d) ->
 evalN (updateArray a b pol La Lb Ar) c =
 rZComp (evalN (updateArray a b pol La Lb Ar) d).
intros c d; case (rNatDec (valRz (evalN Ar c)) b); intros Eqt.
rewrite updateEvalNb; auto.
case (rNatDec (valRz (evalN Ar d)) b); intros Eqt'.
rewrite updateEvalNb; auto.
intros H'; rewrite H'; case (evalN Ar d); auto.
intros H'; Contradict Eqt'; rewrite <- Eqt; rewrite H'; case (evalN Ar d);
 auto.
rewrite updateEvalNO; auto.
case (rNatDec (valRz (evalN Ar d)) b); intros Eqt'.
intros H'; Contradict Eqt; rewrite <- Eqt'; rewrite H'; case (evalN Ar d);
 auto.
rewrite updateEvalNO; auto.
Qed.
(* If evalZ was given b, now it gives a *)

Theorem updateEvalZb :
 forall c : rZ,
 valRz (evalZ Ar c) = b ->
 evalZ (updateArray a b pol La Lb Ar) c =
 samePolRz (evalZ Ar c) (samePolRz pol (rZPlus a)).
intros c; case c; simpl in |- *.
exact updateEvalNb.
intros r H'.
cut (forall p q : rZ, rZComp (samePolRz p q) = samePolRz (rZComp p) q);
 [ intros Eq1; rewrite <- Eq1
 | intros p q; case p; case q; simpl in |- *; auto ].
apply EqrZComp; auto.
apply updateEvalNb; auto.
rewrite <- H'; case (evalN Ar r); auto.
Qed.
(* If evalZ was not giving b, its value is unchanged *)

Theorem updateEvalZO :
 forall c : rZ,
 valRz (evalZ Ar c) <> b ->
 evalZ (updateArray a b pol La Lb Ar) c = evalZ Ar c.
intros c; case c; simpl in |- *.
exact updateEvalNO.
intros r H'; apply EqrZComp; auto.
apply updateEvalNO; auto.
Contradict H'; rewrite <- H'; case (evalN Ar r); auto.
Qed.
(* Equations for evalZ are still valid *)

Theorem updateEvalZ2 :
 forall c d : rZ,
 evalZ Ar c = evalZ Ar d ->
 evalZ (updateArray a b pol La Lb Ar) c =
 evalZ (updateArray a b pol La Lb Ar) d.
intros c d; case c; case d; simpl in |- *; intros; try apply EqrZComp;
 try apply updateEvalN2 || apply updateEvalN2Comp; 
 auto.
apply sym_equal; apply updateEvalN2Comp; auto.
generalize H; case (evalN Ar r0); case (evalN Ar r); simpl in |- *;
 intros r1 r2 H'; inversion H'; auto.
Qed.
(* Same with complement *)

Theorem updateEvalZ2Comp :
 forall c d : rZ,
 evalZ Ar c = rZComp (evalZ Ar d) ->
 evalZ (updateArray a b pol La Lb Ar) c =
 rZComp (evalZ (updateArray a b pol La Lb Ar) d).
intros c d; repeat rewrite <- evalZComp.
intros H'; apply updateEvalZ2; auto.
Qed.
(* evalN a = +/- evalN b  depending of the polarity*)

Theorem updateEvalNab :
 evalN (updateArray a b pol La Lb Ar) a =
 samePolRz pol (evalN (updateArray a b pol La Lb Ar) b).
unfold evalN in |- *; rewrite (updateArraya a b pol La Lb Ar);
 rewrite (updateArrayb a b pol La Lb Ar); auto.
case pol; auto.
Qed.
(* evalZ a = +/- evalZ b depending of the polarity *)

Theorem updateEvalZab :
 evalZ (updateArray a b pol La Lb Ar) (rZPlus a) =
 samePolRz pol (evalZ (updateArray a b pol La Lb Ar) (rZPlus b)).
simpl in |- *; auto.
exact updateEvalNab.
Qed.
(* update is correct *)

Theorem updateCorrect :
 forall c d : rZ,
 eqStateRz (addEq (rZPlus a, samePol pol b) S) c d <->
 evalZ (updateArray a b pol La Lb Ar) c =
 evalZ (updateArray a b pol La Lb Ar) d.
intros c d; split.
cut (exists S' : _, S' = addEq (rZPlus a, samePol pol b) S).
intros H'; Elimc H'; intros S' E; rewrite <- E.
intros H'; generalize E; elim H'; auto.
intros a0 b0 S0 H'0 H'1; rewrite H'1 in H'0.
simpl in H'0; case H'0.
intros H'2; inversion H'2.
rewrite updateEvalZab.
case pol; auto.
intros H'2; apply updateEvalZ2.
case (SisAr a0 b0); auto.
intros a0 b0 S0 H'0 H'1 H'2; repeat rewrite evalZComp; apply EqrZComp; auto.
intros a0 b0 S0 H'0 H'1 H'2; apply sym_equal; auto.
intros a0 b0 c0 S0 H'0 H'1 H'2 H'3 H'4; rewrite H'1; auto.
intros a0 b0 c0 S0 H'0 H'1 H'2;
 absurd
  (evalZ (updateArray a b pol La Lb Ar) a0 =
   evalZ (updateArray a b pol La Lb Ar) (rZComp a0)); 
 auto.
rewrite evalZComp; auto.
exists (addEq (rZPlus a, samePol pol b) S); auto.
case (rNatDec (valRz (evalZ Ar c)) b); intros Eqt.
rewrite updateEvalZb; auto.
case (rNatDec (valRz (evalZ Ar d)) b); intros Eqt'.
rewrite updateEvalZb; auto.
intros tmp; apply eqStateaddEq2.
case (SisAr c d); intros H' H'0; apply H'0; auto.
generalize Eqt; rewrite <- Eqt'; generalize tmp; case (evalZ Ar c);
 case (evalZ Ar d); case pol; simpl in |- *; auto; 
 intros r0 r1 r2 H0 H1; rewrite H1; try discriminate; 
 auto.
rewrite updateEvalZO; auto.
intros H0; apply eqStateRzTrans with (b := samePolRz (evalZ Ar c) (rZPlus b)).
apply eqStateaddEq2.
case (SisAr c (samePolRz (evalZ Ar c) (rZPlus b))); intros H' H'0; apply H'0;
 auto.
rewrite <- Eqt; generalize (evalZInv Ar War c); case (evalZ Ar c);
 simpl in |- *; auto.
apply
 eqStateRzTrans with (b := samePolRz (evalZ Ar c) (samePolRz pol (rZPlus a))).
case (evalZ Ar c); case pol; simpl in |- *; auto; intros r1 r2;
 apply eqStateInvInv; simpl in |- *; auto.
apply eqStateaddEq2.
case (SisAr (samePolRz (evalZ Ar c) (samePolRz pol (rZPlus a))) d);
 intros H' H'0; apply H'0; auto.
rewrite <- H0; case pol; case (evalZ Ar c); simpl in |- *; intros r1 r2;
 unfold evalN in |- *; rewrite geta; auto.
rewrite updateEvalZO; auto.
case (rNatDec (valRz (evalZ Ar d)) b); intros Eqt'.
rewrite updateEvalZb; auto.
intros H0;
 apply
  eqStateRzTrans
   with (b := samePolRz (evalZ Ar d) (samePolRz pol (rZPlus a))).
apply eqStateaddEq2.
case (SisAr c (samePolRz (evalZ Ar d) (samePolRz pol (rZPlus a))));
 intros H' H'0; apply H'0; auto.
rewrite H0; case pol; case (evalZ Ar d); simpl in |- *; intros r1 r2;
 unfold evalN in |- *; rewrite geta; auto.
apply eqStateRzTrans with (b := samePolRz (evalZ Ar d) (rZPlus b)).
case (evalZ Ar d); case pol; simpl in |- *; auto.
apply eqStateaddEq2.
case (SisAr (samePolRz (evalZ Ar d) (rZPlus b)) d); intros H' H'0; apply H'0;
 auto.
rewrite <- Eqt'; generalize (evalZInv Ar War d); case (evalZ Ar d);
 simpl in |- *; auto.
rewrite updateEvalZO; auto.
intros H'; apply eqStateaddEq2.
case (SisAr c d); auto.
Qed.
End Dprop.
(* To be able to return a triple *)

Inductive Triple (A B C : Set) : Set :=
    triple : A -> B -> C -> Triple A B C.

(* Adding an equation returns 3 elements:
    - The new array
    - A boolean that says if a contradiction has been reached
    - The list of elements of the array whose values have changed
         (it is rZ not rNat to avoid reconstruction)
*)

Definition mbD := Triple (rArray vM) bool (list rZ).

Definition mbDOp := triple (rArray vM) bool (list rZ).

(* A let that is not simplified during extraction *)

Definition letP (A B : Set) (h : A) (u : A -> B) : B := u h.

(* Given a rNat n returns the equivalence class*)

Definition getClassN (Ar : rArray vM) (v : rNat) : 
  list rZ := match rArrayGet _ Ar v with
             | ref _ => nil
             | class l => l
             end.

Theorem GetClassNProp :
 forall (Ar : rArray vM) (a : rZ),
 wellFormedArray Ar ->
 rArrayGet vM Ar (valRz (evalZ Ar a)) =
 class (getClassN Ar (valRz (evalZ Ar a))).
intros Ar a War; case a; simpl in |- *; unfold evalN, getClassN in |- *;
 intros r; generalize (fun s => wfPcr _ War r s); CaseEq (rArrayGet vM Ar r);
 simpl in |- *.
intros r0 H' H'0; CaseEq (rArrayGet vM Ar (valRz r0)); auto.
intros r1 H'1; case (H'0 r0 r1); auto.
intros l H'; rewrite H'; auto.
intros r0 H' H'0; rewrite (valRzComp r0); CaseEq (rArrayGet vM Ar (valRz r0));
 auto.
intros r1 H'1; case (H'0 r0 r1); auto.
intros l H'; rewrite H'; auto.
Qed.
(* To add an equation, we find the minimal elements and
     compare them to build the proper call to update *)

Definition addEqMem : forall (Ar : rArray vM) (a b : rZ), mbD.
intros Ar a b.
apply letP with (1 := evalZ Ar a); intros a'.
apply letP with (1 := evalZ Ar b); intros b'.
case (rZltEDec a' b'); intros rLt; [ Casec rLt; intros rLt | idtac ].
apply letP with (1 := getClassN Ar (valRz a')); intros La'.
apply letP with (1 := getClassN Ar (valRz b')); intros Lb'.
exact
 (mbDOp (updateArray (valRz a') (valRz b') (samePolRz a' b') La' Lb' Ar)
    false (a' :: b' :: Lb')).
apply letP with (1 := getClassN Ar (valRz a')); intros La'.
apply letP with (1 := getClassN Ar (valRz b')); intros Lb'.
exact
 (mbDOp (updateArray (valRz b') (valRz a') (samePolRz b' a') Lb' La' Ar)
    false (b' :: a' :: La')).
case (rZDec a' b'); intros eqa'b'.
exact (mbDOp Ar false nil).
exact (mbDOp Ar true nil).
Defined.
Require Import stateDec.

(* The property for an array to represent a state *)

Definition rArrayState (Ar : rArray vM) (S : State) :=
  forall c d : rZ, eqStateRz S c d <-> evalZ Ar c = evalZ Ar d.

Theorem rArrayStateDef1 :
 forall (Ar : rArray vM) (S : State) (c d : rZ),
 rArrayState Ar S -> eqStateRz S c d -> evalZ Ar c = evalZ Ar d.
intros Ar S c d H' H'0; case (H' c d); auto.
Qed.

Theorem rArrayStateDef2 :
 forall (Ar : rArray vM) (S : State) (c d : rZ),
 rArrayState Ar S -> evalZ Ar c = evalZ Ar d -> eqStateRz S c d.
intros Ar S c d H' H'0; case (H' c d); auto.
Qed.

Theorem rArrayStateGet :
 forall (Ar Ar' : rArray vM) (S : State),
 rArrayState Ar S ->
 (forall e : rNat, rArrayGet vM Ar' e = rArrayGet vM Ar e) ->
 rArrayState Ar' S.
intros Ar Ar' S H' H'0.
red in |- *; split; repeat rewrite <- (rArrayGetEvalZ _ _ H'0); auto;
 case (H' c d); auto.
Qed.
(* rArrayState is compatible with equality *)

Theorem rArrayStateEqState :
 forall (Ar : rArray vM) (S S' : State),
 rArrayState Ar S -> eqState S S' -> rArrayState Ar S'.
intros Ar S S' H' H'0; red in |- *; split.
intros H'1.
apply rArrayStateDef1 with (S := S); auto.
apply eqStateEq with (S1 := S'); auto.
intros H'1.
apply eqStateEq with (S1 := S); auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
Qed.
(* The empty array represents the empty state *)

Theorem initCorrect :
 rArrayState (rArrayInit _ (fun n : rNat => class nil)) nil.
red in |- *; intros c d; split; intros H'.
cut (eqConstrState nil c d).
intros H'0; inversion H'0; auto.
apply eqStateRzPImpeqConstrState; auto.
generalize H'; case c; case d; simpl in |- *; unfold evalN in |- *;
 intros r r0; rewrite (rArrayDef vM r0 (fun _ : rNat => class nil));
 rewrite (rArrayDef vM r (fun _ : rNat => class nil)); 
 simpl in |- *; intros H'0; rewrite H'0 || rewrite <- H'0; 
 auto.
Qed.

Theorem getClassOlist :
 forall (Ar : rArray vM) (a : rZ),
 wellFormedArray Ar ->
 OlistRz (evalZ Ar a :: getClassN Ar (valRz (evalZ Ar a))).
intros Ar a War; case a; simpl in |- *.
intros r; unfold evalN, getClassN in |- *.
CaseEq (rArrayGet vM Ar r); simpl in |- *.
intros r0; CaseEq (rArrayGet vM Ar (valRz r0)); simpl in |- *.
intros r1 H' H'0; red in |- *; apply OlistOne; auto.
intros l; case l.
intros H' H'0; red in |- *; apply OlistOne; auto.
intros r1 l0 H' H'0; red in |- *; apply OlistCons; auto.
apply wfOl with (Ar := Ar) (r := valRz r0); auto.
cut (rVlt (samePol r1 (valRz r0)) (valRz r1)).
case r1; simpl in |- *; auto.
apply wfPd with (Ar := Ar); auto.
apply wfPcc1 with (Lr := r1 :: l0); simpl in |- *; auto.
intros l; case l.
intros H'; rewrite H'; red in |- *; apply OlistOne; auto.
intros r0 l0 H'; rewrite H'; red in |- *; apply OlistCons; auto.
apply wfOl with (Ar := Ar) (r := r); auto.
cut (rVlt (samePol r0 r) (valRz r0)).
case r0; simpl in |- *; auto.
apply wfPd with (Ar := Ar); auto.
apply wfPcc1 with (Lr := r0 :: l0); simpl in |- *; auto.
intros r; unfold evalN, getClassN in |- *.
CaseEq (rArrayGet vM Ar r); simpl in |- *.
intros r0; rewrite (valRzComp r0); CaseEq (rArrayGet vM Ar (valRz r0));
 simpl in |- *.
intros r1 H' H'0; red in |- *; apply OlistOne; auto.
intros l; case l.
intros H' H'0; red in |- *; apply OlistOne; auto.
intros r1 l0 H' H'0; red in |- *; apply OlistCons; auto.
apply wfOl with (Ar := Ar) (r := valRz r0); auto.
cut (rVlt (samePol r1 (valRz r0)) (valRz r1)).
case r0; case r1; simpl in |- *; auto.
apply wfPd with (Ar := Ar); auto.
apply wfPcc1 with (Lr := r1 :: l0); simpl in |- *; auto.
intros l; case l.
intros H'; rewrite H'; red in |- *; apply OlistOne; auto.
intros r0 l0 H'; rewrite H'; red in |- *; apply OlistCons; auto.
apply wfOl with (Ar := Ar) (r := r); auto.
cut (rVlt (samePol r0 r) (valRz r0)).
case r0; simpl in |- *; auto.
apply wfPd with (Ar := Ar); auto.
apply wfPcc1 with (Lr := r0 :: l0); simpl in |- *; auto.
Qed.
(* addMem is correct, ie
   If the boolean is true, we have reached a contradiction 
   If the boolena is false, the resulting array is well-formed
   it represents the state plus the equation,
   the diff list is ordered, and elements outside this list are unchanged *)

Theorem addEqMemCorrect :
 forall (Ar : rArray vM) (a b : rZ) (S : State),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 match addEqMem Ar a b with
 | triple Ar' false L =>
     wellFormedArray Ar' /\
     rArrayState Ar' (addEq (a, b) S) /\
     OlistRz L /\
     (forall c : rNat,
      ~ InRz (rZPlus c) L -> rArrayGet _ Ar' c = rArrayGet _ Ar c)
 | triple Ar' true L => contradictory (addEq (a, b) S)
 end.
intros Ar a b S War H'; unfold addEqMem, letP in |- *.
case (rZltEDec (evalZ Ar a) (evalZ Ar b)); simpl in |- *.
intros s; case s; simpl in |- *.
intros H'0; split.
apply updateWellFormed; auto.
apply GetClassNProp; auto.
apply GetClassNProp; auto.
split.
red in |- *; intros c d; repeat split; intros H0.
case
 (updateCorrect Ar War (valRz (evalZ Ar a)) (valRz (evalZ Ar b))
    (samePolRz (evalZ Ar a) (evalZ Ar b)) (getClassN Ar (valRz (evalZ Ar a)))
    (getClassN Ar (valRz (evalZ Ar b)))) with (S := S) (c := c) (d := d);
 auto; auto.
apply GetClassNProp; auto.
apply GetClassNProp; auto.
intros H'1 H'2; apply H'1; auto.
apply eqStateIncl with (2 := H0); auto.
apply inclStateIn; simpl in |- *; auto.
intros a0 b0 H'3; Elimc H'3; intros H'3.
inversion H'3; auto.
apply eqStateRzTrans with (b := evalZ Ar a0).
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZInv; auto.
apply eqStateRzTrans with (b := evalZ Ar b0).
case (evalZ Ar a0); case (evalZ Ar b0); simpl in |- *; auto.
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZInv; auto.
apply eqStateaddEq2; auto.
apply
 eqStateIncl
  with
    (addEq
       (rZPlus (valRz (evalZ Ar a)),
       samePol (samePolRz (evalZ Ar a) (evalZ Ar b)) (valRz (evalZ Ar b))) S);
 auto.
apply inclStateIn; simpl in |- *; auto.
intros a0 b0 H'1; Elimc H'1; intros H'1; auto.
inversion H'1; auto.
apply eqStateRzTrans with (b := samePolRz (evalZ Ar a) a).
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
generalize (evalZInv Ar War a); CaseEq (evalZ Ar a); simpl in |- *; auto.
intros r H'2; rewrite H'2; auto.
intros r H'2 H'3; rewrite evalZComp; rewrite H'2; rewrite <- H'3;
 case (evalN Ar r); auto.
apply eqStateRzTrans with (b := samePolRz (evalZ Ar a) b); auto.
case (evalZ Ar a); simpl in |- *; auto.
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
case (evalZ Ar a); simpl in |- *; auto.
generalize (evalZInv Ar War b); CaseEq (evalZ Ar b); simpl in |- *; auto.
generalize (evalZInv Ar War b); CaseEq (evalZ Ar b); simpl in |- *; auto.
intros r H'2 H'3; rewrite evalZComp; rewrite H'3; rewrite <- H'2; auto.
intros r H'2 H'3; rewrite evalZComp; rewrite H'2; rewrite <- H'3; auto.
case
 (updateCorrect Ar War (valRz (evalZ Ar a)) (valRz (evalZ Ar b))
    (samePolRz (evalZ Ar a) (evalZ Ar b)) (getClassN Ar (valRz (evalZ Ar a)))
    (getClassN Ar (valRz (evalZ Ar b)))) with (S := S) (c := c) (d := d);
 auto; auto.
apply GetClassNProp; auto.
apply GetClassNProp; auto.
split.
red in |- *; apply OlistCons; auto.
apply getClassOlist; auto.
intros c H'1.
apply updateArrayOtherwise; auto.
Contradict H'1; simpl in |- *; auto.
red in |- *; repeat apply InEqSkip; auto.
Contradict H'1; rewrite H'1; simpl in |- *; auto.
red in |- *; apply InEqHead; auto.
Contradict H'1; rewrite H'1; auto.
red in |- *; apply InEqSkip; apply InEqHead; auto.
intros H'0; split.
apply updateWellFormed; auto.
apply GetClassNProp; auto.
apply GetClassNProp; auto.
split.
red in |- *; intros c d; split; intros H0.
case
 (updateCorrect Ar War (valRz (evalZ Ar b)) (valRz (evalZ Ar a))
    (samePolRz (evalZ Ar b) (evalZ Ar a)) (getClassN Ar (valRz (evalZ Ar b)))
    (getClassN Ar (valRz (evalZ Ar a)))) with (S := S) (c := c) (d := d);
 auto.
apply GetClassNProp; auto.
apply GetClassNProp; auto.
intros H'1 H'2; apply H'1; auto.
apply eqStateIncl with (2 := H0); auto.
apply inclStateIn; simpl in |- *; auto.
intros a0 b0 H'3; Elimc H'3; intros H'3.
inversion H'3; auto.
apply eqStateRzTrans with (b := evalZ Ar a0).
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZInv; auto.
apply eqStateRzTrans with (b := evalZ Ar b0).
case (evalZ Ar a0); case (evalZ Ar b0); simpl in |- *; auto; intros r1 r2;
 apply eqStateInvInv; auto.
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZInv; auto.
apply eqStateaddEq2; auto.
apply
 eqStateIncl
  with
    (addEq
       (rZPlus (valRz (evalZ Ar a)),
       samePol (samePolRz (evalZ Ar a) (evalZ Ar b)) (valRz (evalZ Ar b))) S);
 auto.
apply inclStateIn; simpl in |- *; auto.
intros a0 b0 H'1; Elimc H'1; intros H'1.
inversion H'1; auto.
apply eqStateRzTrans with (b := samePolRz (evalZ Ar a) a).
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
generalize (evalZInv Ar War a); CaseEq (evalZ Ar a); simpl in |- *; auto.
intros r H'2; rewrite H'2; auto.
intros r H'2 H'3; rewrite evalZComp; rewrite H'2; rewrite <- H'3;
 case (evalN Ar r); auto.
apply eqStateRzTrans with (b := samePolRz (evalZ Ar a) b); auto.
case (evalZ Ar a); simpl in |- *; auto.
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
case (evalZ Ar a); simpl in |- *; auto.
generalize (evalZInv Ar War b); CaseEq (evalZ Ar b); simpl in |- *; auto.
generalize (evalZInv Ar War b); CaseEq (evalZ Ar b); simpl in |- *; auto.
intros r H'2 H'3; rewrite evalZComp; rewrite H'3; rewrite <- H'2; auto.
intros r H'2 H'3; rewrite evalZComp; rewrite H'2; rewrite <- H'3; auto.
apply eqStateRzIn; unfold addEq in |- *; auto with datatypes.
apply
 eqStateIncl
  with
    (addEq
       (rZPlus (valRz (evalZ Ar b)),
       samePol (samePolRz (evalZ Ar b) (evalZ Ar a)) (valRz (evalZ Ar a))) S);
 auto.
apply inclStateIn; simpl in |- *; auto.
intros a0 b0 H'1; Elimc H'1; intros H'1; auto.
inversion H'1; auto.
case (evalZ Ar a); case (evalZ Ar b); simpl in |- *; auto; intros r1 r2;
 apply eqStateInvInv; auto.
case
 (updateCorrect Ar War (valRz (evalZ Ar b)) (valRz (evalZ Ar a))
    (samePolRz (evalZ Ar b) (evalZ Ar a)) (getClassN Ar (valRz (evalZ Ar b)))
    (getClassN Ar (valRz (evalZ Ar a)))) with (S := S) (c := c) (d := d);
 auto; auto.
apply GetClassNProp; auto.
apply GetClassNProp; auto.
split; auto.
red in |- *; apply OlistCons; auto.
apply getClassOlist; auto.
intros c H'1.
apply updateArrayOtherwise; auto.
Contradict H'1; simpl in |- *; auto.
red in |- *; repeat apply InEqSkip; auto.
Contradict H'1; rewrite H'1; simpl in |- *; auto.
red in |- *; apply InEqHead; auto.
Contradict H'1; rewrite H'1; auto.
red in |- *; apply InEqSkip; apply InEqHead; auto.
case (rZDec (evalZ Ar a) (evalZ Ar b)); simpl in |- *; auto.
intros H'0 H'1; split; auto.
split; auto.
red in |- *; intros c d; split; intros H'2.
apply rArrayStateDef1 with (S := S); auto.
apply eqStateIncl with (2 := H'2); auto.
apply inclStateIn; simpl in |- *; auto.
intros a0 b0 H'3; Elimc H'3; intros H'3; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
inversion H'3; auto.
rewrite <- H1; rewrite <- H0; auto.
apply eqStateaddEq2.
apply rArrayStateDef2 with (Ar := Ar); auto.
split; auto.
red in |- *; apply OlistNil; auto.
intros H'0 H'1; red in |- *; exists a.
apply eqStateRzTrans with (b := b); auto.
apply eqStateaddEq2; auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
rewrite evalZComp; auto.
generalize H'0 H'1; case (evalZ Ar a); case (evalZ Ar b); unfold eqRz in |- *;
 simpl in |- *; intros r r0 H'4 H'5; rewrite H'5; auto; 
 case H'4; rewrite H'5; auto.
Qed.
(* Same but adding a=b and c=d *)

Definition addEqMem2 : forall (Ar : rArray vM) (a b c d : rZ), mbD.
intros Ar a b c d.
case (addEqMem Ar a b).
intros Ar' b' L'; case b'.
exact (mbDOp Ar' b' L').
case (addEqMem Ar' c d).
intros Ar'' b'' L''.
exact (mbDOp Ar'' b'' (appendRz L' L'')).
Defined.

Theorem addEqMem2Correct :
 forall (Ar : rArray vM) (a b c d : rZ) (S : State),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 match addEqMem2 Ar a b c d with
 | triple Ar' false L =>
     wellFormedArray Ar' /\
     rArrayState Ar' (addEq (c, d) (addEq (a, b) S)) /\
     OlistRz L /\
     (forall e : rNat,
      ~ InRz (rZPlus e) L -> rArrayGet _ Ar' e = rArrayGet _ Ar e)
 | triple Ar' true L => contradictory (addEq (c, d) (addEq (a, b) S))
 end.
intros Ar a b c d S War H'; unfold addEqMem2 in |- *.
generalize (addEqMemCorrect Ar a b S War H').
case (addEqMem Ar a b); simpl in |- *.
intros Ar' b' L'; case b'; simpl in |- *.
intros H'0; red in |- *; inversion H'0.
exists x; auto.
intros H'0; Elimc H'0; intros H'0 H'1; Elimc H'1; intros H'1 H'2; Elimc H'2;
 intros H'2 H'3.
generalize (addEqMemCorrect Ar' c d (addEq (pair a b) S) H'0 H'1);
 case (addEqMem Ar' c d); simpl in |- *.
intros Ar'' b'' L''; case b''; simpl in |- *; auto.
intros H'4; Elimc H'4; intros H'4 H'5; Elimc H'5; intros H'5 H'6; Elimc H'6;
 intros H'6 H'7; repeat (split; auto).
red in |- *; unfold appendRz in |- *; apply appendfOlist; auto.
exact rZltEqComp.
intros e H'8.
rewrite H'7; auto.
apply H'3; auto.
Contradict H'8; auto.
cut (InclEq _ eqRz L' (appendf _ rZlt eqRz rZltEDec L' L'')).
intros H'9; inversion H'9; red in |- *; auto.
apply appendfInclEq1; auto.
Contradict H'8; auto.
cut (InclEq _ eqRz L'' (appendf _ rZlt eqRz rZltEDec L' L'')).
intros H'9; inversion H'9; red in |- *; auto.
apply appendfInclEq2; auto.
Qed.
