
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
intros r1 H'0; absurd False; auto.
Contradict H'0.
apply wfPcr with (2 := H'); auto.
intros L HL; split; auto.
generalize HL; case L; auto.
intros H'0; red in |- *; apply OlistOne; auto.
intros r1 l H'0.
red in |- *; apply OlistCons; auto.
apply wfOl with (2 := H'0); auto.
red in |- *; apply wellFormedArrayInImpLt with (2 := H'0); simpl in |- *;
 auto.
intros c; case c; simpl in |- *; split.
intros H'0; Elimc H'0; intros H'0.
inversion H'0; rewrite <- H0.
unfold evalN in |- *; rewrite HL; rewrite H'; auto.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto.
unfold evalN in |- *; rewrite H'; auto.
CaseEq (rArrayGet vM Ar r1); auto.
intros r2 H'0 H'1; right.
replace (rZPlus r1) with (samePol (rZPlus r0) r1).
apply wfPcc2 with (Ar := Ar); auto.
rewrite <- H'1; auto.
simpl in |- *; auto.
intros H'0; Elimc H'0; intros H'0.
discriminate.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto.
unfold evalN in |- *; rewrite H'; auto.
CaseEq (rArrayGet vM Ar r1); auto.
intros r2 H'0 H'1; right.
replace (rZMinus r1) with (samePol (rZComp (rZPlus r0)) r1).
apply wfPcc2 with (Ar := Ar); auto.
rewrite <- H'1; rewrite rZCompInv; auto.
simpl in |- *; auto.
intros r0 H'; CaseEq (rArrayGet _ Ar r0).
intros r1 H'0; absurd False; auto.
Contradict H'0.
apply wfPcr with (2 := H'); auto.
intros L HL; split; auto.
generalize HL; case L; auto.
intros H'0; red in |- *; apply OlistOne; auto.
intros r1 l H'0.
red in |- *; apply OlistCons; auto.
apply wfOl with (2 := H'0); auto.
red in |- *; apply wellFormedArrayInImpLt with (2 := H'0); simpl in |- *;
 auto.
intros c; case c; simpl in |- *; split.
intros H'0; Elimc H'0; intros H'0.
discriminate.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto.
unfold evalN in |- *; rewrite H'; auto.
CaseEq (rArrayGet vM Ar r1); auto.
intros r2 H'0 H'1; right.
replace (rZMinus r1) with (samePol (rZMinus r0) r1).
apply wfPcc2 with (Ar := Ar); auto.
rewrite <- H'1; auto.
simpl in |- *; auto.
intros l H'0 H'1; discriminate.
intros H'0; Elimc H'0; intros H'0.
inversion H'0; rewrite <- H0.
unfold evalN in |- *; rewrite HL; rewrite H'; auto.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ HL H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto.
unfold evalN in |- *; rewrite H'; auto.
CaseEq (rArrayGet vM Ar r1); auto.
intros r2 H'0 H'1; right.
replace (rZPlus r1) with (samePol (rZComp (rZMinus r0)) r1).
apply wfPcc2 with (Ar := Ar); auto.
rewrite <- H'1; rewrite rZCompInv; auto.
simpl in |- *; auto.
simpl in |- *; intros l H'0 H'1; inversion H'1; auto.
intros L H'; split.
generalize H'; case L.
intros H'0; red in |- *; apply OlistOne; auto.
intros r l H'0; red in |- *; apply OlistCons; auto.
apply wfOl with (2 := H'0); auto.
red in |- *; apply wellFormedArrayInImpLt with (2 := H'0); simpl in |- *;
 auto.
intros c; case c; simpl in |- *; split.
intros H'0; Elimc H'0; intros H'0.
inversion H'0; rewrite <- H0; auto.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ H' H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto.
unfold evalN in |- *; rewrite H'; auto.
CaseEq (rArrayGet vM Ar r); auto.
intros r0 H'0 H'1; right.
replace (rZPlus r) with (samePol (rZPlus a) r).
apply wfPcc2 with (Ar := Ar); auto.
rewrite <- H'1; auto.
simpl in |- *; auto.
intros H'0; Elimc H'0; intros H'0.
discriminate.
unfold evalN in |- *; rewrite H'; generalize (wfPcc1 _ War _ _ _ H' H'0);
 simpl in |- *; intros H'1; rewrite H'1; auto.
unfold evalN in |- *; rewrite H'; auto.
CaseEq (rArrayGet vM Ar r); auto.
intros r0 H'0 H'1; right.
replace (rZMinus r) with (samePol (rZComp (rZPlus a)) r).
apply wfPcc2 with (Ar := Ar); auto.
rewrite <- H'1; rewrite rZCompInv; auto.
simpl in |- *; auto.
Defined.

Theorem getEquivProp1 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rNat) (c : rZ),
 snd (getEquiv Ar a) = true ->
 (In (rZComp c) (fst (getEquiv Ar a)) <-> evalZ Ar c = evalZ Ar (rZPlus a)).
intros Ar War a c; generalize (getEquivProp Ar War a); case (getEquiv Ar a);
 auto.
intros x; case x; auto.
intros b; case b; simpl in |- *; auto.
intros H'; elim H'; auto.
intros H' H'0; discriminate.
intros r l b; case b; simpl in |- *; auto.
intros H'; elim H'; auto.
intros H' H'0; discriminate.
Qed.

Theorem getEquivProp2 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rNat) (c : rZ),
 snd (getEquiv Ar a) = false ->
 (In c (fst (getEquiv Ar a)) <-> evalZ Ar c = evalZ Ar (rZPlus a)).
intros Ar War a c; generalize (getEquivProp Ar War a); case (getEquiv Ar a);
 auto.
intros x; case x; auto.
intros b; case b; simpl in |- *; auto.
intros H' H'0; discriminate.
intros H'; elim H'; auto.
intros r l b; case b; simpl in |- *; auto.
intros H' H'0; discriminate.
intros H'; elim H'; auto.
Qed.

Theorem getEquivProp3 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rNat),
 OlistRz (fst (getEquiv Ar a)).
intros Ar War a; generalize (getEquivProp Ar War a); case (getEquiv Ar a);
 auto.
intros x; case x; auto.
intros b; case b; intros H'; elim H'; auto.
intros r l b; case b; intros H'; elim H'; auto.
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
intros a L; elim L; simpl in |- *; auto.
intros a0 l H' H'0; Elimc H'0; auto.
left; apply rZCompEq; auto.
Qed.

Theorem getEquivListProp1 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a c : rZ),
 In c (getEquivList Ar a) <-> evalZ Ar c = evalZ Ar a.
intros Ar War a; unfold getEquivList in |- *; case a; intros a';
 generalize (getEquivProp1 Ar War a'); generalize (getEquivProp2 Ar War a');
 case (getEquiv Ar a'); simpl in |- *; auto; intros l b; 
 case b; auto.
intros H' H'0 c.
lapply (H'0 c); [ intros H'1; red in H'1 | idtac ]; auto.
Elimc H'1; intros H'1 H'2.
red in |- *; split; intros H'3; auto.
apply H'1; auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
rewrite (rZCompInvol c); apply in_map; auto.
intros H' H'0 c.
lapply (H'0 (rZComp c));
 [ rewrite <- rZCompInvol; intros H'1; red in H'1 | idtac ]; 
 auto.
Elimc H'1; intros H'1 H'2.
red in |- *; split; intros H'3; auto.
rewrite <- H'1; auto.
rewrite (evalZComp Ar c); auto.
apply H'2; auto.
rewrite (evalZComp Ar c); auto.
rewrite H'3; auto.
intros H' H'0 c.
lapply (H' (rZComp c)); [ intros H'1; red in H'1 | idtac ]; auto.
Elimc H'1; intros H'1 H'2.
red in |- *; split; intros H'3; auto.
rewrite <- H'1; auto.
rewrite (evalZComp Ar c); auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
rewrite (rZCompInvol c); apply in_map; auto.
apply H'2; auto.
rewrite (evalZComp Ar c); auto.
rewrite H'3; auto.
Qed.

Theorem getEquivListProp2 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rZ),
 OlistRz (getEquivList Ar a).
intros Ar War a; unfold getEquivList in |- *; case a; intros a';
 generalize (getEquivProp3 Ar War a'); case (getEquiv Ar a'); 
 simpl in |- *; auto; intros l b; case b; auto; intros H'; 
 red in |- *; apply Olistf with (eqA := eqRz); auto; 
 exact rZltEqComp.
Qed.

Theorem getEquivListProp3 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (a : rZ),
 In a (getEquivList Ar a).
intros Ar War a.
case (getEquivListProp1 _ War a a); auto.
Qed.

Theorem getEquivListProp4 :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (S : State),
 rArrayState Ar S ->
 forall a b : rZ, eqStateRz S a b <-> getEquivList Ar a = getEquivList Ar b.
intros Ar War S Sar a b; red in |- *; split; intros H'1; auto.
cut (EqL _ (eq (A:=rZ)) (getEquivList Ar a) (getEquivList Ar b)).
intros H'; elim H'; simpl in |- *; auto.
intros a0 b0 L1 L2 H'0 H'2 H'3; rewrite H'0; rewrite H'3; auto.
apply EqLOlist with (ltA := rZlt); try (red in |- *; auto; fail); auto.
intros a0 b0 H'; red in |- *; intros H'0; absurd (rZlt a0 b0); auto;
 rewrite H'0; auto.
intros a0 b0 c d H' H'0 H'2; rewrite <- H'0; rewrite <- H'2; auto.
apply getEquivListProp2; auto.
apply getEquivListProp2; auto.
apply InclEqDef; auto.
intros a0 H'; apply inImpInEq; auto.
red in |- *; auto.
case (getEquivListProp1 Ar War b a0).
intros H'0 H'2; apply H'2; auto.
apply trans_equal with (evalZ Ar a).
case (getEquivListProp1 Ar War a a0).
intros H'3 H'4; apply H'3.
elim H'; simpl in |- *; auto.
apply rArrayStateDef1 with (S := S); auto.
apply InclEqDef; auto.
intros a0 H'; apply inImpInEq; auto.
red in |- *; auto.
case (getEquivListProp1 Ar War a a0).
intros H'0 H'2; apply H'2.
apply trans_equal with (evalZ Ar b).
case (getEquivListProp1 Ar War b a0).
intros H'3 H'4; apply H'3.
elim H'; simpl in |- *; auto.
apply rArrayStateDef1 with (S := S); auto.
apply rArrayStateDef2 with (Ar := Ar); auto.
case (getEquivListProp1 Ar War b a); auto.
intros H' H'0; apply H'.
rewrite <- H'1.
apply getEquivListProp3; auto.
Qed.

Definition getMinId :=
  getMin _ rZlt eqRz rZltEDec (eq (A:=rZ)) (fun (a b : rZ) _ => rZDec a b).

Theorem getMinIdSym :
 forall L1 L2 : list rZ,
 OlistRz L1 -> OlistRz L2 -> getMinId L1 L2 = getMinId L2 L1.
intros L1 L2 H' H'0; CaseEq (getMinId L1 L2).
CaseEq (getMinId L2 L1).
intros x H'1 x0 H'2.
case (rZltEDec x0 x); auto.
intros H'3; case H'3.
intros H'4.
absurd (x0 = x0); auto.
unfold getMinId in H'1; apply getMinMin with (10 := H'1); auto.
intros a b H'5; rewrite H'5; auto.
unfold getMinId in H'2; case getMinComp with (4 := H'2); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto.
intros H'4.
absurd (x = x); auto.
unfold getMinId in H'2; apply getMinMin with (10 := H'2); auto.
intros a b H'5; rewrite H'5; auto.
unfold getMinId in H'1; case getMinComp with (4 := H'1); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto.
unfold getMinId in H'1; apply geMinIn with (4 := H'1); auto.
intros H'3; rewrite (OlistIn _ rZlt eqRz) with (L := L1) (7 := H'3); auto.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto.
unfold getMinId in H'1; case getMinComp with (4 := H'1); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto.
intros H'1 x H'2; absurd (x = x); auto.
unfold getMinId in H'1; apply getMinNone with (8 := H'1); auto.
intros a b H'3; rewrite H'3; auto.
unfold getMinId in H'2; case getMinComp with (4 := H'2); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto.
intros H'1; CaseEq (getMinId L2 L1); auto.
intros x H'2; absurd (x = x); auto.
unfold getMinId in H'1; apply getMinNone with (8 := H'1); auto.
intros a b H'3; rewrite H'3; auto.
unfold getMinId in H'2; case getMinComp with (4 := H'2); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; auto.
unfold getMinId in H'2; apply geMinIn with (4 := H'2); auto.
Qed.

Definition getMinInv :=
  getMin _ rZlt eqRz rZltEDec (fun a b : rZ => a = rZComp b)
    (fun (a b : rZ) (_ : eqRz a b) => rZDec a (rZComp b)).

Theorem getMinInvSym :
 forall L1 L2 : list rZ,
 OlistRz L1 ->
 OlistRz L2 ->
 match getMinInv L1 L2 with
 | None => getMinInv L2 L1 = None _
 | Some a => getMinInv L2 L1 = Some _ (rZComp a)
 end.
intros L1 L2 H' H'0; CaseEq (getMinInv L1 L2).
CaseEq (getMinInv L2 L1).
intros x H'1 x0 H'2.
case (rZltEDec x0 x); auto.
intros H'3; case H'3.
intros H'4.
absurd (rZComp x0 = rZComp x0); auto.
unfold getMinInv in H'1; apply getMinMin with (10 := H'1); auto.
intros a b H'5; rewrite H'5; auto.
apply rZltEqComp with (a := x0) (b := x); auto.
unfold getMinInv in H'2; case getMinComp with (4 := H'2); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto.
intros H'4.
absurd (rZComp x = rZComp x); auto.
unfold getMinInv in H'2; apply getMinMin with (10 := H'2); auto.
intros a b H'5; rewrite H'5; auto.
apply rZltEqComp with (a := x) (b := x0); auto.
unfold getMinInv in H'1; case getMinComp with (4 := H'1); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto.
unfold getMinInv in H'1; apply geMinIn with (4 := H'1); auto.
intros H'3;
 rewrite (OlistIn _ rZlt eqRz) with (L := L1) (a := x0) (b := rZComp x); 
 auto.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto.
unfold getMinInv in H'1; case getMinComp with (4 := H'1); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto.
apply eqrZTrans with (1 := H'3); auto.
intros H'1 x H'2; absurd (rZComp x = rZComp x); auto.
unfold getMinInv in H'1; apply getMinNone with (8 := H'1); auto.
intros a b H'3; rewrite H'3; auto.
unfold getMinInv in H'2; case getMinComp with (4 := H'2); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto.
intros H'1; CaseEq (getMinInv L2 L1); auto.
intros x H'2; absurd (rZComp x = rZComp x); auto.
unfold getMinInv in H'1; apply getMinNone with (8 := H'1); auto.
intros a b H'3; rewrite H'3; auto.
unfold getMinInv in H'2; case getMinComp with (4 := H'2); auto.
intros x1 H'5; elim H'5; intros H'6 H'7; rewrite H'6; rewrite rZCompInv; auto.
unfold getMinInv in H'2; apply geMinIn with (4 := H'2); auto.
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
intros L1 b1 L2 b2 OL1 OL2; case b1; case b2; auto;
 try rewrite (getMinIdSym L1 L2); auto; generalize (getMinInvSym L1 L2); 
 auto; case (getMinInv L1 L2); auto; case (getMinInv L2 L1); 
 auto; intros x1 x2 Hx1 || intros x1 Hx1; auto; generalize (Hx1 OL1 OL2);
 intros Inv0; inversion Inv0; auto.
Qed.

Theorem rZCompInvolList : forall L : list rZ, L = map rZComp (map rZComp L).
intros L; elim L; simpl in |- *; auto.
intros a l H'; rewrite <- H'; auto with datatypes.
rewrite <- rZCompInvol; auto.
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
 case b0; auto.
CaseEq (getMinId l l0); auto.
intros x H' H'0 H'1 H'2 H'3; apply in_map; auto.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZMinus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
apply inMapComp; auto.
CaseEq (getMinInv l l0); auto.
intros x H' H'0 H'1 H'2 H'3; apply in_map; auto.
unfold getMinInv in H'; apply geMinIn with (4 := H'); auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZPlus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
CaseEq (getMinInv l l0); auto.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinInv in H'; apply geMinIn with (4 := H'); auto.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZMinus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
CaseEq (getMinId l l0); auto.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZPlus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
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
 case b0; auto.
CaseEq (getMinId l l0); auto.
intros x H' H'0 H'1 H'2 H'3; apply in_map; auto.
unfold getMinId in H'; case getMinComp with (4 := H'); auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZMinus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
apply inMapComp; auto.
CaseEq (getMinInv l l0); auto.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinInv in H'; case getMinComp with (4 := H'); auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5; rewrite rZCompInv; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZPlus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
CaseEq (getMinInv l l0); auto.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinInv in H'; case getMinComp with (4 := H'); auto.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5.
apply inMapComp; rewrite <- (rZCompInvolList l0); rewrite rZCompInv; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZMinus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
CaseEq (getMinId l l0); auto.
intros x H' H'0 H'1 H'2 H'3.
unfold getMinId in H'; case getMinComp with (4 := H'); auto.
intros x0 H'4; elim H'4; intros H'5 H'6; rewrite H'5; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZPlus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
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
 case b0; auto.
CaseEq (getMinId l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6.
absurd (rZComp c = rZComp c); auto.
unfold getMinId in H'; apply getMinMin with (10 := H'); auto.
intros a0 b1 H'7; rewrite H'7; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply rZltEqComp with (a := c) (b := rZComp x); auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZMinus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
apply inMapComp; auto.
CaseEq (getMinInv l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6; auto.
absurd (rZComp c = rZComp c); auto.
unfold getMinInv in H'; apply getMinMin with (10 := H'); auto.
intros a0 b1 H'7; rewrite H'7; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply rZltEqComp with (a := c) (b := rZComp x); auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZMinus a) (b := rZPlus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
CaseEq (getMinInv l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6.
absurd (c = rZComp (rZComp c)); auto.
unfold getMinInv in H'; apply getMinMin with (10 := H'); auto.
intros a0 b1 H'7; rewrite H'7; auto.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; rewrite <- rZCompInvol; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinInv in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZMinus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
rewrite (rZCompInvolList l0); auto.
apply Olistf with (eqA := eqRz); auto.
try exact rZltEqComp.
apply inMapComp; auto.
CaseEq (getMinId l l0).
intros x H' H'0 H'1 H'2 H'3 c H'4; red in |- *; intros H'5; Elimc H'5;
 intros H'5 H'6.
absurd (c = c); auto.
unfold getMinId in H'; apply getMinMin with (10 := H'); auto.
intros a0 b1 H'7; rewrite H'7; auto.
intros H' H'0 H'1 H'2 H'3.
unfold getMinId in H';
 case getMinNone with (8 := H') (a := rZPlus a) (b := rZPlus a); 
 auto.
intros a0 b1 H'4; rewrite H'4; auto.
Qed.

Theorem getEquivMinEq1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar1 S ->
 forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a.
apply rArrayStateDef2 with (Ar := Ar1); auto.
case (getEquivListProp1 Ar1 War1 (rZPlus a) (getEquivMin Ar1 Ar2 a)).
intros H'0; rewrite H'0; auto.
apply getEquivMinIn1; auto.
Qed.

Theorem getEquivMinEq2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar2 S ->
 forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a.
apply rArrayStateDef2 with (Ar := Ar2); auto.
case (getEquivListProp1 Ar2 War2 (rZPlus a) (getEquivMin Ar1 Ar2 a)).
intros H'0; rewrite H'0; auto.
rewrite getEquivMinSym; auto.
apply getEquivMinIn1; auto.
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
 Elimc H'2; intros H'2 H'3; auto.
absurd
 (In c (getEquivList Ar1 (rZPlus a)) /\ In c (getEquivList Ar2 (rZPlus a)));
 auto.
apply getEquivMinMin; auto.
split; auto.
case (getEquivListProp1 Ar1 War1 (rZPlus a) c).
intros H'4 H'5; apply H'5; auto.
apply rArrayStateDef1 with (S := S1); auto.
case (getEquivListProp1 Ar2 War2 (rZPlus a) c).
intros H'4 H'5; apply H'5; auto.
apply rArrayStateDef1 with (S := S2); auto.
Qed.

Theorem eqNotltRz : forall a b : rZ, rZlt a b -> a <> b.
intros a b H'; red in |- *; intros H'0; absurd (rZlt a b); auto.
rewrite H'0; auto.
Qed.
Hint Resolve eqNotltRz.

Theorem evalZMin :
 forall (Ar : rArray vM) (War : wellFormedArray Ar) (S : State),
 rArrayState Ar S ->
 forall a c : rZ, rZlt c (evalZ Ar a) -> ~ eqStateRz S a c.
intros Ar War S H'0 a c H'1; red in |- *; intros H'2.
absurd (evalZ Ar c = evalZ Ar a); auto.
generalize H'1 H'2; clear H'1 H'2.
case c; case a; simpl in |- *; intros a' c'; unfold evalN in |- *;
 CaseEq (rArrayGet vM Ar a'); CaseEq (rArrayGet vM Ar c'); 
 auto; intros r H' r0 H'1 H'2 H'3; red in |- *; intros H'4;
 (absurd (rVlt r c'); [ idtac | apply wfPd with (Ar := Ar) ]); 
 auto; try (rewrite H'4; unfold rVlt in |- *; apply rltAntiSym; auto);
 rewrite (rZCompInvol r); rewrite H'4; unfold rVlt in |- *; 
 apply rltAntiSym; generalize H'2; case r0; simpl in |- *; 
 auto.
apply rArrayStateDef1 with (S := S); auto.
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
case evalZMin with (3 := s) (S := S1); auto.
apply getEquivMinEq1; auto.
case getEquivMinMinEq with (5 := s) (S1 := S1) (S2 := S2); auto; split; auto.
apply rArrayStateDef2 with (Ar := Ar1); auto.
rewrite evalZInv; auto.
case (eqRzElim _ _ s); auto.
intros H'1; absurd (contradictory S1); auto.
red in |- *; intros H'; elim H'.
intros x H'2; absurd (evalZ Ar1 x = evalZ Ar1 (rZComp x)).
rewrite evalZComp; auto.
apply rArrayStateDef1 with (S := S1); auto.
red in |- *; auto.
exists (rZPlus a); auto.
apply eqStateRzTrans with (b := evalZ Ar1 (rZPlus a)); auto.
apply rArrayStateDef2 with (Ar := Ar1); auto.
rewrite evalZInv; auto.
apply eqStateInvInv; auto.
rewrite <- H'1; auto.
rewrite <- rZCompInvol; auto.
apply eqStateRzSym.
apply getEquivMinEq1; auto.
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
rewrite getEquivMinSym; auto.
apply getEquivIdR with (S1 := S2) (S2 := S1); auto.
Qed.

Theorem getMinInvInd :
 forall L1 L2 : list rZ,
 OlistRz L1 -> OlistRz L2 -> getMinInv L1 (map rZComp L2) = getMinId L1 L2.
intros L1 L2 Ol1 Ol2; auto.
cut (OlistRz (map rZComp L2));
 [ intros Ol2'
 | red in |- *; apply Olistf with (eqA := eqRz); auto; exact rZltEqComp ].
CaseEq (getMinInv L1 (map rZComp L2)); auto.
CaseEq (getMinId L1 L2); auto.
intros x H' x0 H'0.
case (rZltEDec x0 x); intros s; [ Casec s; intros s | idtac ].
absurd (x0 = x0); auto.
unfold getMinId in H'; apply getMinMin with (10 := H'); auto.
intros a b H'1; rewrite H'1; auto.
unfold getMinInv in H'0; apply geMinIn with (4 := H'0); auto.
unfold getMinInv in H'0; elim getMinComp with (4 := H'0); auto.
intros x1 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1.
apply inMapComp; rewrite <- rZCompInvol; auto.
absurd (x = rZComp (rZComp x)); auto.
unfold getMinInv in H'0; apply getMinMin with (10 := H'0); auto.
intros a b H'1; rewrite H'1; auto.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto.
apply in_map; auto.
unfold getMinId in H'; elim getMinComp with (4 := H'); auto.
intros x1 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1; auto.
rewrite (OlistIn _ rZlt eqRz) with (a := x0) (b := x) (L := L1); auto.
unfold getMinInv in H'0; apply geMinIn with (4 := H'0); auto.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto.
intros H' x H'0; absurd (x = x); auto.
unfold getMinId in H'; apply getMinNone with (8 := H'); auto.
intros a b H'1; rewrite H'1; auto.
unfold getMinInv in H'0; apply geMinIn with (4 := H'0); auto.
apply inMapComp; auto.
unfold getMinInv in H'0; elim getMinComp with (4 := H'0); auto.
intros x0 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1; rewrite <- rZCompInvol;
 auto.
CaseEq (getMinId L1 L2); auto.
intros x H' H'0.
absurd (x = rZComp (rZComp x)); auto.
unfold getMinInv in H'0; apply getMinNone with (8 := H'0); auto.
intros a b H'1; rewrite H'1; auto.
unfold getMinId in H'; apply geMinIn with (4 := H'); auto.
apply in_map; auto.
unfold getMinId in H'; elim getMinComp with (4 := H'); auto.
intros x0 H'1; Elimc H'1; intros H'1 H'2; rewrite H'1; auto.
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
 rewrite getEquivMinSym; auto.
Qed.

Theorem getRzMinIn1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rZ),
 In (getRzMin Ar1 Ar2 a) (getEquivList Ar1 a).
intros Ar1 Ar2 War1 War2 a; case a; intros a';
 generalize (getEquivMinIn1 Ar1 Ar2 War1 War2 a'); 
 simpl in |- *; auto.
case (getEquiv Ar1 a'); auto.
intros l b; case b; intros H'; auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
apply in_map; auto.
Qed.

Theorem getRzMinIn2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a : rZ),
 In (getRzMin Ar1 Ar2 a) (getEquivList Ar2 a).
intros Ar1 Ar2 War1 War2 a; case a; intros a';
 generalize (getEquivMinIn2 Ar1 Ar2 War1 War2 a'); 
 simpl in |- *; auto.
case (getEquiv Ar2 a'); auto.
intros l b; case b; intros H'; auto.
apply inMapComp; rewrite <- rZCompInvol; auto.
apply in_map; auto.
Qed.

Theorem getRzMinMin :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (a c : rZ),
 rZlt c (getRzMin Ar1 Ar2 a) ->
 ~ (In c (getEquivList Ar1 a) /\ In c (getEquivList Ar2 a)).
intros Ar1 Ar2 War1 War2 a c; case a; intros a';
 generalize (getEquivMinMin Ar1 Ar2 War1 War2 a'); 
 simpl in |- *; auto.
case (getEquiv Ar1 a'); case (getEquiv Ar2 a'); intros l b l0 b0; case b;
 case b0; simpl in |- *; intros H' H'0; red in |- *; 
 intros H'1; Elimc H'1; intros H'1 H'2;
 (case (H' (rZComp c)); [ apply rZltEqComp with (1 := H'0); auto | idtac ]);
 split; try apply in_map; auto; apply inMapComp; rewrite <- rZCompInvol; 
 auto.
Qed.

Theorem getRzMinEq1 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar1 S -> forall a : rZ, eqStateRz S a (getRzMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a; case a; intros a';
 generalize (getEquivMinEq1 Ar1 Ar2 War1 War2 S H' a'); 
 simpl in |- *; auto.
Qed.

Theorem getRzMinEq2 :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 rArrayState Ar2 S -> forall a : rZ, eqStateRz S a (getRzMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a; case a; intros a';
 generalize (getEquivMinEq2 Ar1 Ar2 War1 War2 S H' a'); 
 simpl in |- *; auto.
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
auto.
intros H'1 H'2; red in |- *; intros H'3; Elimc H'3; intros H'3 H'4.
case (H'1 (rZComp c));
 [ apply rZltEqComp with (1 := H'2); simpl in |- *; auto | idtac ]; 
 split; auto.
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
 auto.
cut (getEquivList Ar2 a = getEquivList Ar2 b);
 [ intros Eq2 | case (getEquivListProp4 Ar2 War2 S2 H'0 a b) ]; 
 auto.
case (rZltEDec (getRzMin Ar1 Ar2 a) (getRzMin Ar1 Ar2 b)); intros s;
 [ Casec s; intros s | idtac ].
case getRzMinMinEq with (5 := s) (S1 := S1) (S2 := S2); auto; split; auto.
apply eqStateRzTrans with (b := a); auto.
apply getRzMinEq1; auto.
apply eqStateRzTrans with (b := a); auto.
apply getRzMinEq2; auto.
case getRzMinMinEq with (5 := s) (S1 := S1) (S2 := S2); auto; split; auto.
apply eqStateRzTrans with (b := b); auto.
apply getRzMinEq1; auto.
apply eqStateRzTrans with (b := b); auto.
apply getRzMinEq2; auto.
apply OlistIn with (ltA := rZlt) (eqA := eqRz) (L := getEquivList Ar1 b);
 auto.
rewrite <- Eq1.
apply getRzMinIn1; auto.
apply getRzMinIn1; auto.
apply getEquivListProp2; auto.
Qed.

Theorem forallgetEquivgetRzMin :
 forall (Ar1 Ar2 : rArray vM) (War1 : wellFormedArray Ar1)
   (War2 : wellFormedArray Ar2) (S : State),
 (forall a : rNat, eqStateRz S (rZPlus a) (getEquivMin Ar1 Ar2 a)) ->
 forall a : rZ, eqStateRz S a (getRzMin Ar1 Ar2 a).
intros Ar1 Ar2 War1 War2 S H' a; case a; intros a'; simpl in |- *; auto.
apply eqStateRzInv with (1 := H' a'); auto.
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
red in |- *; auto.
intros i j H'2.
cut (eqStateRz S1 i j); [ intros Em1 | apply eqStateIncl with (2 := H'2) ];
 auto.
cut (eqStateRz S2 i j); [ intros Em2 | apply eqStateIncl with (2 := H'2) ];
 auto.
case (rZDec i j); intros Eqij; auto.
rewrite Eqij; auto.
apply eqStateRzTrans with (b := getRzMin Ar1 Ar2 i).
apply forallgetEquivgetRzMin; auto.
rewrite (getRzMinUnique Ar1 Ar2 War1 War2 S1 S2 H' H'0 i j); auto.
apply eqStateRzSym; auto.
apply forallgetEquivgetRzMin; auto.
Qed.
End inter.