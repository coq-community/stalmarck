
(****************************************************************************
                                                                           
          Stalmarck  :  ltState                                            
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Define a well-founded order on state looking at the number of equation valid where
variables belong to a given list*)
Require Import state.
Require Import Arith.
Require Import stateDec.
Require Import Inverse_Image.
Require Import Compare.
Require Import Relation_Definitions.
Section lt.
Variable L : list rNat.

(* returns 0 if a=b 1 otherwise *)

Definition oneState (S : State) (a b : rZ) :=
  match eqStateRzDec S a b with
  | left _ => 0
  | right _ => 1
  end.
(* oneState is monotone for inclusion *)

Theorem oneStateLe :
 forall (a b : rZ) (S1 S2 : State),
 inclState S1 S2 -> oneState S2 a b <= oneState S1 a b.
intros a b S1 S2 H'; unfold oneState in |- *.
case (eqStateRzDec S1 a b); case (eqStateRzDec S2 a b); auto.
intros H'0 H'1; case H'0; auto.
Qed.
Hint Resolve oneStateLe.
(* It is strict if inclusion is strict *)

Theorem oneStateLt :
 forall (a b : rZ) (S1 S2 : State),
 inclState S1 S2 ->
 eqStateRz S2 a b -> ~ eqStateRz S1 a b -> oneState S2 a b < oneState S1 a b.
intros a b S1 S2 H'; unfold oneState in |- *.
case (eqStateRzDec S1 a b); case (eqStateRzDec S2 a b); auto.
intros H'0 H'1 H'2 H'3; case H'3; auto.
intros H'0 H'1 H'2 H'3; case H'0; auto.
intros H'0 H'1 H'2 H'3; case H'0; auto.
Qed.
Hint Resolve oneStateLt.

(* Returns 1 if +/- a = +/- b (if the state is not contradictory then 4), O otherwise *)

Definition oneStateAll (S : State) (a b : rNat) :=
  oneState S (rZPlus a) (rZPlus b) + oneState S (rZPlus a) (rZMinus b) +
  (oneState S (rZMinus a) (rZPlus b) + oneState S (rZMinus a) (rZMinus b)).

Theorem lePlusComp : forall a b c d : nat, a <= b -> c <= d -> a + c <= b + d.
intros a b c d H' H'0.
apply le_trans with (m := a + d); auto.
apply plus_le_compat_l; auto.
apply plus_le_compat_r; auto.
Qed.
Hint Resolve lePlusComp.
(* Monotonicity *)

Theorem oneStateAllLe :
 forall (a b : rNat) (S1 S2 : State),
 inclState S1 S2 -> oneStateAll S2 a b <= oneStateAll S1 a b.
intros a b S1 S2 H'; unfold oneStateAll in |- *; generalize oneStateLe;
 intros H'1; auto.
Qed.
Hint Resolve oneStateAllLe.

Theorem ltlePlusCompL :
 forall a b c d : nat, a < b -> c <= d -> a + c < b + d.
intros a b c d H' H'0; apply lt_le_trans with (m := b + c); auto.
apply plus_lt_compat_r; auto.
Qed.
Hint Resolve ltlePlusCompL.

Theorem ltlePlusCompR :
 forall a b c d : nat, a <= b -> c < d -> a + c < b + d.
intros a b c d H' H'0; apply le_lt_trans with (m := b + c); auto.
apply plus_lt_compat_l; auto.
Qed.
Hint Resolve ltlePlusCompR.
(* Strict monotony *)

Theorem oneStateAllLt :
 forall (a b : rZ) (S1 S2 : State),
 inclState S1 S2 ->
 eqStateRz S2 a b ->
 ~ eqStateRz S1 a b ->
 oneStateAll S2 (valRz a) (valRz b) < oneStateAll S1 (valRz a) (valRz b).
intros a b S1 S2 H'; unfold oneStateAll in |- *.
case a; case b; simpl in |- *; auto.
Qed.
Hint Resolve oneStateAllLt.
(* Adds oneStateAll for a list of variable *)

Fixpoint Nrel (S1 : State) (a : rNat) (L1 : list rNat) {struct L1} : nat :=
  match L1 with
  | nil => 0
  | b :: L2 => oneStateAll S1 a b + Nrel S1 a L2
  end.
(* Monotony *)

Theorem NrelLe :
 forall (L1 : list rNat) (a : rNat) (S1 S2 : State),
 inclState S1 S2 -> Nrel S2 a L1 <= Nrel S1 a L1.
intros L1 a S1 S2 H'; elim L1; simpl in |- *; auto.
Qed.
Hint Resolve NrelLe.
(* Strict monotony *)

Theorem NrelLt :
 forall (L1 : list rNat) (a : rNat) (b : rZ) (S1 S2 : State),
 inclState S1 S2 ->
 eqStateRz S2 (rZPlus a) b ->
 ~ eqStateRz S1 (rZPlus a) b ->
 In (valRz b) L1 -> Nrel S2 a L1 < Nrel S1 a L1.
intros L1; elim L1; simpl in |- *; auto.
intros a b S1 S2 H' H'0 H'1 H'2; elim H'2; auto.
intros a l H' a0 b S1 S2 H'0 H'1 H'2 H'3; Elimc H'3; intros H'3; auto.
rewrite H'3; auto.
apply ltlePlusCompL; auto.
change
  (oneStateAll S2 (valRz (rZPlus a0)) (valRz b) <
   oneStateAll S1 (valRz (rZPlus a0)) (valRz b)) in |- *; 
 auto.
apply ltlePlusCompR; auto.
apply H' with (b := b); auto.
Qed.
Hint Resolve NrelLt.
(* We do a product between two list*)

Fixpoint Ncount (S1 : State) (L2 L1 : list rNat) {struct L1} : nat :=
  match L1 with
  | nil => 0
  | a :: L3 => Nrel S1 a L2 + Ncount S1 L2 L3
  end.

Theorem NcountLe :
 forall (L1 L2 : list rNat) (S1 S2 : State),
 inclState S2 S1 -> Ncount S1 L2 L1 <= Ncount S2 L2 L1.
intros L1; elim L1; simpl in |- *; auto.
Qed.
Hint Resolve NcountLe.

Theorem NcountLt :
 forall (L1 L2 : list rNat) (a : rNat) (b : rZ),
 In a L1 ->
 In (valRz b) L2 ->
 forall S1 S2 : State,
 inclState S1 S2 ->
 eqStateRz S2 (rZPlus a) b ->
 ~ eqStateRz S1 (rZPlus a) b -> Ncount S2 L2 L1 < Ncount S1 L2 L1.
intros L1; elim L1; simpl in |- *; auto.
intros L2 a b H'; elim H'; auto.
intros a l H' L2 a0 b H'0; Elimc H'0; intros H'0; [ rewrite <- H'0 | idtac ];
 auto.
intros H'1 S1 S2 H'2 H'3 H'4.
apply ltlePlusCompL; auto.
apply NrelLt with (b := b); auto.
intros H'1 S1 S2 H'2 H'3 H'4.
apply ltlePlusCompR; auto.
apply H' with (a := a0) (b := b); auto.
Qed.

(* The value of a state is then the number of non-trivial equations that are not valid *)

Definition valState (S : State) := Ncount S L L.

Theorem vallStateLe :
 forall S1 S2 : State, inclState S1 S2 -> valState S2 <= valState S1.
unfold valState in |- *; auto.
Qed.
Hint Resolve vallStateLe.
(* This number decreases for strict inclusion *)

Theorem vallStateLt :
 forall a b : rZ,
 In (valRz a) L ->
 In (valRz b) L ->
 forall S1 S2 : State,
 inclState S1 S2 ->
 eqStateRz S2 a b -> ~ eqStateRz S1 a b -> valState S2 < valState S1.
intros a; case a; auto.
intros a' b H' H'0 S1 S2 H'1 H'2 H'3; unfold valState in |- *.
apply NcountLt with (a := a') (b := b); auto.
intros a' b H' H'0 S1 S2 H'1 H'2 H'3; unfold valState in |- *.
apply NcountLt with (a := a') (b := rZComp b); auto.
generalize H'0; case b; auto.
apply eqStateRzSym; auto.
Qed.

(* Using valState and lt we get our order *)

Definition ltState (S1 S2 : State) := valState S1 < valState S2.

Theorem ltStateTrans : transitive State ltState.
red in |- *; unfold ltState in |- *; auto.
intros S1 S2 S3 H' H'0.
apply lt_trans with (m := valState S2); auto.
Qed.

Theorem ltStateEqComp :
 forall S1 S2 S3 S4 : State,
 eqState S1 S3 -> eqState S2 S4 -> ltState S1 S2 -> ltState S3 S4.
unfold eqState, ltState in |- *.
intros S1 S2 S3 S4 H' H'0 H'1.
Elimc H'0; intros H'0 H'2.
Elimc H'; intros H' H'3.
apply lt_le_trans with (m := valState S2); auto.
apply le_lt_trans with (m := valState S1); auto.
Qed.

Theorem ltStateLt :
 forall a b : rZ,
 In (valRz a) L ->
 In (valRz b) L ->
 forall S1 S2 : State,
 inclState S1 S2 -> eqStateRz S2 a b -> ~ eqStateRz S1 a b -> ltState S2 S1.
intros a b H' H'0 S1 S2 H'1 H'2 H'3; red in |- *.
apply vallStateLt with (a := a) (b := b); auto.
Qed.
(* It is well founded *)

Theorem ltStateWf : well_founded ltState.
unfold ltState in |- *; apply wf_inverse_image with (B := nat); auto.
try exact lt_wf.
Qed.
End lt.