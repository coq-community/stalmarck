
(****************************************************************************
                                                                           
          Stalmarck  :    stateDec                                         
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Given a state, equality is decidable*)
Require Import List.
Require Export state.
(* To show that the equality is decidable we need a more `constructive' predicate
    than eqStateRz to define equality. We introduce eqConstrState and prove that
    it  has the same meaning than eqStateRz *)

Inductive eqConstrState : State -> rZ -> rZ -> Prop :=
  | eqConstrStateNil : forall a : rZ, eqConstrState nil a a
  | eqConstrStateTail :
      forall (a b : rZ) (p : rZ * rZ) (S : State),
      eqConstrState S a b -> eqConstrState (p :: S) a b
  | eqConstrStateComp1 :
      forall (a b c d : rZ) (S : State),
      eqConstrState S a b ->
      eqConstrState S c d -> eqConstrState ((b, c) :: S) a d
  | eqConstrStateComp2 :
      forall (a b c d : rZ) (S : State),
      eqConstrState S a c ->
      eqConstrState S b d -> eqConstrState ((b, c) :: S) a d
  | eqConstrStateComp3 :
      forall (a b c d : rZ) (S : State),
      eqConstrState S a (rZComp b) ->
      eqConstrState S (rZComp c) d -> eqConstrState ((b, c) :: S) a d
  | eqConstrStateComp4 :
      forall (a b c d : rZ) (S : State),
      eqConstrState S a (rZComp c) ->
      eqConstrState S (rZComp b) d -> eqConstrState ((b, c) :: S) a d
  | eqConstrStateContr :
      forall (a b c d : rZ) (S : State),
      eqConstrState S a (rZComp b) -> eqConstrState ((a, b) :: S) c d.
Hint Resolve eqConstrStateNil eqConstrStateTail eqConstrStateComp1
  eqConstrStateComp2 eqConstrStateComp3 eqConstrStateComp4 eqConstrStateContr.

Theorem eqConstrStateRef : forall (a : rZ) (S : State), eqConstrState S a a.
intros a L; elim L; auto.
Qed.
Hint Resolve eqConstrStateRef.

Theorem eqConstrStateIn :
 forall (a b : rZ) (S : State), In (a, b) S -> eqConstrState S a b.
intros a b L; elim L; simpl in |- *; auto.
intros H'; elim H'; auto.
intros a0 l H' H'0; Elimc H'0; intros H'0; [ rewrite H'0 | idtac ]; auto.
Qed.
Hint Resolve eqConstrStateIn.

Theorem eqConstrStateInv :
 forall (a b : rZ) (S : State),
 eqConstrState S a b -> eqConstrState S (rZComp a) (rZComp b).
intros a b S H'; elim H'; auto.
intros a0 b0 S0; repeat rewrite rZCompInv; auto.
intros a0 b0 S0; repeat rewrite rZCompInv; auto.
Qed.
Hint Resolve eqConstrStateInv.

Theorem eqConstrStateSym :
 forall (a b : rZ) (S : State), eqConstrState S a b -> eqConstrState S b a.
intros a b S H'; elim H'; auto.
Qed.
Hint Immediate eqConstrStateSym.

Theorem eqConstrStateSimpl :
 forall (a b : rZ) (S : State),
 eqConstrState S (rZComp a) b -> eqConstrState S a (rZComp b).
intros a b S H'; auto.
rewrite <- (rZCompInv a); auto.
Qed.
Hint Resolve eqConstrStateSimpl.

Theorem eqConstrStateTransConstr :
 forall S : State,
 (forall a b c : rZ, eqConstrState S a (rZComp a) -> eqConstrState S b c) /\
 (forall a b c : rZ,
  eqConstrState S a b -> eqConstrState S b c -> eqConstrState S a c).
intros L; elim L; auto.
split; intros a b c H'; inversion H'; auto.
generalize H1; case a; intros; discriminate.
intros p; case p.
intros e f l H'; Elimc H'; intros H'0 H'1.
split;
 [ intros a b c H'; inversion H'; generalize (H'0 a);
    generalize (fun b c : rZ => H'1 b a c);
    generalize (fun b c : rZ => H'1 b (rZComp a) c); 
    intros Hc0 Hc1 Hc2; auto 4
 | idtac ].
apply eqConstrStateContr; auto.
apply Hc1; auto.
rewrite <- (rZCompInv e); rewrite <- (rZCompInv a); apply eqConstrStateInv;
 auto.
intros a b c H'; inversion H'; intros H'2; inversion H'2; generalize (H'0 f);
 generalize (fun a c : rZ => H'1 a b c); intros Hc0 Hc1; 
 auto 4.
apply eqConstrStateTail.
apply H'1 with (b := e); auto.
apply eqConstrStateTail.
apply H'1 with (b := f); auto.
apply eqConstrStateTail; auto.
apply H'0 with (a := e); auto.
apply eqConstrStateTail; auto.
apply H'1 with (b := rZComp e); auto.
apply eqConstrStateTail; auto.
apply H'0 with (a := e); auto.
apply eqConstrStateTail; auto.
apply H'1 with (b := rZComp f); auto.
Qed.

Theorem eqConstrStateTrans :
 forall (S : State) (a b c : rZ),
 eqConstrState S a b -> eqConstrState S b c -> eqConstrState S a c.
intros S a b c H' H'0.
elim (eqConstrStateTransConstr S); intros H'2 H'3; lapply (H'3 a b c);
 [ intros H'7; lapply H'7; clear H'7; [ intros H'7; apply H'7 | idtac ]
 | idtac ]; auto.
Qed.

Theorem eqConstrStateContrGen :
 forall (S : State) (a b c : rZ),
 eqConstrState S a (rZComp a) -> eqConstrState S b c.
intros S a b c H'.
elim (eqConstrStateTransConstr S); intros H'1 H'2; lapply (H'1 a b c);
 [ intros H'6; apply H'6 | idtac ]; auto.
Qed.

Theorem eqStateRzPImpeqConstrState :
 forall (S : State) (a b : rZ), eqStateRz S a b -> eqConstrState S a b.
intros S a b H'; elim H'; auto.
intros a0 b0 c S0 H'0 H'1 H'2 H'3.
apply eqConstrStateTrans with (b := b0); auto.
intros a0 b0 c S0 H'0 H'1.
apply eqConstrStateContrGen with (a := a0); auto.
Qed.

Theorem eqStateRzTail :
 forall (a b : rZ) (S : State) (p : rZ * rZ),
 eqStateRz S a b -> eqStateRz (p :: S) a b.
intros a b S p H'; elim H'; auto.
intros a0 b0 S0 H'0.
apply eqStateRzIn; simpl in |- *; auto.
intros a0 b0 c S0 H'0 H'1 H'2 H'3.
apply eqStateRzTrans with (b := b0); auto.
intros a0 b0 c S0 H'0 H'1.
apply eqStateRzContr with (a := a0); auto.
Qed.
Hint Resolve eqStateRzTail.

Theorem eqConstrStateCons :
 forall (S : State) (a b : rZ), eqStateRz ((a, b) :: S) a b.
auto with datatypes.
Qed.
Hint Resolve eqConstrStateCons.

Theorem eqConstrStateImpeqStateRz :
 forall (S : State) (a b : rZ), eqConstrState S a b -> eqStateRz S a b.
intros S a b H'; elim H'; auto.
intros a0 b0 c d S0 H'0 H'1 H'2 H'3.
apply eqStateRzTrans with (b := b0); auto.
apply eqStateRzTrans with (b := c); auto.
intros a0 b0 c d S0 H'0 H'1 H'2 H'3.
apply eqStateRzTrans with (b := c); auto.
apply eqStateRzTrans with (b := b0); auto.
intros a0 b0 c d S0 H'0 H'1 H'2 H'3.
apply eqStateRzTrans with (b := rZComp b0); auto.
apply eqStateRzTrans with (b := rZComp c); auto.
intros a0 b0 c d S0 H'0 H'1 H'2 H'3.
apply eqStateRzTrans with (b := rZComp c); auto.
apply eqStateRzTrans with (b := rZComp b0); auto.
intros a0 b0 c d S0 H'0 H'1.
apply eqStateRzContr with (a := b0); auto.
apply eqStateRzTrans with (b := a0); auto.
Qed.
Hint Immediate eqStateRzPImpeqConstrState eqConstrStateImpeqStateRz.
(* To check equality for eqConstrState is quite direct *)

Definition eqConstrStateDec :
  forall (S : State) (a b : rZ),
  {eqConstrState S a b} + {~ eqConstrState S a b}.
intros L; elim L; simpl in |- *; auto.
intros a b; case (rZDec a b); intros Eqab.
rewrite <- Eqab; auto.
right; red in |- *; intros H'.
apply Eqab; inversion H'; auto.
intros p l H' a b.
case (H' a b); intros EqabL; auto.
case p.
intros c d.
case (H' a (rZComp a)); intros Eqama; auto.
left; apply eqConstrStateContrGen with (a := a); auto.
case (H' c (rZComp d)); intros Eqcmd; auto.
case (H' c d); intros Eqcd; auto.
case (H' a b); intros Eqab; auto.
right; red in |- *; intros H'0; apply Eqab; auto.
apply eqStateRzPImpeqConstrState.
apply eqStateIncl with (S1 := addEq (c, d) l); auto.
case (H' a c); intros Eqac; auto.
case (H' d b); intros EqdbL; auto.
right; red in |- *; intros H'0; inversion H'0; auto.
case Eqcd; apply eqConstrStateTrans with (b := a); auto.
case Eqama; apply eqConstrStateTrans with (b := c); auto.
case Eqcmd; apply eqConstrStateTrans with (b := a); auto.
case (H' a d); intros Eqad; auto.
case (H' c b); intros Eqcb; auto.
right; red in |- *; intros H'0; inversion H'0; auto.
case Eqcmd; apply eqConstrStateTrans with (b := rZComp a); auto.
case Eqama; apply eqConstrStateTrans with (b := rZComp d); auto.
case (H' a (rZComp c)); intros Eqamc; auto.
case (H' (rZComp d) b); intros Eqmdb; auto.
right; red in |- *; intros H'0; inversion H'0; auto.
case Eqcd; apply eqConstrStateTrans with (b := rZComp a); auto.
apply eqConstrStateSym; auto.
case (H' a (rZComp d)); intros Eqamd; auto.
case (H' (rZComp c) b); intros Eqmcb; auto.
right; red in |- *; intros H'0; inversion H'0; auto.
right; red in |- *; intros H'0; inversion H'0; auto.
Defined.
(* So we can lift the previous definition for eqStateRz *)

Definition eqStateRzDec :
  forall (S : State) (a b : rZ), {eqStateRz S a b} + {~ eqStateRz S a b}.
intros S a b; case (eqConstrStateDec S a b); auto.
Defined.
(* Check if a state is contradictory *)

Definition eqStateRzContrDec :
  forall S : State,
  {(forall a b : rZ, eqStateRz S a b)} +
  {~ (forall a b : rZ, eqStateRz S a b)}.
intros S; case S; auto.
right; red in |- *; intros H'; auto.
cut (eqConstrState nil (rZPlus zero) (rZMinus zero)); auto.
intros H'0; inversion H'0; auto.
intros p S'; case p; intros a b.
case (eqStateRzDec ((a, b) :: S') a (rZComp a)); auto.
intros H'; left; intros a0 b0.
apply eqStateRzContr with (a := a); auto.
Defined.
(* Check the inclusion of two states *)

Definition inclStateDec :
  forall S1 S2 : State, {inclState S1 S2} + {~ inclState S1 S2}.
intros S1; elim S1; auto.
intros S2; left; red in |- *; auto with datatypes; intros i j H'1; elim S2;
 auto.
intros a; case a; auto.
intros a' b' l H' S2.
elim (H' S2); intros H'1; auto.
case (eqStateRzDec S2 a' b'); intros EqS2; auto.
left; change (inclState (addEq (a', b') l) S2) in |- *; auto.
right; red in |- *; intros H'0; case H'1; auto.
apply inclStateTrans with (S2 := addEq (a', b') l); auto.
Defined.
(* Check if two states are equal *)

Definition eqStateDec :
  forall S1 S2 : State, {eqState S1 S2} + {~ eqState S1 S2}.
intros S1 S2.
case (inclStateDec S1 S2); intros inclS1S2; auto.
case (inclStateDec S2 S1); intros inclS2S1; auto.
left; red in |- *; auto.
right; red in |- *; intros H'; red in H'; case inclS2S1; auto.
elim H'; intros H'0 H'1; auto.
right; red in |- *; intros H'; case inclS1S2; auto.
red in H'; elim H'; auto.
Defined.
(* Same as incStateDec but give a witness if there is not inclusion *)

Definition inclStateDecBis :
  forall S1 S2 : State,
  {inclState S1 S2} +
  {(exists a : rZ, (exists b : rZ, eqStateRz S1 a b /\ ~ eqStateRz S2 a b))}.
intros S1; elim S1; auto.
intros S2; left; auto.
red in |- *; intros i j H'1; elim S2; auto.
intros a; case a; auto.
intros a' b' l H' S2.
elim (H' S2); intros H'1; auto.
case (eqStateRzDec S2 a' b'); intros EqS2; auto.
left; change (inclState (addEq (a', b') l) S2) in |- *; auto.
right; exists a'; exists b'; split; auto.
right.
elim H'1; intros a0 E; elim E; intros b E0; elim E0; intros H'0 H'2;
 try exact H'0; clear E0 E H'1.
exists a0; exists b; split; auto.
Defined.