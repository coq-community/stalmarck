
(****************************************************************************
                                                                           
          Stalmarck  :  doTriplets                                          
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Propagation as transitive closure of the one step propagation *)
Require Export doTriplet.
Require Import PolyListAux.
(* Reflexive transitive closure of doTriplet *)

Inductive doTripletsP : State -> list triplet -> State -> Prop :=
  | doTripletsRef :
      forall (S1 S2 : State) (L : list triplet),
      eqState S1 S2 -> doTripletsP S1 L S2
  | doTripletsTrans :
      forall (S1 S2 S3 : State) (L : list triplet) (t : triplet),
      In t L ->
      doTripletP S1 t S2 -> doTripletsP S2 L S3 -> doTripletsP S1 L S3.
Hint Resolve doTripletsRef.
(* It is compatible *)

Theorem doTripletsComp :
 forall (S1 S2 S3 S4 : State) (L : list triplet),
 doTripletsP S1 L S2 -> eqState S3 S1 -> eqState S4 S2 -> doTripletsP S3 L S4.
intros S1 S2 S3 S4 L H'; generalize S3 S4; elim H'; clear H' L S1 S2 S3 S4;
 auto.
intros S1 S2 L H' S3 S4 H'0 H'1.
apply doTripletsRef; auto.
apply eqStateTrans with (S2 := S1); auto.
apply eqStateTrans with (S2 := S2); auto.
intros S1 S2 S3 L t H' H'0 H'1 H'2 S0 S4 H'3 H'4.
elim (doTripletEqCompEx S1 S2 S0 t);
 [ intros S6 E; Elimc E; intros H'11 H'12 | idtac | idtac ]; 
 auto.
apply doTripletsTrans with (S2 := S6) (t := t); auto.
Qed.
(* Transitive *)

Theorem doTripletsRTrans :
 forall (S1 S2 S3 : State) (L : list triplet),
 doTripletsP S1 L S2 -> doTripletsP S2 L S3 -> doTripletsP S1 L S3.
intros S1 S2 S3 L H'; elim H'; auto.
intros S4 S5 L0 H'0 H'1.
apply doTripletsComp with (S1 := S5) (S2 := S3); auto.
intros S4 S5 S0 L0 t H'0 H'1 H'2 H'3 H'4.
apply doTripletsTrans with (S2 := S5) (t := t); auto.
Qed.
(*We only add equation *)

Theorem doTripletsUnionEx :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP S1 L S2 -> exists S3 : State, eqState S2 (unionState S3 S1).
intros S1 S2 L H'; elim H'; auto.
intros S3 S4 H'0 H'1; exists S3; auto.
apply eqStateTrans with (S2 := S3); auto.
red in |- *; split; auto.
intros S3 S4 S5 L0 t H'0 H'1 H'2 H'3.
elim (doTripletUnionEx S3 S4 t); [ intros S6 E | idtac ]; auto.
elim H'3; intros S7 E0.
exists (unionState S7 S6).
apply eqStateTrans with (S2 := unionState S7 S4); auto.
rewrite E; auto.
apply unionStateAssoc; auto.
Qed.
(* The state always grows *)

Theorem doTripletsIncl :
 forall (S1 S2 : State) (L : list triplet),
 doTripletsP S1 L S2 -> inclState S1 S2.
intros S1 S2 L H'.
elim (doTripletsUnionEx S1 S2 L); [ intros S3 E | idtac ]; auto.
apply inclStateEqStateComp with (S1 := S1) (S3 := unionState S3 S1); auto.
Qed.
(* It is a congruence *)

Theorem doTripletCongruent :
 forall (S1 S2 S3 : State) (L : list triplet),
 doTripletsP S1 L S2 -> doTripletsP (unionState S3 S1) L (unionState S3 S2).
intros S1 S2 S3 L H'; Elimc H'; clear S1 S2 L; auto.
intros S1 S2 S0 L t H' H'0 H'1 H'2.
apply doTripletsRTrans with (S2 := unionState S3 S2); auto.
elim (doTripletCongruentEx S1 S2 S3 t);
 [ intros S4 E; Elimc E; intros H'8 H'9 | idtac ]; 
 auto.
apply doTripletsRTrans with (S2 := S4); auto.
apply doTripletsTrans with (S2 := S4) (t := t); auto.
Qed.
(* It is monotone *)

Theorem doTripletsMonotoneEx :
 forall (S1 S2 S3 : State) (L : list triplet),
 doTripletsP S1 L S3 ->
 inclState S1 S2 -> exists S4 : State, doTripletsP S2 L S4 /\ inclState S3 S4.
intros S1 S2 S3 L H' H'0.
lapply (doTripletCongruent S1 S3 S2 L); [ intros H'5 | idtac ]; auto.
exists (unionState S2 S3); split; auto.
apply doTripletsComp with (S1 := unionState S2 S1) (S2 := unionState S2 S3);
 auto.
red in |- *; split; auto.
Qed.
(* It is confluent *)

Theorem doTripletsConftEx :
 forall (L : list triplet) (S1 S2 S3 : State),
 doTripletsP S1 L S2 ->
 doTripletsP S1 L S3 ->
 exists S4 : State, doTripletsP S2 L S4 /\ doTripletsP S3 L S4.
intros L S1 S2 S3 H' H'0.
elim (doTripletsUnionEx S1 S2 L); [ intros S4 E | idtac ]; auto.
elim (doTripletsUnionEx S1 S3 L); [ intros S5 E0 | idtac ]; auto.
exists (unionState S5 S2); split; auto.
apply doTripletsComp with (S1 := unionState S4 S1) (S2 := unionState S4 S3);
 auto.
apply doTripletCongruent; auto.
apply eqStateTrans with (S2 := unionState S5 (unionState S4 S1)); auto.
apply eqStateTrans with (S2 := unionState (unionState S5 S4) S1); auto.
apply unionStateAssoc; auto.
apply eqStateTrans with (S2 := unionState (unionState S4 S5) S1); auto.
apply eqStateTrans with (S2 := unionState S4 (unionState S5 S1)); auto.
apply eqStateTrans with (S2 := unionState (unionState S4 S5) S1); auto.
apply eqStateSym; auto.
apply unionStateAssoc; auto.
apply doTripletsComp with (S1 := unionState S5 S1) (S2 := unionState S5 S2);
 auto.
apply doTripletCongruent; auto.
Qed.
(* We don't loose realizability of memories if the triplets are realized *)

Theorem doTripletsRealizeStateEval :
 forall (f : rNat -> bool) (S1 S2 : State) (L : list triplet),
 realizeState f S1 ->
 doTripletsP S1 L S2 ->
 realizeTriplets f L -> f zero = true -> realizeState f S2.
intros f S1 S2 L H' H'0; generalize H'; elim H'0; auto.
intros S3 S4 L0 H'1 H'2 H'3 H'4.
apply realizeStateIncl with (S1 := S3); auto; inversion H'1; auto.
intros S3 S4 S5 L0 t H'1 H'2 H'3 H'4 H'5 H'6 H'7.
apply H'4; auto.
apply realizeStateEval with (2 := H'2); auto.
Qed.

Theorem doTripletsTermExAux :
 forall (L : list triplet) (S1 S2 : State),
 doTripletsP S1 L S2 ->
 forall t : triplet,
 In t L ->
 doTripletsP S1 (rem _ tripletDec t L) S2 \/
 (exists S3 : State,
    (exists S4 : State,
       doTripletsP S1 (rem _ tripletDec t L) S3 /\
       doTripletP S3 t S4 /\ doTripletsP S4 (rem _ tripletDec t L) S2)).
intros L S1 S2 H'; Elimc H'; clear L S1 S2; auto.
intros S1 S2 S3 L t H' H'0 H'1 H'2 t0 H'3.
case (tripletDec t t0); intros H.
elim (H'2 t);
 [ intros H'6
 | intros H'6; Elimc H'6; intros S0 E; Elimc E; intros S4 E; Elimc E;
    intros H'6 H'7; Elimc H'7; intros H'7 H'8
 | idtac ]; auto.
right; exists S1; exists S2; split; auto; split; auto.
rewrite <- H; auto.
rewrite <- H; auto.
right; exists S1; exists S2; split; auto; split; auto.
rewrite <- H; auto.
apply doTripletsRTrans with (S2 := S0); auto.
rewrite <- H; auto.
apply doTripletsComp with (S1 := S4) (S2 := S3); auto.
rewrite <- H; auto.
apply doTripletInvol with (t := t) (S1 := S1) (S2 := S2); auto.
apply doTripletsIncl with (L := rem triplet tripletDec t L); auto.
elim (H'2 t0);
 [ intros H'6
 | intros H'6; Elimc H'6; intros S0 E; Elimc E; intros S4 E; Elimc E;
    intros H'6 H'7; Elimc H'7; intros H'7 H'8
 | idtac ]; auto.
left.
apply doTripletsTrans with (S2 := S2) (t := t); auto.
right; exists S0; exists S4; split; [ idtac | split ]; auto.
apply doTripletsTrans with (S2 := S2) (t := t); auto.
Qed.
(* Once we have used  a triplet we can do without *)

Theorem doTripletsTermEx :
 forall (L : list triplet) (S1 S2 : State),
 doTripletsP S1 L S2 ->
 eqState S1 S2 \/
 (exists t : triplet,
    (exists S3 : State,
       In t L /\
       doTripletP S1 t S3 /\ doTripletsP S3 (rem _ tripletDec t L) S2)).
intros L S1 S2 H'; inversion H'; auto.
right; exists t; exists S3; split; try split; auto.
lapply (doTripletsTermExAux L S3 S2);
 [ intros H'3; elim (H'3 t);
    [ intros H'6
    | intros H'6; Elimc H'6; intros S5 E; Elimc E; intros S6 E; Elimc E;
       intros H'6 H'7; Elimc H'7; intros H'7 H'8
    | idtac ]
 | idtac ]; auto.
apply doTripletsRTrans with (S2 := S5); auto.
apply doTripletsComp with (S1 := S6) (S2 := S2); auto.
apply doTripletInvol with (t := t) (S1 := S1) (S2 := S3); auto.
apply doTripletsIncl with (L := rem triplet tripletDec t L); auto.
Qed.
(* The more we have triplets the more we can do *)

Theorem doTripletsInclList :
 forall (L1 L2 : list triplet) (S1 S2 : State),
 incl L1 L2 -> doTripletsP S1 L1 S2 -> doTripletsP S1 L2 S2.
intros L1 L2 S1 S2 H' H'0; generalize L2 H'; elim H'0; clear H'0 H' L2; auto.
intros S3 S4 S5 L0 t H' H'0 H'1 H'2 L2 H'3.
apply doTripletsTrans with (S2 := S4) (t := t); auto with datatypes.
Qed.