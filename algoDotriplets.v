
(****************************************************************************
                                                                           
          Stalmarck  :  algoDotriplets                                  
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Implement the propagation*)
Require Export algoDotriplet.
Require Export trace.
Require Export doTriplets.
Section algos.
(* To return 4 elements *)

Inductive Quatuor (A B C D : Set) : Set :=
    quatuor : A -> B -> C -> D -> Quatuor A B C D.

(* The propagation returns
          - the new array
          - a boolean that says if we have reached a contradiction 
          -  the diff list
          -  the trace *)

Definition mbDT := Quatuor (rArray vM) bool (list rZ) Trace.

Definition mbDTOp := quatuor (rArray vM) bool (list rZ) Trace.

(* append two trace removing useless emptyTrace *)

Definition appTrace (t1 : Trace) t2 :=
  match t1, t2 with
  | emptyTrace, _ => t2
  | _, emptyTrace => t1
  | _, _ => seqTrace t1 t2
  end.
(* Given a list of triplets we try the propagation on all of them *)

Fixpoint doTripletFs (L : list triplet) : rArray vM -> mbDT :=
  fun Ar =>
  match L with
  | nil => quatuor _ _ _ _ Ar false nil emptyTrace
  | a :: L1 =>
      match doTripletF Ar a with
      | None => doTripletFs L1 Ar
      | Some (triple Ar' true L') =>
          quatuor _ _ _ _ Ar' true L' (tripletTrace a)
      | Some (triple Ar' b' nil) => doTripletFs L1 Ar'
      | Some (triple Ar' b' L') =>
          match doTripletFs L1 Ar' with
          | quatuor Ar'' b'' L'' T'' =>
              quatuor _ _ _ _ Ar'' b'' (appendRz L' L'')
                (seqTrace (tripletTrace a) T'')
          end
      end
  end.
(* evaluation of traces is compatible with equality *)

Theorem evalTraceEq :
 forall (S1 S2 S3 S4 : State) (T : Trace),
 evalTrace S1 T S2 -> eqState S1 S3 -> eqState S2 S4 -> evalTrace S3 T S4.
intros S1 S2 S3 S4 T H'; generalize S3 S4; clear S3 S4; elim H'; auto.
intros S3 S4 H'0 S5 S6 H'1 H'2.
apply emptyTraceEval; auto.
apply eqStateTrans with S3; auto.
apply eqStateTrans with S4; auto.
intros t S3 S4 S5 H'0 H'1 S6 S7 H'2 H'3.
apply evalTraceComp with (S1 := S3) (S2 := S5); auto.
apply tripletTraceEval with (S2 := S4); auto.
intros t1 t2 S3 S4 S5 H'0 H'1 H'2 H'3 S6 S7 H'4 H'5.
apply seqTraceEval with (S2 := S4); auto; auto.
intros t1 t2 a b S3 S4 S5 S6 H'0 H'1 H'2 H'3 H'4 S7 S8 H'5 H'6.
apply dilemmaTraceEval with (S2 := S4) (S3 := S5); auto.
apply eqStateTrans with S6; auto.
Qed.
(* two identical arrays give identical states *)

Theorem eqStateRarray :
 forall (Ar Ar' : rArray vM) (S S' : State),
 rArrayState Ar S ->
 rArrayState Ar' S' ->
 (forall e : rNat, rArrayGet vM Ar' e = rArrayGet vM Ar e) -> eqState S S'.
intros Ar Ar' S S' H' H'0 H'1; red in |- *; split.
red in |- *; intros i j H; case (H'0 i j); intros H1 H2; apply H2.
repeat rewrite <- (rArrayGetEvalZ Ar Ar'); auto.
case (H' i j); auto.
red in |- *; intros i j H; case (H' i j); intros H1 H2; apply H2.
repeat rewrite <- (rArrayGetEvalZ Ar' Ar); auto.
case (H'0 i j); auto.
Qed.

Definition FStalCorrect (Ar : rArray vM) (Lt : list triplet) 
  (S : State) (res : mbDT) :=
  wellFormedArray Ar ->
  rArrayState Ar S ->
  match res with
  | quatuor Ar' false L T =>
      wellFormedArray Ar' /\
      (exists S' : State,
         stalmarckP S Lt S' /\ rArrayState Ar' S' /\ evalTrace S T S') /\
      OlistRz L /\
      (forall e : rNat,
       ~ InRz (rZPlus e) L -> rArrayGet _ Ar' e = rArrayGet _ Ar e)
  | quatuor Ar' true L T =>
      exists S' : State,
        stalmarckP S Lt S' /\ contradictory S' /\ evalTrace S T S'
  end.

Theorem stalmarckInclList :
 forall (L1 L2 : list triplet) (S1 S2 : State),
 incl L1 L2 -> stalmarckP S1 L1 S2 -> stalmarckP S1 L2 S2.
intros L1 L2 S1 S2 H' H'0; generalize L2 H'; clear H' L2; elim H'0; auto.
intros S3 S4 L H' L2 H'1.
apply stalmarckPref.
apply doTripletsInclList with (L1 := L); auto.
intros a b S3 S4 S5 S6 L H' H'1 H'2 H'3 H'4 L2 H'5.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S4) (S3 := S5); auto.
intros S3 S4 S5 L H' H'1 H'2 H'3 L2 H'4.
apply stalmarckTrans with (S2 := S4); auto.
Qed.
(* Propagation is correct *)

Theorem doTripletFsCorrect :
 forall (Ar : rArray vM) (Lt : list triplet) (S : State),
 FStalCorrect Ar Lt S (doTripletFs Lt Ar).
intros Ar Lt; generalize Ar; clear Ar; elim Lt; unfold FStalCorrect in |- *;
 simpl in |- *.
intros Ar S H' H'0; repeat (split; auto).
exists S; split; auto.
red in |- *; apply OlistNil; auto.
intros a l H' Ar S H'0 H'1.
generalize (doTripletFCorrect Ar a S H'0 H'1).
case (doTripletF Ar a).
intros x; case x.
intros Ar' b' L'; case b'.
intros H'2; Elimc H'2; intros S' E; Elimc E; intros H'2 H'3.
case L'.
exists S'; repeat (split; auto).
apply stalmarckPref.
apply doTripletsTrans with (S2 := S') (t := a); auto.
simpl in |- *; auto.
apply tripletTraceEval with (S2 := S'); auto.
intros a1 l1.
exists S'; repeat (split; auto).
apply stalmarckPref.
apply doTripletsTrans with (S2 := S') (t := a); auto.
simpl in |- *; auto.
apply tripletTraceEval with (S2 := S'); auto.
intros H'2; Elimc H'2; intros H'2 H'3; Elimc H'3; intros H'3 H'4; Elimc H'4;
 intros H'4 H'5.
Elimc H'3; intros S' E; Elimc E; intros H'3 H'6.
generalize (H' Ar' S' H'2 H'6).
case (doTripletFs l Ar').
intros Ar'' b'' L'' T''; case b''.
intros H'7; Elimc H'7; intros S'0 E; Elimc E; intros H'7 H'8; Elimc H'8;
 intros H'8 H'9.
generalize H'5; clear H'5; case L'.
intros H'5; exists S'0; repeat (split; auto).
apply stalmarckTrans with (S2 := S'); auto.
apply stalmarckPref.
apply doTripletsTrans with (S2 := S') (t := a); auto.
simpl in |- *; auto.
apply stalmarckTrans with (S2 := S'0); auto.
apply stalmarckInclList with (L1 := l); auto with datatypes.
apply evalTraceEq with (S1 := S') (S2 := S'0); auto.
apply eqStateRarray with (Ar := Ar') (Ar' := Ar); auto.
intros e; rewrite H'5; auto with datatypes.
red in |- *; intros H'10; inversion H'10; auto.
intros r l0 H'10; exists S'0; repeat (split; auto).
apply stalmarckTrans with (S2 := S'); auto.
apply stalmarckPref; auto.
apply doTripletsTrans with (S2 := S') (t := a); auto with datatypes.
apply stalmarckInclList with (L1 := l); auto with datatypes.
apply seqTraceEval with (S2 := S'); auto.
apply tripletTraceEval with (S2 := S'); auto.
intros H'7; Elimc H'7; intros H'7 H'8; Elimc H'8; intros H'8 H'9; Elimc H'9;
 intros H'9 H'10.
Elimc H'8; intros S'0 E; Elimc E; intros H'8 H'11; Elimc H'11;
 intros H'11 H'12.
repeat (split; auto).
generalize H'5 H'4; clear H'5 H'4; case L'.
intros H'13 H'14; repeat (split; auto).
exists S'0; repeat (split; auto).
apply stalmarckTrans with (S2 := S'); auto.
apply stalmarckPref; auto.
apply doTripletsTrans with (S2 := S') (t := a); auto with datatypes.
apply stalmarckInclList with (L1 := l); auto with datatypes.
apply evalTraceEq with (S1 := S') (S2 := S'0); auto.
apply eqStateRarray with (Ar := Ar') (Ar' := Ar); auto.
intros e; rewrite H'13; auto with datatypes.
red in |- *; intros H'15; inversion H'15; auto.
intros e H'15; rewrite <- H'13; auto.
red in |- *; intros H'16; inversion H'16; auto.
intros r l0 H'4 H'5; repeat (split; auto).
exists S'0; repeat (split; auto).
apply stalmarckTrans with (S2 := S'); auto.
apply stalmarckPref; auto.
apply doTripletsTrans with (S2 := S') (t := a); auto with datatypes.
apply stalmarckInclList with (L1 := l); auto with datatypes.
apply seqTraceEval with (S2 := S'); auto.
apply tripletTraceEval with (S2 := S'); auto.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto.
try exact rZltEqComp.
intros e H'13.
rewrite H'10.
apply H'4; auto.
Contradict H'13; auto.
cut (InclEq _ eqRz (r :: l0) (appendf _ rZlt eqRz rZltEDec (r :: l0) L'')).
intros H'14; inversion H'14; red in |- *; auto.
apply appendfInclEq1; auto.
Contradict H'13; auto.
cut (InclEq _ eqRz L'' (appendf _ rZlt eqRz rZltEDec (r :: l0) L'')).
intros H'14; inversion H'14; red in |- *; auto.
apply appendfInclEq2; auto.
intros H'2; auto.
generalize (H' Ar S H'0 H'1).
case (doTripletFs l Ar).
intros Ar' b' L' T'; case b'.
intros H'3; Elimc H'3; intros S' E; Elimc E; intros H'3 H'4; Elimc H'4;
 intros H'4 H'5.
exists S'; repeat (split; auto).
apply stalmarckInclList with (L1 := l); auto with datatypes.
intros H'3; Elimc H'3; intros H'3 H'4; Elimc H'4; intros H'4 H'5; Elimc H'5;
 intros H'5 H'6.
Elimc H'4; intros S' E; Elimc E; intros H'4 H'7; Elimc H'7; intros H'7 H'10.
repeat (split; auto).
exists S'; repeat (split; auto).
apply stalmarckInclList with (L1 := l); auto with datatypes.
Qed.
Variable getT : rZ -> list triplet.
Variable LL : list triplet.
Hypothesis getTCorrect : forall a : rZ, incl (getT a) LL.
(* Given a diff listed, try all the triplets related to these variables *)

Fixpoint doTripletsR (L : list rZ) : rArray vM -> mbDT :=
  fun Ar =>
  match L with
  | nil => quatuor _ _ _ _ Ar false nil emptyTrace
  | a :: L1 =>
      match doTripletFs (getT a) Ar with
      | quatuor Ar' true L' T' => quatuor _ _ _ _ Ar' true L' T'
      | quatuor Ar' b' L' T' =>
          match doTripletsR L1 Ar' with
          | quatuor Ar'' b'' L'' T'' =>
              quatuor _ _ _ _ Ar'' b'' (appendRz L' L'') (appTrace T' T'')
          end
      end
  end.

Theorem appTraceCorrect :
 forall (S1 S2 S3 : State) (T1 T2 : Trace),
 evalTrace S1 T1 S2 -> evalTrace S2 T2 S3 -> evalTrace S1 (appTrace T1 T2) S3.
intros S1 S2 S3 T1 T2 H' H'0; inversion_clear H'; inversion_clear H'0;
 simpl in |- *; auto.
apply evalTraceEq with (S1 := S2) (S2 := S3); auto.
apply evalTraceEq with (S1 := S2) (S2 := S3); auto.
apply tripletTraceEval with (S2 := S4); auto.
apply evalTraceEq with (S1 := S2) (S2 := S3); auto.
apply seqTraceEval with (S2 := S4); auto.
apply evalTraceEq with (S1 := S2) (S2 := S3); auto.
apply dilemmaTraceEval with (S2 := S4) (S3 := S5); auto.
apply evalTraceEq with (S1 := S1) (S2 := S4); auto.
apply tripletTraceEval with (S2 := S4); auto.
apply eqStateTrans with S2; auto.
apply seqTraceEval with (S2 := S4); auto.
apply tripletTraceEval with (S2 := S4); auto.
apply evalTraceEq with (S1 := S2) (S2 := S5); auto.
apply tripletTraceEval with (S2 := S5); auto.
apply seqTraceEval with (S2 := S4); auto.
apply tripletTraceEval with (S2 := S4); auto.
apply seqTraceEval with (S2 := S5); auto.
apply evalTraceEq with (S1 := S2) (S2 := S5); auto.
apply seqTraceEval with (S2 := S2); auto.
apply tripletTraceEval with (S2 := S4); auto.
apply dilemmaTraceEval with (S2 := S5) (S3 := S6); auto.
apply seqTraceEval with (S2 := S4); auto.
apply evalTraceEq with (S1 := S4) (S2 := S2); auto.
apply seqTraceEval with (S2 := S2); auto.
apply seqTraceEval with (S2 := S4); auto.
apply tripletTraceEval with (S2 := S5); auto.
apply seqTraceEval with (S2 := S2); auto.
apply seqTraceEval with (S2 := S4); auto.
apply seqTraceEval with (S2 := S5); auto.
apply seqTraceEval with (S2 := S2); auto.
apply seqTraceEval with (S2 := S4); auto.
apply dilemmaTraceEval with (S2 := S5) (S3 := S6); auto.
apply dilemmaTraceEval with (S2 := S4) (S3 := S5); auto.
apply eqStateTrans with S2; auto.
apply seqTraceEval with (S2 := S2); auto.
apply dilemmaTraceEval with (S2 := S4) (S3 := S5); auto.
apply tripletTraceEval with (S2 := S6); auto.
apply seqTraceEval with (S2 := S2); auto.
apply dilemmaTraceEval with (S2 := S4) (S3 := S5); auto.
apply seqTraceEval with (S2 := S6); auto.
apply seqTraceEval with (S2 := S2); auto.
apply dilemmaTraceEval with (S2 := S4) (S3 := S5); auto.
apply dilemmaTraceEval with (S2 := S6) (S3 := S7); auto.
Qed.

Theorem FStalCorrect0 :
 forall (Ar : rArray vM) (S : State),
 FStalCorrect Ar LL S
   (quatuor (rArray vM) bool (list rZ) Trace Ar false nil emptyTrace).
intros Ar S; repeat (split; auto).
exists S; repeat (split; auto).
red in |- *; apply OlistNil; auto.
Qed.

Theorem FStalCorrectIncl :
 forall (Ar : rArray vM) (S : State) (L1 L2 : list triplet) (M : mbDT),
 incl L1 L2 -> FStalCorrect Ar L1 S M -> FStalCorrect Ar L2 S M.
intros Ar S L1 L2 M; case M; unfold FStalCorrect in |- *; simpl in |- *; auto.
intros Ar' b'; case b'; auto.
intros H' t H'0 H'1 H'2 H'3.
elim H'1;
 [ intros S' E; elim E; intros H'6 H'7; elim H'7; intros H'8 H'9;
    clear H'7 E H'1
 | clear H'1
 | clear H'1 ]; auto.
exists S'; repeat (split; auto).
apply stalmarckInclList with (L1 := L1); auto.
intros l t H' H'0 H'1 H'2.
elim H'0;
 [ intros H'5 H'6; elim H'6; intros H'7 H'8; elim H'8; intros H'9 H'10;
    clear H'8 H'6 H'0
 | clear H'0
 | clear H'0 ]; auto.
elim H'7; intros S' E; elim E; intros H'0 H'3; elim H'3; intros H'4 H'6;
 clear H'3 E H'7; auto.
repeat (split; auto).
exists S'; repeat (split; auto).
apply stalmarckInclList with (L1 := L1); auto.
Qed.

Theorem FStalCorrectComp :
 forall (Ar Ar' Ar'' : rArray vM) (b'' : bool) (L' L'' : list rZ)
   (T' T'' : Trace) (S : State),
 (forall S : State,
  FStalCorrect Ar' LL S
    (quatuor (rArray vM) bool (list rZ) Trace Ar'' b'' L'' T'')) ->
 FStalCorrect Ar LL S
   (quatuor (rArray vM) bool (list rZ) Trace Ar' false L' T') ->
 FStalCorrect Ar LL S
   (quatuor (rArray vM) bool (list rZ) Trace Ar'' b'' 
      (appendRz L' L'') (appTrace T' T'')).
intros Ar Ar' Ar'' b'' L' L'' T' T''; unfold FStalCorrect in |- *;
 simpl in |- *.
case b''; auto.
intros S H' H'0 H'1 H'2.
elim H'0;
 [ intros H'5 H'6; elim H'6; intros H'7 H'8; elim H'8; intros H'9 H'10;
    clear H'8 H'6 H'0
 | clear H'0
 | clear H'0 ]; auto.
elim H'7; intros S' E; elim E; intros H'0 H'3; elim H'3; intros H'4 H'6;
 clear H'3 E H'7; auto.
elim (H' S');
 [ intros S'0 E; elim E; intros H'11 H'12; elim H'12; intros H'13 H'14;
    clear H'12 E
 | idtac
 | idtac ]; auto.
exists S'0; repeat (split; auto).
apply stalmarckTrans with (S2 := S'); auto.
apply appTraceCorrect with (S2 := S'); auto.
intros S H' H'0 H'1 H'2.
elim H'0;
 [ intros H'5 H'6; elim H'6; intros H'7 H'8; elim H'8; intros H'9 H'10;
    clear H'8 H'6 H'0
 | clear H'0
 | clear H'0 ]; auto.
elim H'7; intros S' E; elim E; intros H'0 H'3; elim H'3; intros H'4 H'6;
 clear H'3 E H'7; auto.
elim (H' S');
 [ intros H'11 H'12; elim H'12; intros H'13 H'14; elim H'14; intros H'15 H'16;
    clear H'14 H'12
 | idtac
 | idtac ]; auto.
elim H'13; intros S'0 E; elim E; intros H'3 H'7; elim H'7; intros H'8 H'12;
 clear H'7 E H'13.
repeat (split; auto).
exists S'0; repeat (split; auto).
apply stalmarckTrans with (S2 := S'); auto.
apply appTraceCorrect with (S2 := S'); auto.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto.
try exact rZltEqComp.
intros e H'14.
rewrite H'16.
apply H'10; auto.
Contradict H'14; auto.
cut (InclEq _ eqRz L' (appendf _ rZlt eqRz rZltEDec L' L'')).
intros H'7; inversion H'7; red in |- *; auto.
apply appendfInclEq1; auto.
Contradict H'14; auto.
cut (InclEq _ eqRz L'' (appendf _ rZlt eqRz rZltEDec L' L'')).
intros H'7; inversion H'7; red in |- *; auto.
apply appendfInclEq2; auto.
Qed.

Theorem doTripletFsRCorrect :
 forall (Ar : rArray vM) (Lt : list rZ) (S : State),
 FStalCorrect Ar LL S (doTripletsR Lt Ar).
intros Ar Lt; generalize Ar; clear Ar; elim Lt; simpl in |- *.
exact FStalCorrect0.
intros a l H' Ar S; generalize (doTripletFsCorrect Ar (getT a) S).
case (doTripletFs (getT a) Ar); auto.
intros Ar' b' L' T'; case b'.
intros H'0.
apply FStalCorrectIncl with (L1 := getT a); auto.
generalize (H' Ar').
case (doTripletsR l Ar').
intros r b l0 t H'0 H'1.
apply FStalCorrectComp with (Ar' := Ar'); auto.
apply FStalCorrectIncl with (L1 := getT a); auto.
Qed.
(* we try the propagation n times, if n is big enough this ensure that
    we will reach a point where no new information is gained *)

Fixpoint doTripletsN (L : list rZ) (n : nat) {struct n} :
 rArray vM -> mbDT :=
  fun Ar =>
  match doTripletsR L Ar with
  | quatuor Ar' true L' T' => quatuor _ _ _ _ Ar' true L' T'
  | quatuor Ar' false nil T => quatuor _ _ _ _ Ar' false nil T
  | quatuor Ar' b' L' T' =>
      match n with
      | O => quatuor _ _ _ _ Ar' b' L' T'
      | S n =>
          match doTripletsN L' n Ar' with
          | quatuor Ar'' b'' L'' T'' =>
              quatuor _ _ _ _ Ar'' b'' (appendRz L' L'') (appTrace T' T'')
          end
      end
  end.

Theorem doTripletFsNCorrect :
 forall (n : nat) (Ar : rArray vM) (Lt : list rZ) (S : State),
 FStalCorrect Ar LL S (doTripletsN Lt n Ar).
intros n; elim n; simpl in |- *; auto.
intros Ar Lt S; generalize (doTripletFsRCorrect Ar Lt S).
case (doTripletsR Lt Ar).
intros Ar' b' L' T'; case b'; auto.
case L'; auto.
intros n0 H' Ar Lt S; generalize (doTripletFsRCorrect Ar Lt S).
case (doTripletsR Lt Ar).
intros Ar' b' L' T'; case b'; auto.
case L'; auto.
intros r l H'0; generalize (H' Ar' (r :: l)).
case (doTripletsN (r :: l) n0 Ar'); auto.
intros r0 b l0 t H'1.
apply FStalCorrectComp with (Ar' := Ar'); auto.
Qed.
End algos.
