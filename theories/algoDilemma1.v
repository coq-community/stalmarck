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
                                                                           
          Stalmarck  :   algoDilemma1                                       
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
Implement the dilemma with one variable*)
Require Export algoDotriplets.
Require Export interImplement2.
Require Export stalmarck.
Section odilemma1.
Variable getT : rZ -> list triplet.
Variable LL : list triplet.
Hypothesis getTCorrect : forall a : rZ, incl (getT a) LL.

(* Avoid constructing sequence of empty traces *)

Definition dT (a b : rZ) (T1 T2 : Trace) :=
  match T1, T2 with
  | emptyTrace, emptyTrace => emptyTrace
  | _, _ => dilemmaTrace a b T1 T2
  end.

Theorem dTCorrect :
 forall (t1 t2 : Trace) (a b : rZ) (S1 S2 S3 S4 : State),
 evalTrace (addEq (a, b) S1) t1 S2 ->
 evalTrace (addEq (a, rZComp b) S1) t2 S3 ->
 eqState (interState S2 S3) S4 -> evalTrace S1 (dT a b t1 t2) S4.
intros t1; case t1; simpl in |- *; auto with stalmarck.
intros t1'; case t1'; simpl in |- *; auto with stalmarck.
intros a b S1 S2 S3 S4 H' H'0 H'1.
apply emptyTraceEval; auto with stalmarck.
apply eqStateTrans with (2 := H'1).
inversion_clear H'.
inversion_clear H'0.
apply
 eqStateTrans with (interState (addEq (a, b) S1) (addEq (a, rZComp b) S1)).
apply CompInterR; auto with stalmarck.
apply interStateEq; auto with stalmarck.
intros t a b S1 S2 S3 S4 H' H'0 H'1.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
intros t t0 a b S1 S2 S3 S4 H' H'0 H'1.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
intros r r0 t t0 a b S1 S2 S3 S4 H' H'0 H'1.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
intros t t2 a b S1 S2 S3 S4 H' H'0 H'1.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
intros t t0 t2 a b S1 S2 S3 S4 H' H'0 H'1.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
intros r r0 t t0 t2 a b S1 S2 S3 S4 H' H'0 H'1.
apply dilemmaTraceEval with (S2 := S2) (S3 := S3); auto with stalmarck.
Qed.

(* Dilemma with 2 branches a=b and a=-b *)

Definition dilemma1 (f : list rZ -> rArray vM -> mbDT) 
  (Ar : rArray vM) (a b : rZ) : mbDT :=
  match addEqMem Ar a b with
  | triple Ar1 true L1 => quatuor _ _ _ _ Ar false nil emptyTrace
  | triple Ar1 false L1 =>
      match addEqMem Ar a (rZComp b) with
      | triple Ar2 true L2 => quatuor _ _ _ _ Ar false nil emptyTrace
      | triple Ar2 false L2 =>
          match f L1 Ar1 with
          | quatuor Ar1' true L1' T1' =>
              match f L2 Ar2 with
              | quatuor Ar2' true L2' T2' =>
                  quatuor _ _ _ _ Ar true nil (dT a b T1' T2')
              | quatuor Ar2' false L2' T2' =>
                  quatuor _ _ _ _ Ar2' false (appendRz L2 L2')
                    (dT a b T1' T2')
              end
          | quatuor Ar1' false L1' T1' =>
              match f L2 Ar2 with
              | quatuor Ar2' true L2' T2' =>
                  quatuor _ _ _ _ Ar1' false (appendRz L1 L1')
                    (dT a b T1' T2')
              | quatuor Ar2' false L2' T2' =>
                  match
                    interMem Ar1' Ar2' Ar (appendRz L1 L1') (appendRz L2 L2')
                  with
                  | (Ar', nil) => quatuor _ _ _ _ Ar' false nil emptyTrace
                  | (Ar', L') =>
                      quatuor _ _ _ _ Ar' false L' (dT a b T1' T2')
                  end
              end
          end
      end
  end.
(* To speedup Coq *)
Opaque addEqMem.

Hint Resolve f_equal : core.

Theorem dilemma1Correct :
 forall (f : list rZ -> rArray vM -> mbDT) (Ar : rArray vM) 
   (a b : rZ) (S : State),
 (forall (L : list rZ) (Ar : rArray vM) (S : State),
  FStalCorrect Ar LL S (f L Ar)) -> FStalCorrect Ar LL S (dilemma1 f Ar a b).
intros f Ar a b S H'; unfold dilemma1 in |- *.
generalize (addEqMemCorrect Ar a b S).
case (addEqMem Ar a b).
intros Ar1 b1 L1; case b1.
intros H'0.
apply FStalCorrect0; auto with stalmarck.
intros H'0.
generalize (addEqMemCorrect Ar a (rZComp b) S).
case (addEqMem Ar a (rZComp b)).
intros Ar2 b2 L2; case b2.
intros H'1.
apply FStalCorrect0; auto with stalmarck.
intros H'1.
generalize (H' L1 Ar1).
case (f L1 Ar1); auto with stalmarck.
intros Ar1' b1' L1' T1'; case b1'.
intros H'2.
generalize (H' L2 Ar2).
case (f L2 Ar2); auto with stalmarck.
intros Ar2' b2' L2' T2'; case b2'.
generalize H'2; unfold FStalCorrect in |- *; simpl in |- *.
intros H'3 H'4 H'5 H'6.
elim H'1;
 [ intros H'9 H'10; elim H'10; intros H'11 H'12; elim H'12; intros H'13 H'14;
    clear H'12 H'10 H'1
 | clear H'1
 | clear H'1 ]; auto with stalmarck.
elim H'0;
 [ intros H'8 H'10; elim H'10; intros H'12 H'15; elim H'15; intros H'16 H'17;
    clear H'15 H'10 H'0
 | clear H'0
 | clear H'0 ]; auto with stalmarck.
elim (H'3 (addEq (pair a b) S));
 [ intros S' E; elim E; intros H'10 H'15; elim H'15; intros H'18 H'19;
    clear H'15 E
 | idtac
 | idtac ]; auto with stalmarck.
elim (H'4 (addEq (pair a (rZComp b)) S));
 [ intros S'0 E; elim E; intros H'15 H'20; elim H'20; intros H'21 H'22;
    clear H'20 E
 | idtac
 | idtac ]; auto with stalmarck.
cut (eqState (interState S' S'0) S'); [ intros Eq1 | idtac ].
exists S'; repeat (split; auto with stalmarck).
apply stalmarckPSplit with (a := a) (b := b) (S2 := S') (S3 := S'0); auto with stalmarck.
apply dTCorrect with (S2 := S') (S3 := S'0); auto with stalmarck.
split; auto with stalmarck.
red in |- *.
intros i j H'0.
apply interMemEqStateRz; auto with stalmarck.
inversion H'21.
apply eqStateRzContr with (a := x); auto with stalmarck.
generalize H'2; unfold FStalCorrect in |- *; simpl in |- *.
intros H'3 H'4 H'5 H'6.
elim H'1;
 [ intros H'9 H'10; elim H'10; intros H'11 H'12; elim H'12; intros H'13 H'14;
    clear H'12 H'10 H'1
 | clear H'1
 | clear H'1 ]; auto with stalmarck.
elim H'0;
 [ intros H'8 H'10; elim H'10; intros H'12 H'15; elim H'15; intros H'16 H'17;
    clear H'15 H'10 H'0
 | clear H'0
 | clear H'0 ]; auto with stalmarck.
elim (H'3 (addEq (pair a b) S));
 [ intros S' E; elim E; intros H'10 H'15; elim H'15; intros H'18 H'19;
    clear H'15 E
 | idtac
 | idtac ]; auto with stalmarck.
elim (H'4 (addEq (pair a (rZComp b)) S));
 [ intros S'0 E; elim E; intros H'15 H'20; elim H'20; intros H'21 H'22;
    clear H'20 E
 | idtac
 | idtac ]; auto with stalmarck.
repeat (split; auto with stalmarck).
elim H'15; intros S'1 E; elim E; intros H'0 H'1; elim H'1; intros H'7 H'20;
 clear H'1 E H'15.
cut (eqState (interState S' S'1) S'1); [ intros Eq1 | idtac ].
exists S'1; repeat (split; auto with stalmarck).
apply stalmarckPSplit with (a := a) (b := b) (S2 := S') (S3 := S'1); auto with stalmarck.
apply dTCorrect with (S2 := S') (S3 := S'1); auto with stalmarck.
split; auto with stalmarck.
red in |- *.
intros i j H'1.
apply interMemEqStateRz; auto with stalmarck.
inversion H'18.
apply eqStateRzContr with (a := x); auto with stalmarck.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
intros e H'0.
rewrite H'22.
apply H'14; auto with stalmarck.
Contradict H'0; auto with stalmarck.
cut (InclEq _ eqRz L2 (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'1; inversion H'1; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'0; auto with stalmarck.
cut (InclEq _ eqRz L2' (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'1; inversion H'1; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
generalize (H' L2 Ar2).
case (f L2 Ar2); auto with stalmarck.
intros Ar2' b2' L2' T2'; case b2'.
unfold FStalCorrect in |- *; simpl in |- *.
intros H'3 H'4 H'5 H'6.
elim H'1;
 [ intros H'9 H'10; elim H'10; intros H'11 H'12; elim H'12; intros H'13 H'14;
    clear H'12 H'10 H'1
 | clear H'1
 | clear H'1 ]; auto with stalmarck.
elim H'0;
 [ intros H'8 H'10; elim H'10; intros H'12 H'15; elim H'15; intros H'16 H'17;
    clear H'15 H'10 H'0
 | clear H'0
 | clear H'0 ]; auto with stalmarck.
elim (H'3 (addEq (pair a (rZComp b)) S));
 [ intros S' E; elim E; intros H'10 H'15; elim H'15; intros H'18 H'19;
    clear H'15 E
 | idtac
 | idtac ]; auto with stalmarck.
elim (H'4 (addEq (pair a b) S));
 [ intros S'0 E; elim E; intros H'15 H'20; elim H'20; intros H'21 H'22;
    clear H'20 E
 | idtac
 | idtac ]; auto with stalmarck.
repeat (split; auto with stalmarck).
elim H'15; intros S'1 E; elim E; intros H'0 H'1; elim H'1; intros H'7 H'20;
 clear H'1 E H'15.
cut (eqState (interState S'1 S') S'1); [ intros Eq1 | idtac ].
exists S'1; repeat (split; auto with stalmarck).
apply stalmarckPSplit with (a := a) (b := b) (S2 := S'1) (S3 := S'); auto with stalmarck.
apply dTCorrect with (S2 := S'1) (S3 := S'); auto with stalmarck.
split; auto with stalmarck.
red in |- *.
intros i j H'1.
apply interMemEqStateRz; auto with stalmarck.
inversion H'18.
apply eqStateRzContr with (a := x); auto with stalmarck.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
intros e H'0.
rewrite H'22.
apply H'17; auto with stalmarck.
Contradict H'0; auto with stalmarck.
cut (InclEq _ eqRz L1 (appendf _ rZlt eqRz rZltEDec L1 L1')); auto with stalmarck.
intros H'1; inversion H'1; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'0; auto with stalmarck.
cut (InclEq _ eqRz L1' (appendf _ rZlt eqRz rZltEDec L1 L1')); auto with stalmarck.
intros H'1; inversion H'1; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
unfold FStalCorrect in |- *; simpl in |- *.
intros H'3 H'4 H'5 H'6.
elim H'1;
 [ intros H'9 H'10; elim H'10; intros H'11 H'12; elim H'12; intros H'13 H'14;
    clear H'12 H'10 H'1
 | clear H'1
 | clear H'1 ]; auto with stalmarck.
elim H'0;
 [ intros H'8 H'10; elim H'10; intros H'12 H'15; elim H'15; intros H'16 H'17;
    clear H'15 H'10 H'0
 | clear H'0
 | clear H'0 ]; auto with stalmarck.
elim (H'3 (addEq (pair a (rZComp b)) S));
 [ intros H'7 H'10; elim H'10; intros H'15 H'18; elim H'18; intros H'19 H'20;
    clear H'18 H'10
 | idtac
 | idtac ]; auto with stalmarck.
elim (H'4 (addEq (pair a b) S));
 [ intros H'10 H'18; elim H'18; intros H'21 H'22; elim H'22; intros H'23 H'24;
    clear H'22 H'18
 | idtac
 | idtac ]; auto with stalmarck.
cut (OlistRz (appendRz L1 L1'));
 [ intros O1
 | unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck;
    exact rZltEqComp ].
cut (OlistRz (appendRz L2 L2'));
 [ intros O2
 | unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck;
    exact rZltEqComp ].
elim H'15; intros S' E; elim E; intros H'0 H'1; elim H'1; intros H'2 H'18;
 clear H'1 E H'15.
elim H'21; intros S'0 E; elim E; intros H'1 H'15; elim H'15; intros H'22 H'25;
 clear H'15 E H'21.
generalize
 (interImplement2.interMemProp Ar1' Ar2' Ar H'10 H'7 H'5 (appendRz L1 L1')
    (appendRz L2 L2') O1 O2 _ _ _ H'22 H'2 H'6).
case (interMem Ar1' Ar2' Ar (appendRz L1 L1') (appendRz L2 L2')).
intros Ar' L' H'15; elim H'15;
 [ intros H'29 H'30; elim H'30; intros H'31 H'32; elim H'32;
    clear H'32 H'30 H'15
 | clear H'15
 | clear H'15
 | clear H'15
 | clear H'15 ]; auto with stalmarck.
case L'; auto with stalmarck.
intros H'15 H'21; repeat (split; auto with stalmarck).
exists S; split; [ idtac | split ]; auto with stalmarck.
apply rArrayStateGet with (Ar := Ar); auto with stalmarck.
intros e; apply H'15; auto with stalmarck.
red in |- *; intros H'26; inversion H'26.
intros r l H'15 H'21; repeat (split; auto with stalmarck).
exists (interState S'0 S'); split; [ idtac | split ]; auto with stalmarck.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S'0) (S3 := S'); auto with stalmarck.
apply dTCorrect with (S2 := S'0) (S3 := S'); auto with stalmarck.
apply inclStateTrans with (addEq (pair a b) S); auto with stalmarck.
apply stalmarckIncl with (L := LL); auto with stalmarck.
apply inclStateTrans with (addEq (pair a (rZComp b)) S); auto with stalmarck.
apply stalmarckIncl with (L := LL); auto with stalmarck.
intros e H'15; rewrite H'24; auto with stalmarck.
apply H'17; auto with stalmarck.
Contradict H'15.
cut (InclEq _ eqRz L1 (appendf _ rZlt eqRz rZltEDec L1 L1')); auto with stalmarck.
intros H'21; inversion H'21; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'15.
cut (InclEq _ eqRz L1' (appendf _ rZlt eqRz rZltEDec L1 L1')); auto with stalmarck.
intros H'21; inversion H'21; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
intros e H'15; rewrite H'20; auto with stalmarck.
apply H'14; auto with stalmarck.
Contradict H'15.
cut (InclEq _ eqRz L2 (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'21; inversion H'21; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'15.
cut (InclEq _ eqRz L2' (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'21; inversion H'21; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
Qed.
(* We do the dilemma n times starting from v *)

Fixpoint dilemma1R (f : list rZ -> rArray vM -> mbDT) 
 (v : rNat) (n : nat) {struct n} : rArray vM -> mbDT :=
  fun Ar =>
  match rArrayGet _ Ar v with
  | ref _ =>
      match n with
      | O => quatuor _ _ _ _ Ar false nil emptyTrace
      | S m => dilemma1R f (rnext v) m Ar
      end
  | class _ =>
      match dilemma1 f Ar (rZPlus v) rZTrue with
      | quatuor Ar1 true L1 T1 => quatuor _ _ _ _ Ar1 true L1 T1
      | quatuor Ar1 false L1 T1 =>
          match n with
          | O => quatuor _ _ _ _ Ar1 false L1 T1
          | S m =>
              match dilemma1R f (rnext v) m Ar1 with
              | quatuor Ar2 b L2 T2 =>
                  quatuor _ _ _ _ Ar2 b (appendRz L1 L2) (appTrace T1 T2)
              end
          end
      end
  end.

Theorem dilemma1RCorrect :
 forall (f : list rZ -> rArray vM -> _) (n1 : nat) 
   (v : rNat) (Ar : rArray vM) (S : State),
 (forall (L : list rZ) (Ar : rArray vM) (S : State),
  FStalCorrect Ar LL S (f L Ar)) ->
 FStalCorrect Ar LL S (dilemma1R f v n1 Ar).
intros f n1; elim n1; simpl in |- *; auto with stalmarck.
intros v Ar S H'; case (rArrayGet vM Ar v); auto with stalmarck.
intros H'0.
apply FStalCorrect0; auto with stalmarck.
intros L; generalize (dilemma1Correct f Ar (rZPlus v) rZTrue S H').
case (dilemma1 f Ar (rZPlus v) rZTrue).
intros Ar1 b1 L1 T1; case b1; auto with stalmarck.
intros n0 H' v Ar S H'0.
case (rArrayGet vM Ar v); auto with stalmarck.
intros L; generalize (dilemma1Correct f Ar (rZPlus v) rZTrue S H'0).
case (dilemma1 f Ar (rZPlus v) rZTrue).
intros Ar1 b1 L1 T1; case b1; auto with stalmarck.
intros H'1.
generalize (fun S : State => H' (rnext v) Ar1 S H'0).
case (dilemma1R f (rnext v) n0 Ar1).
intros r b l t H'2.
apply FStalCorrectComp with (Ar' := Ar1); auto with stalmarck.
Qed.
Variable n : nat.
(* Now we iter  dilemma1R till no information, this is done using an integer
    n1 sufficiently large *)

Fixpoint dilemma1RR (f : list rZ -> rArray vM -> mbDT) 
 (n1 : nat) {struct n1} : rArray vM -> mbDT :=
  fun Ar =>
  match dilemma1R f zero n Ar with
  | quatuor Ar1 true L1 T1 => quatuor _ _ _ _ Ar1 true L1 T1
  | quatuor Ar1 false nil T1 => quatuor _ _ _ _ Ar1 false nil T1
  | quatuor Ar1 false L1 T1 =>
      match n1 with
      | O => quatuor _ _ _ _ Ar1 false L1 T1
      | S m =>
          match dilemma1RR f m Ar1 with
          | quatuor Ar2 b L2 T2 =>
              quatuor _ _ _ _ Ar2 b (appendRz L1 L2) (appTrace T1 T2)
          end
      end
  end.

Theorem dilemma1RRCorrect :
 forall (f : list rZ -> rArray vM -> _) (n1 : nat) 
   (Ar : rArray vM) (S : State),
 (forall (L : list rZ) (Ar : rArray vM) (S : State),
  FStalCorrect Ar LL S (f L Ar)) -> FStalCorrect Ar LL S (dilemma1RR f n1 Ar).
intros f n1; elim n1; simpl in |- *; auto with stalmarck.
intros Ar S H'.
generalize (dilemma1RCorrect f n zero Ar S H').
case (dilemma1R f zero n Ar).
intros Ar1 b1 L1 T1; case b1; auto with stalmarck.
case L1; auto with stalmarck.
intros n0 H' Ar S H'0.
generalize (dilemma1RCorrect f n zero Ar S H'0).
case (dilemma1R f zero n Ar).
intros Ar1 b1 L1 T1; case b1; auto with stalmarck.
case L1; auto with stalmarck.
intros r l H'1.
generalize (fun S : State => H' Ar1 S H'0).
case (dilemma1RR f n0 Ar1).
intros r0 b l0 t H'2.
apply FStalCorrectComp with (Ar' := Ar1); auto with stalmarck.
Qed.

(*We first apply  a doTriplets to take care of the modif*)

Definition dilemma1RRL (f : list rZ -> rArray vM -> mbDT) 
  (Lt : list rZ) (n : nat) (Ar : rArray vM) : mbDT :=
  match doTripletsN getT Lt n Ar with
  | quatuor Ar1 true L1 T1 => quatuor _ _ _ _ Ar1 true L1 T1
  | quatuor Ar1 false L1 T1 =>
      match dilemma1RR f n Ar1 with
      | quatuor Ar2 b L2 T2 =>
          quatuor _ _ _ _ Ar2 b (appendRz L1 L2) (appTrace T1 T2)
      end
  end.

Theorem dilemma1RRLCorrect :
 forall (f : list rZ -> rArray vM -> _) (Lt : list rZ) 
   (n1 : nat) (Ar : rArray vM) (S : State),
 (forall (L : list rZ) (Ar : rArray vM) (S : State),
  FStalCorrect Ar LL S (f L Ar)) ->
 FStalCorrect Ar LL S (dilemma1RRL f Lt n1 Ar).
intros f Lt n1 Ar S H'; unfold dilemma1RRL in |- *.
generalize (doTripletFsNCorrect getT LL getTCorrect n1 Ar Lt S).
case (doTripletsN getT Lt n1 Ar); auto with stalmarck.
intros Ar1 b1 L1 T1; case b1; auto with stalmarck.
intros H'0.
generalize (fun S : State => dilemma1RRCorrect f n1 Ar1 S H').
case (dilemma1RR f n1 Ar1); auto with stalmarck.
intros r b l t H'1.
apply FStalCorrectComp with (Ar' := Ar1); auto with stalmarck.
Qed.
(* We do the dilemma n times starting from v *)

Fixpoint dilemmaN (L : list rZ) (m n : nat) {struct n} : 
 rArray vM -> mbDT :=
  match n with
  | O => doTripletsN getT L m
  | S n1 => dilemma1RRL (fun L : list rZ => dilemmaN L m n1) L m
  end.

Theorem dilemmaNCorrect :
 forall (L : list rZ) (m n : nat) (Ar : rArray vM) (S : State),
 FStalCorrect Ar LL S (dilemmaN L m n Ar).
intros L m n0; generalize L; elim n0; auto with stalmarck; clear L.
intros L Ar S;
 change (FStalCorrect Ar LL S (doTripletsN getT L m Ar)) in |- *.
apply doTripletFsNCorrect; auto with stalmarck.
intros n1 H' L Ar S0; simpl in |- *; auto with stalmarck.
apply dilemma1RRLCorrect; auto with stalmarck.
Qed.
Transparent addEqMem.
End odilemma1.
