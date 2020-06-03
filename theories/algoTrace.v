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
                                                                           
          Stalmarck  :  algoTrace                                           
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
****************************************************************************)
Require Export trace.
Require Export algoDotriplet.
Require Export interImplement2.
Require Import makeTriplet.

(* Append inside a triplet *)

Definition appL (L : list rZ) (d : mbD) : mbD :=
  match d with
  | triple a b l => triple _ _ _ a b (appendRz L l)
  end.
(* To make Coq run faster *)
Opaque addEqMem.
Opaque doTripletF.
Opaque interMem.
(* Evaluation of a dotriplet trace *)

Fixpoint evalTraceF (T : Trace) : rArray vM -> mbD :=
  fun Ar =>
  match T with
  | emptyTrace => triple _ _ _ Ar false nil
  | tripletTrace t =>
      match doTripletF Ar t with
      | None => triple _ _ _ Ar false nil
      | Some T => T
      end
  | seqTrace T1 T2 =>
      match evalTraceF T1 Ar with
      | triple Ar' true L' => triple _ _ _ Ar' true L'
      | triple Ar' false L' => appL L' (evalTraceF T2 Ar')
      end
  | dilemmaTrace a b T1 T2 =>
      match addEqMem Ar a b with
      | triple Ar1 true L1 =>
          match addEqMem Ar a (rZComp b) with
          | triple Ar2 true L2 => triple _ _ _ Ar true nil
          | triple Ar2 false L2 => appL L2 (evalTraceF T2 Ar2)
          end
      | triple Ar1 false L1 =>
          match addEqMem Ar a (rZComp b) with
          | triple Ar2 true L2 => appL L1 (evalTraceF T1 Ar1)
          | triple Ar2 false L2 =>
              match evalTraceF T1 Ar1 with
              | triple Ar1' true L1' => appL L2 (evalTraceF T2 Ar2)
              | triple Ar1' false L1' =>
                  match evalTraceF T2 Ar2 with
                  | triple Ar2' true L2' =>
                      triple _ _ _ Ar1' false (appendRz L1 L1')
                  | triple Ar2' false L2' =>
                      match
                        interMem Ar1' Ar2' Ar (appendRz L1 L1')
                          (appendRz L2 L2')
                      with
                      | (Ar', L') => triple _ _ _ Ar' false L'
                      end
                  end
              end
          end
      end
  end.

Theorem TraceCorrect :
 forall (Ar : rArray vM) (T : Trace) (LL : list triplet),
 TraceInList T LL ->
 forall S : State,
 wellFormedArray Ar ->
 rArrayState Ar S ->
 match evalTraceF T Ar with
 | triple Ar' false L =>
     wellFormedArray Ar' /\
     (exists S' : State, stalmarckP S LL S' /\ rArrayState Ar' S') /\
     OlistRz L /\
     (forall e : rNat,
      ~ InRz (rZPlus e) L -> rArrayGet _ Ar' e = rArrayGet _ Ar e)
 | triple Ar' true L =>
     exists S' : State, stalmarckP S LL S' /\ contradictory S'
 end.
intros Ar T; generalize Ar; clear Ar; elim T; simpl in |- *.
intros Ar LL H' S H'0 H'1; repeat (split; auto with stalmarck).
exists S; split; auto with stalmarck.
red in |- *; apply OlistNil; auto with stalmarck.
intros t Ar LL H' S H'0 H'1.
generalize (doTripletFCorrect Ar t S H'0 H'1).
case (doTripletF Ar t).
intros x; case x; auto with stalmarck.
intros Ar' b' L'; case b'.
intros H'3; Elimc H'3; intros S' E; Elimc E; intros H'3 H'4.
exists S'; split; auto with stalmarck.
apply stalmarckPref; auto with stalmarck.
apply doTripletsTrans with (S2 := S') (t := t); auto with stalmarck.
intros H'3; Elimc H'3; intros H'3 H'4; Elimc H'4; intros H'4 H'5; Elimc H'5;
 intros H'5 H'6.
Elimc H'4; intros S' E; Elimc E; intros H'4 H'7.
repeat (split; auto with stalmarck).
exists S'; split; auto with stalmarck.
apply stalmarckTrans with (S2 := S'); auto with stalmarck.
apply stalmarckPref; auto with stalmarck.
apply doTripletsTrans with (S2 := S') (t := t); auto with stalmarck.
intros H'2; repeat (split; auto with stalmarck).
exists S; split; auto with stalmarck.
red in |- *; apply OlistNil; auto with stalmarck.
intros t H' t0 H'0 Ar LL H'1 S H'2 H'3.
elim H'1; intros H'4 H'5; clear H'1.
generalize (H' Ar LL H'4 S H'2 H'3).
case (evalTraceF t Ar).
intros Ar'' b'' L''; case b''; simpl in |- *; auto with stalmarck.
intros H'1; elim H'1; intros H'6 H'7; elim H'7; intros H'8 H'9; elim H'9;
 intros H'10 H'11; clear H'9 H'7 H'1.
elim H'8; intros S' E; elim E; intros H'1 H'7; clear E H'8.
generalize (H'0 Ar'' LL H'5 S' H'6 H'7).
case (evalTraceF t0 Ar''); auto with stalmarck.
intros Ar''' b''' L'''; case b'''; simpl in |- *; auto with stalmarck.
intros H'8; elim H'8; intros S'0 E; elim E; intros H'9 H'12; clear E H'8.
exists S'0; split; auto with stalmarck.
apply stalmarckTrans with (S2 := S'); auto with stalmarck.
intros H'8; elim H'8; intros H'9 H'12; elim H'12; intros H'13 H'14; elim H'14;
 intros H'15 H'16; clear H'14 H'12 H'8.
repeat (split; auto with stalmarck).
elim H'13; intros S'0 E; elim E; intros H'8 H'12; clear E H'13.
exists S'0; split; auto with stalmarck.
apply stalmarckTrans with (S2 := S'); auto with stalmarck.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
intros e H'14.
rewrite H'16.
apply H'11; auto with stalmarck.
Contradict H'14; auto with stalmarck.
cut (InclEq _ eqRz L'' (appendf _ rZlt eqRz rZltEDec L'' L''')).
intros H'8; inversion H'8; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'14; auto with stalmarck.
cut (InclEq _ eqRz L''' (appendf _ rZlt eqRz rZltEDec L'' L''')).
intros H'8; inversion H'8; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
intros a b t H' t0 H'0 Ar LL H'1 S H'2 H'3.
generalize (addEqMemCorrect Ar a b S H'2 H'3).
case (addEqMem Ar a b).
intros Ar1 b1 L1; case b1.
intros H'4.
generalize (addEqMemCorrect Ar a (rZComp b) S H'2 H'3); auto with stalmarck.
case (addEqMem Ar a (rZComp b)); auto with stalmarck.
intros Ar2 b2 L2; case b2.
intros H'5; exists S; split; auto with stalmarck.
red in |- *.
exists a.
apply eqStateRzTrans with (b := rZComp (rZComp b)); auto with stalmarck.
apply eqStateRzInv; auto with stalmarck.
apply eqStateRzSym; auto with stalmarck.
intros H'5; Elimc H'5; intros H'5 H'6; Elimc H'6; intros H'6 H'7; Elimc H'7;
 intros H'7 H'8.
Elimc H'1; intros H'1 H'9.
generalize (H'0 Ar2 LL H'9 _ H'5 H'6).
case (evalTraceF t0 Ar2); auto with stalmarck.
intros Ar2' b2' L2'; case b2'; simpl in |- *; auto with stalmarck.
intros H'10; Elimc H'10; intros S' E; Elimc E; intros H'10 H'11.
exists S'; split; auto with stalmarck.
apply stalmarckTrans with (S2 := S'); auto with stalmarck.
apply
 stalmarckPSplit with (a := a) (b := b) (S2 := addEq (a, b) S) (S3 := S');
 auto with stalmarck.
red in |- *; split; auto with stalmarck.
red in |- *.
intros i j H'12.
apply interMemEqStateRz; auto with stalmarck.
case H'4.
intros x H'13.
apply eqStateRzContr with (a := x); auto with stalmarck.
intros H'10; Elimc H'10; intros H'10 H'11; Elimc H'11; intros H'11 H'12;
 Elimc H'12; intros H'12 H'13.
Elimc H'11; intros S' E; Elimc E; intros H'11 H'14.
repeat (split; auto with stalmarck).
exists S'; split; auto with stalmarck.
apply
 stalmarckPSplit with (a := a) (b := b) (S2 := addEq (a, b) S) (S3 := S');
 auto with stalmarck.
red in |- *; split; auto with stalmarck.
red in |- *.
intros i j H'15.
apply interMemEqStateRz; auto with stalmarck.
case H'4.
intros x H'16.
apply eqStateRzContr with (a := x); auto with stalmarck.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
intros e H'15.
rewrite H'13.
apply H'8; auto with stalmarck.
Contradict H'15; auto with stalmarck.
cut (InclEq _ eqRz L2 (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'16; inversion H'16; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'15; auto with stalmarck.
cut (InclEq _ eqRz L2' (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'16; inversion H'16; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
intros H'4; Elimc H'4; intros H'4 H'5; Elimc H'5; intros H'5 H'6; Elimc H'6;
 intros H'6 H'7.
Elimc H'1; intros H'1 H'8.
generalize (addEqMemCorrect Ar a (rZComp b) S H'2 H'3); auto with stalmarck.
case (addEqMem Ar a (rZComp b)); auto with stalmarck.
intros Ar2 b2 L2; case b2.
intros H'9.
generalize (H' Ar1 LL H'1 _ H'4 H'5).
case (evalTraceF t Ar1).
intros Ar1' b1' L1'; case b1'; simpl in |- *; auto with stalmarck.
intros H'10; Elimc H'10; intros S' E; Elimc E; intros H'10 H'11.
exists S'; split; auto with stalmarck.
apply
 stalmarckPSplit
  with (a := a) (b := b) (S2 := S') (S3 := addEq (a, rZComp b) S); 
 auto with stalmarck.
red in |- *; split; auto with stalmarck; auto with stalmarck.
red in |- *.
intros i j H'12.
apply interMemEqStateRz; auto with stalmarck.
case H'9.
intros x H'13.
apply eqStateRzContr with (a := x); auto with stalmarck.
intros H'10; Elimc H'10; intros H'10 H'11; Elimc H'11; intros H'11 H'12;
 Elimc H'12; intros H'12 H'13.
repeat (split; auto with stalmarck).
Elimc H'11; intros S' E; Elimc E; intros H'11 H'14.
exists S'; split; auto with stalmarck.
apply
 stalmarckPSplit
  with (a := a) (b := b) (S2 := S') (S3 := addEq (a, rZComp b) S); 
 auto with stalmarck.
red in |- *; split; auto with stalmarck; auto with stalmarck.
red in |- *.
intros i j H'15.
apply interMemEqStateRz; auto with stalmarck.
case H'9.
intros x H'16.
apply eqStateRzContr with (a := x); auto with stalmarck.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
intros e H'14.
rewrite H'13.
apply H'7; auto with stalmarck.
Contradict H'14; auto with stalmarck.
cut (InclEq _ eqRz L1 (appendf _ rZlt eqRz rZltEDec L1 L1')).
intros H'15; inversion H'15; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'14; auto with stalmarck.
cut (InclEq _ eqRz L1' (appendf _ rZlt eqRz rZltEDec L1 L1')).
intros H'15; inversion H'15; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
intros H'9; Elimc H'9; intros H'9 H'10; Elimc H'10; intros H'10 H'11;
 Elimc H'11; intros H'11 H'12.
generalize (H' Ar1 LL H'1 _ H'4 H'5).
case (evalTraceF t Ar1).
intros Ar1' b1' L1'; case b1'; simpl in |- *; auto with stalmarck.
intros H'13; Elimc H'13; intros S' E; Elimc E; intros H'13 H'14.
generalize (H'0 Ar2 LL H'8 _ H'9 H'10).
case (evalTraceF t0 Ar2).
intros Ar2' b2' L2'; case b2'; simpl in |- *; auto with stalmarck.
intros H'15; Elimc H'15; intros S'0 E; Elimc E; intros H'15 H'16.
exists S'; split; auto with stalmarck.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S') (S3 := S'0); auto with stalmarck.
split; auto with stalmarck.
red in |- *.
intros i j H'17.
apply interMemEqStateRz; auto with stalmarck.
case H'16.
intros x H'18.
apply eqStateRzContr with (a := x); auto with stalmarck.
intros H'15; Elimc H'15; intros H'15 H'16; Elimc H'16; intros H'16 H'17;
 Elimc H'17; intros H'17 H'18.
Elimc H'16; intros S'0 E; Elimc E; intros H'16 H'19.
repeat (split; auto with stalmarck).
exists S'0; split; auto with stalmarck.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S') (S3 := S'0); auto with stalmarck.
split; auto with stalmarck.
red in |- *.
intros i j H'20.
apply interMemEqStateRz; auto with stalmarck.
case H'14.
intros x H'21.
apply eqStateRzContr with (a := x); auto with stalmarck.
unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
try exact rZltEqComp.
intros e H'20.
rewrite H'18.
apply H'12; auto with stalmarck.
Contradict H'20; auto with stalmarck.
cut (InclEq _ eqRz L2 (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'21; inversion H'21; red in |- *; auto with stalmarck.
apply appendfInclEq1; auto with stalmarck.
Contradict H'20; auto with stalmarck.
cut (InclEq _ eqRz L2' (appendf _ rZlt eqRz rZltEDec L2 L2')).
intros H'21; inversion H'21; red in |- *; auto with stalmarck.
apply appendfInclEq2; auto with stalmarck.
intros H'13; Elimc H'13; intros H'13 H'14; Elimc H'14; intros H'14 H'15;
 Elimc H'15; intros H'15 H'16.
cut (OlistRz (appendRz L1 L1')); [ intros O1 | idtac ].
2: unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
2: try exact rZltEqComp.
cut
 (forall e : rNat,
  ~ InRz (rZPlus e) (appendRz L1 L1') ->
  rArrayGet vM Ar1' e = rArrayGet vM Ar e); [ intros E1 | idtac ].
2: intros e H'17.
2: rewrite H'16; auto with stalmarck.
2: apply H'7; auto with stalmarck.
2: Contradict H'17; auto with stalmarck.
2: cut (InclEq _ eqRz L1 (appendf _ rZlt eqRz rZltEDec L1 L1')).
2: intros H'18; inversion H'18; red in |- *; auto with stalmarck.
2: apply appendfInclEq1; auto with stalmarck.
2: Contradict H'17; auto with stalmarck.
2: cut (InclEq _ eqRz L1' (appendf _ rZlt eqRz rZltEDec L1 L1')).
2: intros H'18; inversion H'18; red in |- *; auto with stalmarck.
2: apply appendfInclEq2; auto with stalmarck.
generalize (H'0 Ar2 LL H'8 _ H'9 H'10).
case (evalTraceF t0 Ar2).
intros Ar2' b2' L2'; case b2'; simpl in |- *; auto with stalmarck.
intros H'17; Elimc H'17; intros S' E; Elimc E; intros H'17 H'18.
repeat (split; auto with stalmarck).
Elimc H'14; intros S'0 E; Elimc E; intros H'14 H'19.
exists S'0; split; auto with stalmarck.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S'0) (S3 := S'); auto with stalmarck.
split; auto with stalmarck.
red in |- *.
intros i j H'20.
apply interMemEqStateRz; auto with stalmarck.
case H'18.
intros x H'21.
apply eqStateRzContr with (a := x); auto with stalmarck.
intros H'17; Elimc H'17; intros H'17 H'18; Elimc H'18; intros H'18 H'19;
 Elimc H'19; intros H'19 H'20.
cut (OlistRz (appendRz L2 L2')); [ intros O2 | idtac ].
2: unfold appendRz in |- *; red in |- *; apply appendfOlist; auto with stalmarck.
2: try exact rZltEqComp.
cut
 (forall e : rNat,
  ~ InRz (rZPlus e) (appendRz L2 L2') ->
  rArrayGet vM Ar2' e = rArrayGet vM Ar e); [ intros E2 | idtac ].
2: intros e H'21.
2: rewrite H'20; auto with stalmarck.
2: apply H'12; auto with stalmarck.
2: Contradict H'21; auto with stalmarck.
2: cut (InclEq _ eqRz L2 (appendf _ rZlt eqRz rZltEDec L2 L2')).
2: intros H'22; inversion H'22; red in |- *; auto with stalmarck.
2: apply appendfInclEq1; auto with stalmarck.
2: Contradict H'21; auto with stalmarck.
2: cut (InclEq _ eqRz L2' (appendf _ rZlt eqRz rZltEDec L2 L2')).
2: intros H'22; inversion H'22; red in |- *; auto with stalmarck.
2: apply appendfInclEq2; auto with stalmarck.
Elimc H'18; intros S'0 E; Elimc E; intros H'18 H'21.
Elimc H'14; intros S' E; Elimc E; intros H'14 H'22.
cut (inclState S S'); [ intros I1 | idtac ].
cut (inclState S S'0); [ intros I2 | idtac ].
generalize
 (interMemProp Ar1' Ar2' Ar H'13 H'17 H'2 (appendRz L1 L1') 
    (appendRz L2 L2') O1 O2 _ _ _ H'22 H'21 H'3 I1 I2 E1 E2).
case (interMem Ar1' Ar2' Ar (appendRz L1 L1') (appendRz L2 L2')).
intros Ar' L' H'23; Elimc H'23; intros H'23 H'24; Elimc H'24;
 intros H'24 H'25; Elimc H'25; intros H'25 H'26.
repeat (split; auto with stalmarck).
exists (interState S' S'0); split; auto with stalmarck.
apply stalmarckPSplit with (a := a) (b := b) (S2 := S') (S3 := S'0); auto with stalmarck.
apply inclStateTrans with (addEq (a, rZComp b) S); auto with stalmarck.
apply stalmarckIncl with (L := LL); auto with stalmarck.
apply inclStateTrans with (addEq (a, b) S); auto with stalmarck.
apply stalmarckIncl with (L := LL); auto with stalmarck.
Qed.
(* A computable InDec *)

Definition InDec :
  forall A : Set,
  (forall x y : A, {x = y :>A} + {x <> y :>A}) ->
  forall (a : A) (l : list A), {In a l} + {~ In a l}.
fix InDec 4.
intros A H' a l; case l.
right; red in |- *; intros H'0; inversion H'0.
intros a0 l0; case (H' a a0).
intros H'0; left; rewrite H'0; auto with datatypes stalmarck.
intros H'0; case (InDec A H' a l0).
intros H'1; left; auto with datatypes stalmarck.
intros H'1; right; simpl in |- *; red in |- *; intros H'2; case H'2; auto with stalmarck.
Defined.
(* the function f returns given a signed variable the triplets that contains this variable
    fIn just check if all triplets in the trace are in the image of f *)

Fixpoint fInT (f : rZ -> list triplet) (T : Trace) {struct T} : bool :=
  match T with
  | emptyTrace => true
  | tripletTrace (Triplet b p q r) =>
      match InDec _ tripletDec (Triplet b p q r) (f p) with
      | left _ => true
      | right _ => false
      end
  | seqTrace T1 T2 =>
      match fInT f T1 with
      | true => fInT f T2
      | false => false
      end
  | dilemmaTrace _ _ T1 T2 =>
      match fInT f T1 with
      | true => fInT f T2
      | false => false
      end
  end.

Theorem fInTCorrect :
 forall (LL : list triplet) (f : rZ -> _) (T : Trace),
 (forall n : rZ, incl (f n) LL) -> fInT f T = true -> TraceInList T LL.
intros LL f T H'; elim T; simpl in |- *; auto with stalmarck.
intros t; case t; auto with stalmarck.
intros r r0 r1 r2; case (InDec _ tripletDec (Triplet r r0 r1 r2) (f r0));
 auto with stalmarck.
intros H'0 H'1; apply (H' r0); auto with stalmarck.
intros; discriminate.
intros t; case (fInT f t); auto with stalmarck.
intros; discriminate.
intros a b t; case (fInT f t); auto with stalmarck.
intros; discriminate.
Qed.
(* Build the hashtable *)

Fixpoint buildL (L : list triplet) : rArray (list triplet) :=
  match L with
  | nil => rArrayMake _ (rEmpty _) (fun r => nil)
  | t :: L1 =>
      match t with
      | Triplet _ p q r =>
          letP _ _
            (letP _ _
               (letP _ _ (buildL L1)
                  (fun Ar1 =>
                   rArraySet _ Ar1 (valRz p) (t :: rArrayGet _ Ar1 (valRz p))))
               (fun Ar2 =>
                rArraySet _ Ar2 (valRz q) (t :: rArrayGet _ Ar2 (valRz q))))
            (fun Ar3 =>
             rArraySet _ Ar3 (valRz r) (t :: rArrayGet _ Ar3 (valRz r)))
      end
  end.

Definition getT (Ar : rArray (list triplet)) (r : rZ) :=
  rArrayGet _ Ar (valRz r).

Theorem getTCorrect :
 forall (L : list triplet) (a : rZ), incl (getT (buildL L) a) L.
unfold getT in |- *; intros L; elim L; simpl in |- *.
intros a; elim a; simpl in |- *.
intros r; case r; simpl in |- *; auto with datatypes stalmarck.
intros r; case r; simpl in |- *; auto with datatypes stalmarck.
intros t; case t; auto with stalmarck.
intros r r0 r1 r2 l H' a; unfold letP, getT in |- *; simpl in |- *.
case (rNatDec (valRz r2) (valRz a)); intros Eq1.
repeat rewrite Eq1.
repeat rewrite rArrayDef1 with (m := valRz a).
case (rNatDec (valRz r1) (valRz a)); intros Eq2.
repeat rewrite Eq2.
repeat rewrite rArrayDef1 with (m := valRz a).
case (rNatDec (valRz r0) (valRz a)); intros Eq3.
repeat rewrite Eq3.
repeat rewrite rArrayDef1 with (m := valRz a); auto with datatypes stalmarck.
repeat rewrite rArrayDef2 with (m2 := valRz a); auto with datatypes stalmarck.
rewrite rArrayDef2 with (m2 := valRz a); auto with stalmarck.
case (rNatDec (valRz r0) (valRz a)); intros Eq3.
repeat rewrite Eq3.
repeat rewrite rArrayDef1 with (m := valRz a); auto with datatypes stalmarck.
rewrite rArrayDef2 with (m2 := valRz a); auto with datatypes stalmarck.
rewrite rArrayDef2 with (m2 := valRz a); auto with datatypes stalmarck.
case (rNatDec (valRz r1) (valRz a)); intros Eq2.
repeat rewrite Eq2.
repeat rewrite rArrayDef1 with (m := valRz a).
case (rNatDec (valRz r0) (valRz a)); intros Eq3.
repeat rewrite Eq3.
repeat rewrite rArrayDef1 with (m := valRz a); auto with datatypes stalmarck.
repeat rewrite rArrayDef2 with (m2 := valRz a); auto with datatypes stalmarck.
rewrite rArrayDef2 with (m2 := valRz a); auto with stalmarck.
case (rNatDec (valRz r0) (valRz a)); intros Eq3.
repeat rewrite Eq3.
repeat rewrite rArrayDef1 with (m := valRz a); auto with datatypes stalmarck.
rewrite rArrayDef2 with (m2 := valRz a); auto with datatypes stalmarck.
Qed.
(* The initial array is well-formed *)

Theorem rIwF : wellFormedArray (rArrayInit vM (fun _ : rNat => class nil)).
apply wellFormedArrayDef; auto with stalmarck.
apply pointerDecreaseDef; simpl in |- *; auto with stalmarck.
intros r; case r; simpl in |- *; intros; discriminate.
apply pointToClassRefDef; simpl in |- *; auto with stalmarck.
intros r; case r; simpl in |- *; intros; discriminate.
apply pointToClassClassRef; simpl in |- *; auto with stalmarck.
intros r; case r; simpl in |- *.
intros p s Lr H'; inversion H'.
intros H'0; inversion H'0.
intros p s Lr H'; inversion H'.
intros H'0; inversion H'0.
intros s Lr H'; inversion H'.
intros H'0; inversion H'0.
intros r; case r; simpl in |- *; intros; discriminate.
apply OlistArrayDef; simpl in |- *; auto with stalmarck.
intros r; case r; simpl in |- *.
intros H' Lr H'0; inversion H'0; red in |- *; apply OlistNil; auto with stalmarck.
intros H' Lr H'0; inversion H'0; red in |- *; apply OlistNil; auto with stalmarck.
intros Lr H'; inversion H'; red in |- *; apply OlistNil; auto with stalmarck.
Qed.
(* The correction of our checker *)

Theorem checkTrace :
 forall (e : Expr) (T : Trace),
 match makeTriplets (norm e) with
 | tRC L r n =>
     match fInT (getT (buildL L)) T with
     | true =>
         match addEqMem (rArrayInit _ (fun r => class nil)) r rZFalse with
         | triple Ar1 true L1 => Tautology e
         | triple Ar1 false L1 =>
             match evalTraceF T Ar1 with
             | triple Ar' false L => True
             | triple Ar' true L => Tautology e
             end
         end
     | false => True
     end
 end.
intros e T; CaseEq (makeTriplets (norm e)).
intros l r r0.
CaseEq (fInT (getT (buildL l)) T); auto with stalmarck.
CaseEq (addEqMem (rArrayInit vM (fun _ : rNat => class nil)) r rZFalse).
intros r1 b; case b; auto with stalmarck.
intros l0 H' H'0 H'1.
case (TautoRTauto e).
intros H'3 H'4; apply H'4; auto with stalmarck.
case (rTautotTauto (norm e)).
intros H'5 H'6; apply H'6; auto with stalmarck.
red in |- *; rewrite H'1.
apply stalmarckGivesValidEquation with (S := addEq (r, rZFalse) nil); auto with stalmarck.
generalize
 (addEqMemCorrect (rArrayInit vM (fun _ : rNat => class nil)) r rZFalse nil).
rewrite H'; auto with stalmarck.
intros H'2; apply H'2; auto with stalmarck.
apply rIwF; auto with stalmarck.
exact initCorrect; auto with stalmarck.
CaseEq (evalTraceF T r1).
intros r2 b0; case b0; auto with stalmarck.
intros l0 H' l1 H'0 H'1 H'2.
case (TautoRTauto e).
intros H'3 H'4; apply H'4; auto with stalmarck.
case (rTautotTauto (norm e)).
intros H'5 H'6; apply H'6; auto with stalmarck.
red in |- *; rewrite H'2.
generalize (TraceCorrect r1 T l).
rewrite H'; auto with stalmarck.
generalize
 (addEqMemCorrect (rArrayInit vM (fun _ : rNat => class nil)) r rZFalse nil).
rewrite H'0; auto with stalmarck.
intros H'7; Elimc H'7;
 [ intros H'7 H'8; Elimc H'8; intros H'8 H'9; Elimc H'9; intros H'9 H'10
 | idtac
 | idtac ]; auto with stalmarck.
intros H'11; lapply H'11;
 [ intros H'12; elim (H'12 (addEq (r, rZFalse) nil));
    [ intros S' E; Elimc E; intros H'13 H'14; clear H'11
    | clear H'11
    | clear H'11 ]
 | clear H'11 ]; auto with stalmarck.
apply stalmarckGivesValidEquation with (S := S'); auto with stalmarck.
apply fInTCorrect with (f := getT (buildL l)); auto with stalmarck.
intros n; apply getTCorrect; auto with stalmarck.
apply rIwF; auto with stalmarck.
exact initCorrect; auto with stalmarck.
Qed.
Transparent addEqMem.
Transparent doTripletF.
Transparent interMem.

(* How to prove a\/ ~a *)

Local Definition t1 :
  Tautology (Node Or (V (rnext zero)) (normalize.N (V (rnext zero)))) :=
  checkTrace (Node Or (V (rnext zero)) (normalize.N (V (rnext zero))))
    (seqTrace
       (tripletTrace
          (Triplet rAnd (rZPlus (rnext (rnext zero))) 
             (rZMinus (rnext zero)) (rZPlus (rnext zero)))) emptyTrace).


(* A function to check trace *)

Definition checkTracef (e : Expr) (T : Trace) :=
  match makeTriplets (norm e) with
  | tRC L r n =>
      match fInT (getT (buildL L)) T with
      | true =>
          match addEqMem (rArrayInit _ (fun r => class nil)) r rZFalse with
          | triple Ar1 true L1 => true
          | triple Ar1 false L1 =>
              match evalTraceF T Ar1 with
              | triple Ar' false L => false
              | triple Ar' true L => true
              end
          end
      | false => false
      end
  end.
