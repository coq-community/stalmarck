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

(** * doTriplet

Pierre Letouzey & Laurent Thery

One step propagation
*)

From Stalmarck Require Export unionState.
From Stalmarck Require Export stateExtra.

(*We define the Stalmarck One Step Saturation as a relation *)

Inductive doTripletP (S : State) : triplet -> State -> Prop :=
  | doTripletAndPpmq :
      forall p q r : rZ,
      eqStateRz S p (rZComp q) ->
      doTripletP S (Triplet rAnd p q r)
        (addEq (q, rZTrue) (addEq (r, rZFalse) S))
  | doTripletAndPpmr :
      forall p q r : rZ,
      eqStateRz S p (rZComp r) ->
      doTripletP S (Triplet rAnd p q r)
        (addEq (q, rZFalse) (addEq (r, rZTrue) S))
  | doTripletAndPqr :
      forall p q r : rZ,
      eqStateRz S q r -> doTripletP S (Triplet rAnd p q r) (addEq (p, r) S)
  | doTripletAndPqmr :
      forall p q r : rZ,
      eqStateRz S q (rZComp r) ->
      doTripletP S (Triplet rAnd p q r) (addEq (p, rZFalse) S)
  | doTripletAndPpT :
      forall p q r : rZ,
      eqStateRz S p rZTrue ->
      doTripletP S (Triplet rAnd p q r)
        (addEq (q, rZTrue) (addEq (r, rZTrue) S))
  | doTripletAndPqT :
      forall p q r : rZ,
      eqStateRz S q rZTrue ->
      doTripletP S (Triplet rAnd p q r) (addEq (p, r) S)
  | doTripletAndPqF :
      forall p q r : rZ,
      eqStateRz S q rZFalse ->
      doTripletP S (Triplet rAnd p q r) (addEq (p, rZFalse) S)
  | doTripletAndPrT :
      forall p q r : rZ,
      eqStateRz S r rZTrue ->
      doTripletP S (Triplet rAnd p q r) (addEq (p, q) S)
  | doTripletAndPrF :
      forall p q r : rZ,
      eqStateRz S r rZFalse ->
      doTripletP S (Triplet rAnd p q r) (addEq (p, rZFalse) S)
  | doTripletEqPpq :
      forall p q r : rZ,
      eqStateRz S p q ->
      doTripletP S (Triplet rEq p q r) (addEq (r, rZTrue) S)
  | doTripletEqPpmq :
      forall p q r : rZ,
      eqStateRz S p (rZComp q) ->
      doTripletP S (Triplet rEq p q r) (addEq (r, rZFalse) S)
  | doTripletEqPpr :
      forall p q r : rZ,
      eqStateRz S p r ->
      doTripletP S (Triplet rEq p q r) (addEq (q, rZTrue) S)
  | doTripletEqPpmr :
      forall p q r : rZ,
      eqStateRz S p (rZComp r) ->
      doTripletP S (Triplet rEq p q r) (addEq (q, rZFalse) S)
  | doTripletEqPqr :
      forall p q r : rZ,
      eqStateRz S q r ->
      doTripletP S (Triplet rEq p q r) (addEq (p, rZTrue) S)
  | doTripletEqPqmr :
      forall p q r : rZ,
      eqStateRz S q (rZComp r) ->
      doTripletP S (Triplet rEq p q r) (addEq (p, rZFalse) S)
  | doTripletEqPpT :
      forall p q r : rZ,
      eqStateRz S p rZTrue ->
      doTripletP S (Triplet rEq p q r) (addEq (q, r) S)
  | doTripletEqPpF :
      forall p q r : rZ,
      eqStateRz S p rZFalse ->
      doTripletP S (Triplet rEq p q r) (addEq (q, rZComp r) S)
  | doTripletEqPqT :
      forall p q r : rZ,
      eqStateRz S q rZTrue ->
      doTripletP S (Triplet rEq p q r) (addEq (p, r) S)
  | doTripletEqPqF :
      forall p q r : rZ,
      eqStateRz S q rZFalse ->
      doTripletP S (Triplet rEq p q r) (addEq (p, rZComp r) S)
  | doTripletEqPrT :
      forall p q r : rZ,
      eqStateRz S r rZTrue ->
      doTripletP S (Triplet rEq p q r) (addEq (p, q) S)
  | doTripletEqPrF :
      forall p q r : rZ,
      eqStateRz S r rZFalse ->
      doTripletP S (Triplet rEq p q r) (addEq (p, rZComp q) S).
#[export] Hint Resolve doTripletAndPpmq doTripletAndPpmr doTripletAndPqr
  doTripletAndPqmr doTripletAndPpT doTripletAndPqT doTripletAndPqF
  doTripletAndPrT doTripletAndPrF doTripletEqPpq doTripletEqPpmq
  doTripletEqPpr doTripletEqPpmr doTripletEqPqr doTripletEqPqmr
  doTripletEqPpT doTripletEqPpF doTripletEqPqT doTripletEqPqF doTripletEqPrT
  doTripletEqPrF : stalmarck.

Theorem doTripletEqAux1 :
 forall (p q : rZ) (S1 S3 : State) (t : triplet),
 doTripletP S1 t (addEq (p, q) S1) ->
 eqState S1 S3 ->
 doTripletP S3 t (addEq (p, q) S3) ->
 exists S4 : State, doTripletP S3 t S4 /\ eqState S4 (addEq (p, q) S1).
intros p q S1 S3 t H' H'0 H'1; exists (addEq (p, q) S3); split; auto with stalmarck.
Qed.

Theorem doTripletEqAux2 :
 forall (p q r s : rZ) (S1 S3 : State) (t : triplet),
 doTripletP S1 t (addEq (p, q) (addEq (r, s) S1)) ->
 eqState S1 S3 ->
 doTripletP S3 t (addEq (p, q) (addEq (r, s) S3)) ->
 ex
   (fun S4 : State =>
    doTripletP S3 t S4 /\ eqState S4 (addEq (p, q) (addEq (r, s) S1))).
intros p q r s S1 S3 t H' H'0; exists (addEq (p, q) (addEq (r, s) S3)); split;
 auto with stalmarck.
Qed.
(* proagation is compatible with equality *)

Theorem doTripletEqCompEx :
 forall (S1 S2 S3 : State) (t : triplet),
 doTripletP S1 t S2 ->
 eqState S1 S3 -> exists S4 : State, doTripletP S3 t S4 /\ eqState S4 S2.
intros S1 S2 S3 t H' H'1; inversion H';
 apply doTripletEqAux2 || apply doTripletEqAux1; auto with stalmarck;
 generalize (eqStateEq _ _ _ _ H'1 H); auto with stalmarck.
Qed.

Theorem doTripletUnionEx1 :
 forall (p q : rZ) (S1 : State) (t : triplet),
 doTripletP S1 t (addEq (p, q) S1) ->
 exists S3 : State, addEq (p, q) S1 = unionState S3 S1.
intros p q S1 t H'; exists ((p, q) :: nil); auto with stalmarck.
Qed.

Theorem doTripletUnionEx2 :
 forall (p q r s : rZ) (S1 : State) (t : triplet),
 doTripletP S1 t (addEq (p, q) (addEq (r, s) S1)) ->
 exists S3 : State, addEq (p, q) (addEq (r, s) S1) = unionState S3 S1.
intros p q r s S1 t H'; exists ((p, q) :: (r, s) :: nil); auto with stalmarck.
Qed.
(* Doing  propagation we just add equations *)

Theorem doTripletUnionEx :
 forall (S1 S2 : State) (t : triplet),
 doTripletP S1 t S2 -> exists S3 : State, S2 = unionState S3 S1.
intros S1 S2 t H'; inversion H';
 apply doTripletUnionEx2 with (t := t) ||
   apply doTripletUnionEx1 with (t := t); auto with stalmarck; rewrite H1; 
 auto with stalmarck.
Qed.
(* The result is always bigger *)

Theorem doTripletIncl :
 forall (S1 S2 : State) (t : triplet), doTripletP S1 t S2 -> inclState S1 S2.
intros S1 S2 t H'.
case (doTripletUnionEx S1 S2 t); auto with stalmarck.
intros x H'0; rewrite H'0; auto with stalmarck.
Qed.

Theorem doTripletUnionAux1 :
 forall (p q : rZ) (S1 S3 : State) (t : triplet),
 doTripletP (unionState S3 S1) t (addEq (p, q) (unionState S3 S1)) ->
 exists S4 : State,
   doTripletP (unionState S3 S1) t S4 /\
   eqState S4 (unionState S3 (addEq (p, q) S1)).
intros p q S1 S3 t H'; exists (addEq (p, q) (unionState S3 S1)); split; auto with stalmarck.
apply eqStateTrans with (unionState (unionState ((p, q) :: nil) S3) S1); auto with stalmarck.
apply eqStateTrans with (unionState (unionState S3 ((p, q) :: nil)) S1); auto with stalmarck.
apply eqStateSym; auto with stalmarck.
replace (addEq (p, q) S1) with (unionState ((p, q) :: nil) S1); auto with stalmarck.
apply unionStateAssoc; auto with stalmarck.
Qed.

Theorem doTripletUnionAux2 :
 forall (p q r s : rZ) (S1 S3 : State) (t : triplet),
 doTripletP (unionState S3 S1) t
   (addEq (p, q) (addEq (r, s) (unionState S3 S1))) ->
 exists S4 : State,
   doTripletP (unionState S3 S1) t S4 /\
   eqState S4 (unionState S3 (addEq (p, q) (addEq (r, s) S1))).
intros p q r s S1 S3 t H';
 exists (addEq (p, q) (addEq (r, s) (unionState S3 S1))); 
 split; auto with stalmarck.
apply
 eqStateTrans with (unionState (unionState ((p, q) :: (r, s) :: nil) S3) S1);
 auto with stalmarck.
apply
 eqStateTrans with (unionState (unionState S3 ((p, q) :: (r, s) :: nil)) S1);
 auto with stalmarck.
apply
 eqStateTrans with (unionState S3 (unionState ((p, q) :: (r, s) :: nil) S1));
 auto with stalmarck.
apply eqStateSym; auto with stalmarck.
apply unionStateAssoc.
Qed.
(* Propagation is a congruence *)

Theorem doTripletCongruentEx :
 forall (S1 S2 S3 : State) (t : triplet),
 doTripletP S1 t S2 ->
 exists S4 : State,
   doTripletP (unionState S3 S1) t S4 /\ eqState S4 (unionState S3 S2).
intros S1 S2 S3 t H'; inversion H';
 apply doTripletUnionAux2 || apply doTripletUnionAux1; 
 auto with stalmarck; generalize (eqStateIncl _ _ _ _ (unionStateInclR S3 S1) H); 
 auto with stalmarck.
Qed.
(* It is monotone *)

Theorem doTripletMonotoneEx :
 forall (S1 S2 S3 : State) (t : triplet),
 doTripletP S1 t S3 ->
 inclState S1 S2 -> exists S4 : State, doTripletP S2 t S4 /\ inclState S3 S4.
intros S1 S2 S3 t H' H'0.
elim (doTripletCongruentEx S1 S3 S2 t);
 [ intros S4 E; Elimc E; intros H'6 H'7 | idtac ]; 
 auto with stalmarck.
elim (doTripletEqCompEx (unionState S2 S1) S4 S2 t);
 [ intros S5 E; Elimc E; intros H'9 H'10 | idtac | idtac ]; 
 auto with stalmarck.
exists S5; split; auto with stalmarck.
apply inclStateTrans with (S2 := unionState S2 S3); auto with stalmarck.
apply inclStateEqStateComp with (S1 := S4) (S3 := S4); auto with stalmarck.
red in |- *; auto with stalmarck.
Qed.
(* It is confluence *)

Theorem doTripletConflEx :
 forall (t1 t2 : triplet) (S1 S2 S3 : State),
 doTripletP S1 t1 S2 ->
 doTripletP S1 t2 S3 ->
 exists S4 : State,
   (exists S5 : State,
      doTripletP S2 t2 S4 /\ doTripletP S3 t1 S5 /\ eqState S4 S5).
intros t1 t2 S1 S2 S3 H' H'0.
elim (doTripletUnionEx S1 S2 t1); [ intros S4 E; rewrite E | idtac ]; auto with stalmarck.
elim (doTripletUnionEx S1 S3 t2); [ intros S5 E0; rewrite E0 | idtac ]; auto with stalmarck.
elim (doTripletCongruentEx S1 S2 S5 t1);
 [ intros S6 E1; Elimc E1; intros H'6 H'7 | idtac ]; 
 auto with stalmarck.
elim (doTripletCongruentEx S1 S3 S4 t2);
 [ intros S7 E1; Elimc E1; intros H'8 H'9 | idtac ]; 
 auto with stalmarck.
exists S7; exists S6; split; [ idtac | split ]; auto with stalmarck.
apply eqStateTrans with (S2 := unionState S4 S3); auto with stalmarck.
rewrite E0.
apply eqStateTrans with (S2 := unionState S5 S2); auto with stalmarck.
rewrite E.
apply eqStateTrans with (S2 := unionState (unionState S4 S5) S1); auto with stalmarck.
apply unionStateAssoc; auto with stalmarck.
apply eqStateTrans with (S2 := unionState (unionState S5 S4) S1); auto with stalmarck.
apply eqStateSym; auto with stalmarck.
apply unionStateAssoc; auto with stalmarck.
Qed.

Lemma realizeStateEvalAux1 :
 forall (f : rNat -> bool) (p q r s t u : rZ) (S : State)
   (EqS : eqStateRz S p q),
 (rZEval f p = rZEval f q ->
  rZEval f r = rZEval f s /\ rZEval f t = rZEval f u) ->
 realizeState f S -> realizeState f (addEq (r, s) (addEq (t, u) S)).
intros f p q r s t u S H' H'0 H'1.
Elimc H'0; [ intros H'3 H'4 | idtac ].
apply realizeStateAddEq; auto with stalmarck.
apply realizeStateInv with (S := S); auto with stalmarck.
Qed.

Lemma realizeStateEvalAux2 :
 forall (f : rNat -> bool) (p q r s : rZ) (S : State) (EqS : eqStateRz S p q),
 (rZEval f p = rZEval f q -> rZEval f r = rZEval f s) ->
 realizeState f S -> realizeState f (addEq (r, s) S).
intros f p q r s S H' H'0 H'1.
lapply H'0; [ intros H'2 | idtac ].
apply realizeStateAddEq; auto with stalmarck.
apply realizeStateInv with (S := S); auto with stalmarck.
Qed.
(* If the triplet is valid, we keep realizability while doing propagation *)

Theorem realizeStateEval :
 forall (f : rNat -> bool) (S1 S2 : State) (t : triplet),
 realizeState f S1 ->
 doTripletP S1 t S2 -> tEval f t = true -> f zero = true -> realizeState f S2.
intros f S1 S2 t H' H'0; elim H'0; simpl in |- *; auto with stalmarck;
 intros p q r H'1 H'2 H'3;
 apply realizeStateEvalAux1 with (1 := H'1) ||
   apply realizeStateEvalAux2 with (1 := H'1); auto with stalmarck;
 try rewrite rZEvalCompInv; try rewrite rZEvalCompInv; 
 generalize H'2; try repeat rewrite H'3; case (rZEval f p); 
 simpl in |- *; case (rZEval f q); simpl in |- *; case (rZEval f r);
 simpl in |- *; auto with stalmarck; try repeat rewrite H'3; auto with stalmarck.
Qed.

Lemma evalRealizeStateAux1 :
 forall (A : Prop) (f : rNat -> bool) (p q r s t u : rZ) 
   (S : State) (EqS : eqStateRz S p q),
 (rZEval f p = rZEval f q /\
  rZEval f r = rZEval f s /\ rZEval f t = rZEval f u -> A) ->
 realizeState f (addEq (r, s) (addEq (t, u) S)) -> A.
intros A f p q r s t u S H' H'0 H'1.
lapply H'0; [ intros H'2 | split; [ idtac | split ] ]; auto with stalmarck.
apply realizeStateInv with (S := S); auto with stalmarck.
apply realizeStateIncl with (1 := H'1); auto with stalmarck.
apply realizeStateInv with (1 := H'1); auto with stalmarck.
apply realizeStateInv with (1 := H'1); auto with stalmarck.
Qed.

Lemma evalRealizeStateAux2 :
 forall (A : Prop) (f : rNat -> bool) (p q r s : rZ) 
   (S : State) (EqS : eqStateRz S p q),
 (rZEval f p = rZEval f q /\ rZEval f r = rZEval f s -> A) ->
 realizeState f (addEq (r, s) S) -> A.
intros A f p q r s S H' H'0 H'1.
lapply H'0; [ intros H'2 | split ]; auto with stalmarck.
apply realizeStateInv with (S := S); auto with stalmarck.
apply realizeStateIncl with (1 := H'1); auto with stalmarck.
apply realizeStateInv with (1 := H'1); auto with stalmarck.
Qed.
(* Conversely if the result of a propagation is realizable this means that
   the triplet is valid *)

Theorem evalRealizeState :
 forall (f : rNat -> bool) (S1 S2 : State) (t : triplet),
 doTripletP S1 t S2 -> realizeState f S2 -> f zero = true -> tEval f t = true.
intros f S1 S2 t H'; elim H'; intros p q r H'1 H2 H'3;
 apply evalRealizeStateAux1 with (1 := H'1) (3 := H2) ||
   apply evalRealizeStateAux2 with (1 := H'1) (3 := H2);
 try rewrite rZEvalCompInv; try rewrite rZEvalCompInv; 
 simpl in |- *; case (rZEval f p); simpl in |- *; case (rZEval f q);
 simpl in |- *; case (rZEval f r); simpl in |- *; auto with stalmarck;
 try repeat rewrite H'3; auto with stalmarck; intuition.
Qed.
(* Prove that the semantic of doTriplet is correct *)

Theorem realizeStateEvalEquiv :
 forall (f : rNat -> bool) (S1 S2 : State) (t : triplet),
 doTripletP S1 t S2 ->
 realizeState f S1 ->
 f zero = true -> (realizeState f S2 <-> tEval f t = true).
intros f S1 S2 H' H'0; red in |- *.
split; intros H'1.
apply evalRealizeState with (1 := H'0); auto with stalmarck.
apply realizeStateEval with (2 := H'0); auto with stalmarck.
Qed.

Theorem doTripletBisIncl :
 forall (t : triplet) (S1 S2 : State),
 doTripletP S1 t S2 ->
 forall S3 : State, doTripletP S1 t S3 -> inclState S3 S2.
intros t S1 S2 H12 S3 H13.
apply realizeStateInclInv; intros f Pfzero Pf2; unfold realizeState in |- *;
 intros i j Pij; apply realizeStateInv with (S := S3); 
 auto with stalmarck.
cut (realizeState f S1); [ intros Pf1 | idtac ].
apply realizeStateEval with (S1 := S1) (t := t); auto with stalmarck.
apply evalRealizeState with (S1 := S1) (S2 := S2); auto with stalmarck.
apply realizeStateIncl with (S1 := S2); auto with stalmarck.
apply doTripletIncl with (t := t); auto with stalmarck.
Qed.
(*It does not matter which rule you apply *)

Theorem doTripletEq :
 forall (S1 S2 S3 : State) (t : triplet),
 doTripletP S1 t S2 -> doTripletP S1 t S3 -> eqState S2 S3.
intros S1 S2 S3 t H' H'0.
red in |- *; split; apply doTripletBisIncl with (S1 := S1) (t := t); auto with stalmarck.
Qed.
(* Monotony of the saturation *)

Theorem doTripletEqMonotone :
 forall (S1 S2 S3 S4 : State) (t : triplet),
 doTripletP S1 t S3 ->
 doTripletP S2 t S4 -> inclState S1 S2 -> inclState S3 S4.
intros S1 S2 S3 S4 t H' H'0 H'1.
elim (doTripletMonotoneEx S1 S2 S3 t);
 [ intros S5 E; Elimc E; intros H'8 H'9 | idtac | idtac ]; 
 auto with stalmarck.
apply inclStateEqStateComp with (S1 := S3) (S3 := S5); auto with stalmarck.
apply doTripletEq with (S1 := S2) (t := t); auto with stalmarck.
Qed.
(* It is compatible *)

Theorem doTripletEqComp :
 forall (t : triplet) (S1 S2 S3 S4 : State),
 doTripletP S1 t S3 -> doTripletP S2 t S4 -> eqState S1 S2 -> eqState S3 S4.
intros t S1 S2 S3 S4 H' H'0 H'1.
elim (doTripletEqCompEx S1 S3 S2 t);
 [ intros S5 E; Elimc E; intros H'8 H'9 | idtac | idtac ]; 
 auto with stalmarck.
apply eqStateTrans with (S2 := S5); auto with stalmarck.
apply doTripletEq with (S1 := S2) (t := t); auto with stalmarck.
Qed.
(* It is confluent *)

Theorem doTripletConfl :
 forall (t1 t2 : triplet) (S1 S2 S3 S4 S5 : State),
 doTripletP S1 t1 S2 ->
 doTripletP S2 t2 S4 ->
 doTripletP S1 t2 S3 -> doTripletP S3 t1 S5 -> eqState S4 S5.
intros t1 t2 S1 S2 S3 S4 S5 H' H'0 H'1 H'2.
elim (doTripletConflEx t1 t2 S1 S2 S3);
 [ intros S6 E; Elimc E; intros S7 E0; Elimc E0; intros H'10 H'11; Elimc H'11;
    intros H'12 H'13
 | idtac
 | idtac ]; auto with stalmarck.
apply eqStateTrans with (S2 := S6).
apply doTripletEqComp with (t := t2) (S1 := S2) (S2 := S2); auto with stalmarck.
apply eqStateTrans with (S2 := S7); auto with stalmarck.
apply doTripletEqComp with (t := t1) (S1 := S3) (S2 := S3); auto with stalmarck.
Qed.

Theorem doTripletInvolExAux1 :
 forall (tr : triplet) (p q : rZ) (S1 S3 : State),
 inclState (addEq (p, q) S1) S3 ->
 inclState S1 S3 ->
 doTripletP S3 tr (addEq (p, q) S3) ->
 ex (fun S4 : State => doTripletP S3 tr S4 /\ eqState S3 S4).
intros tr p q S1 S3 H' H'0 H'1; exists (addEq (p, q) S3); split; auto with stalmarck.
generalize (eqStateIncl (addEq (p, q) S1)); intros Eq1; red in |- *; auto 8 with stalmarck.
Qed.

Theorem doTripletInvolExAux2 :
 forall (tr : triplet) (p q r s : rZ) (S1 S3 : State),
 inclState (addEq (p, q) (addEq (r, s) S1)) S3 ->
 inclState S1 S3 ->
 doTripletP S3 tr (addEq (p, q) (addEq (r, s) S3)) ->
 ex (fun S4 : State => doTripletP S3 tr S4 /\ eqState S3 S4).
intros tr p q r s S1 S3 H' H'0 H'1; exists (addEq (p, q) (addEq (r, s) S3));
 split; auto with stalmarck.
generalize (eqStateIncl (addEq (p, q) (addEq (r, s) S1))); intros Eq1;
 red in |- *; auto 8 with stalmarck.
Qed.
(* A triplet is useful only once *)

Theorem doTripletInvolEx :
 forall (t : triplet) (S1 S2 S3 : State),
 doTripletP S1 t S2 ->
 inclState S2 S3 -> exists S4 : State, doTripletP S3 t S4 /\ eqState S3 S4.
intros t S1 S2 S3 H' H'0; (generalize (eqStateIncl S1); intros Eq0);
 cut (inclState S1 S3);
 [ idtac
 | apply inclStateTrans with (S2 := S2); auto with stalmarck;
    apply doTripletIncl with (t := t); auto with stalmarck ]; generalize H'0; 
 clear H'0; elim H'; intros p q r H'0 H'1 H'2;
 apply doTripletInvolExAux2 with (1 := H'1) ||
   apply doTripletInvolExAux1 with (1 := H'1); auto with stalmarck.
Qed.

Theorem doTripletInvol :
 forall (t : triplet) (S1 S2 S3 S4 : State),
 doTripletP S1 t S2 -> inclState S2 S3 -> doTripletP S3 t S4 -> eqState S3 S4.
intros t S1 S2 S3 S4 H' H'0 H'1.
elim (doTripletInvolEx t S1 S2 S3);
 [ intros S5 E; Elimc E; intros H'8 H'9 | idtac | idtac ]; 
 auto with stalmarck.
apply eqStateTrans with (S2 := S5); auto with stalmarck.
apply doTripletEqComp with (t := t) (S1 := S3) (S2 := S3); auto with stalmarck.
Qed.
