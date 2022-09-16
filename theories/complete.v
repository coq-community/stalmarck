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
                                                                           
          Stalmarck  :    stalmarck                                        
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 The proof of completness of the algorithm *)
Require Import PolyListAux.
Require Import makeTriplet.
Require Export stalmarck.

Definition stateAssignedOn (S : State) (L : list triplet) :=
  forall a : rZ,
  In a (varTriplets L) -> eqStateRz S a rZTrue \/ eqStateRz S a rZFalse.

Lemma stateAssignedProp1 :
 forall (S : State) (L : list triplet),
 stateAssignedOn S L ->
 forall a b : rZ,
 In a (varTriplets L) ->
 In b (varTriplets L) -> eqStateRz S a b \/ eqStateRz S a (rZComp b).
unfold stateAssignedOn in |- *; intros S L H a b Ha Hb.
elim (H a Ha); elim (H b Hb); intros H1 H2.
left; apply eqStateRzTrans with (b := rZTrue); auto with stalmarck.
right; apply eqStateRzTrans with (b := rZTrue); auto with stalmarck.
cut (rZTrue = rZComp rZFalse); [ intros T; rewrite T | simpl in |- * ]; auto with stalmarck.
right; apply eqStateRzTrans with (b := rZFalse); auto with stalmarck.
cut (rZFalse = rZComp rZTrue); [ intros T; rewrite T | simpl in |- * ]; auto with stalmarck.
left; apply eqStateRzTrans with (b := rZFalse); auto with stalmarck.
Qed.

Lemma stateAssignedProp2 :
 forall (S : State) (L : list triplet),
 stateAssignedOn S L ->
 forall a b : rZ,
 inTriplets a L ->
 inTriplets b L -> eqStateRz S a b \/ eqStateRz S a (rZComp b).
intros S L H a b Ha Hb.
case (inTripletsVarTriplet L a Ha); case (inTripletsVarTriplet L b Hb);
 intros H1 H2.
apply (stateAssignedProp1 S L); auto with stalmarck.
lapply (stateAssignedProp1 S L H a (rZComp b) H2); auto with stalmarck.
rewrite (rZCompInv b); auto with stalmarck; intros Z; elim Z; simpl in |- *; auto with stalmarck.
lapply (stateAssignedProp1 S L H (rZComp a) b H2); auto with stalmarck.
intros Z; elim Z; intros Z1; auto with stalmarck; right; rewrite <- (rZCompInv a); auto with stalmarck.
rewrite <- (rZCompInv a); rewrite <- (rZCompInv b).
lapply (stateAssignedProp1 S L H (rZComp a) (rZComp b) H2); auto with stalmarck.
intros Z; elim Z; simpl in |- *; auto with stalmarck.
Qed.

Theorem stateAssignedDoTriplet :
 forall (S : State) (L : list triplet),
 stateAssignedOn S L ->
 forall t : triplet,
 In t L ->
 exists u : rZ * rZ,
   match u with
   | (a, b) => inTriplets a L /\ inTriplets b L
   end /\ doTripletP S t (addEq u S).
unfold stateAssignedOn in |- *; intros S L H t; case t; intros b p q r Ht.
cut (inTriplets p L); [ intros Hp | apply inTripletsIn with (2 := Ht) ];
 simpl in |- *; auto with stalmarck.
cut (inTriplets r L); [ intros Hr | apply inTripletsIn with (2 := Ht) ];
 simpl in |- *; auto with stalmarck.
cut (inTriplets (rZComp r) L);
 [ intros Hr2 | apply inTripletsIn with (2 := Ht) ]; 
 simpl in |- *; auto with stalmarck.
cut (inTriplets rZFalse L); [ intros Hz | apply inTripletsFalse ]; auto with stalmarck.
elim (H q);
 [ intros Hq; case b
 | intros Hq; case b
 | apply varTripletTriplet2 with (1 := Ht) ]; auto with stalmarck.
exists (p, r); simpl in |- *; split; [ split | apply doTripletAndPqT ]; auto with stalmarck.
exists (p, r); simpl in |- *; split; [ split | apply doTripletEqPqT ]; auto with stalmarck.
exists (p, rZFalse); simpl in |- *; split; [ split | apply doTripletAndPqF ];
 auto with stalmarck.
exists (p, rZComp r); simpl in |- *; split; [ split | apply doTripletEqPqF ];
 auto with stalmarck.
Qed.

Definition RealizeTripletsDec :
  forall (f : rNat -> bool) (L : list triplet),
  {realizeTriplets f L} + {~ realizeTriplets f L}.
simple induction L.
left; auto with stalmarck.
intros t L' HR.
elim HR; intros H.
cut (tEval f t = tEval f t); auto with stalmarck; pattern (tEval f t) at 2 in |- *;
 case (tEval f t).
intros Ht; left; auto with stalmarck.
intros Ht; right; unfold realizeTriplets in |- *; red in |- *; intros Abs.
absurd (tEval f t = true); auto with stalmarck.
rewrite Ht; simpl in |- *; auto with bool stalmarck.
apply Abs; simpl in |- *; auto with stalmarck.
right; red in |- *; intros Abs.
absurd (realizeTriplets f L'); auto with stalmarck;
 apply realizeTripletIncl with (L1 := t :: L'); auto with datatypes stalmarck.
Qed.

Lemma negRealizeTriplets :
 forall (f : rNat -> bool) (L : list triplet),
 ~ realizeTriplets f L -> ex (fun t : triplet => In t L /\ tEval f t = false).
simple induction L.
intros Abs; absurd (realizeTriplets f nil); auto with stalmarck.
intros t L' HR Abs.
cut (tEval f t = tEval f t); auto with stalmarck; pattern (tEval f t) at 2 in |- *;
 case (tEval f t).
intros Ht.
case (RealizeTripletsDec f L'); intros HL'.
absurd (realizeTriplets f (t :: L')); auto with stalmarck.
elim (HR HL'); intros t0 H; elim H; exists t0; simpl in |- *; auto with stalmarck.
intros H; exists t; auto with datatypes stalmarck.
Qed.

Definition eqStateRzContrDec2 :
  forall S : State, {contradictory S} + {~ contradictory S}.
intros S; case (eqStateRzContrDec S); intros A; unfold contradictory in |- *;
 [ left | right; red in |- *; intros B ].
exists (rZPlus zero); auto with stalmarck.
elim B; intros a Ha; auto with stalmarck.
absurd (forall a b : rZ, eqStateRz S a b); auto with stalmarck.
intros c b; apply (eqStateRzContr a); auto with stalmarck.
Qed.

Theorem stateAssignContrad :
 forall (S : State) (L : list triplet),
 stateAssignedOn S L ->
 forall a b : rZ,
 validEquation L a b ->
 eqStateRz S a (rZComp b) ->
 ex (fun S' : State => doTripletsP S L S' /\ contradictory S').
intros S L H a b Hab1 Hab2.
case (eqStateRzContrDec2 S); intros HS.
exists S; auto with stalmarck.
elim (Realizable2 S HS); intros f Hf; elim Hf; intros Hf1 Hf2.
elim (negRealizeTriplets f L);
 [ intros t Ht; elim Ht; intros Ht1 Ht2 | idtac ].
elim (stateAssignedDoTriplet S L H t Ht1); intros p; case p; intros c d T;
 elim T; intros T2 HS'; elim T2; intros Hc Hd.
exists (addEq (c, d) S); split; auto with stalmarck.
apply doTripletsTrans with (t := t) (S2 := addEq (c, d) S); auto with stalmarck.
unfold contradictory in |- *; exists d.
apply eqStateRzTrans with (b := c); auto with stalmarck.
cut (eqStateRz S c (rZComp d)); auto with stalmarck.
elim (stateAssignedProp2 S L H c d); auto with stalmarck.
intros Hcd.
elim (realizeStateEvalEquiv f S (addEq (c, d) S) t); auto with stalmarck; intros Thm1 Thm2.
rewrite Ht2 in Thm1; absurd (false = true); [ auto with bool  stalmarck| apply Thm1 ].
apply realizeStateAddEq; auto with stalmarck.
eapply realizeStateInv; eauto with stalmarck.
red in |- *; intros Abs; unfold validEquation in Hab1.
lapply (realizeStateInv f S Hf1 a (rZComp b)); auto with stalmarck.
rewrite (Hab1 f Abs Hf2); rewrite (rZEvalCompInv b f).
case (rZEval f b); auto with bool stalmarck.
Qed.
Require Import Arith.

Fixpoint nthTail (n : nat) : list rZ -> list rZ :=
  fun l : list rZ =>
  match n, l with
  | O, l => l
  | S n', nil => nil
  | S n', t :: l' => nthTail n' l'
  end.

Fixpoint myNth (n : nat) (l : list rZ) {struct l} : 
 rZ -> rZ :=
  fun default =>
  match n, l with
  | O, x :: l' => x
  | S m, x :: t => myNth m t default
  | _, _ => default
  end.

Lemma nthTailProp1 :
 forall (n : nat) (l : list rZ),
 n < length l -> nthTail n l = myNth n l rZTrue :: nthTail (S n) l.
simple induction n.
intros l; case l; simpl in |- *; intros; auto with stalmarck; absurd (0 < 0);
 auto with arith stalmarck.
intros n' HR l; case l; simpl in |- *;
 [ intros H; absurd (S n' < 0) | intros t l' H; rewrite (HR l') ];
 auto with arith stalmarck.
Qed.

Lemma nthTailProp2 :
 forall (n : nat) (l : list rZ), length l <= n -> nthTail n l = nil.
simple induction n.
intros l; case l; simpl in |- *; auto with stalmarck; intros t l' H;
 absurd (S (length l') <= 0); auto with arith stalmarck.
intros n' HR l; case l; simpl in |- *; auto with stalmarck.
intros t l' H; rewrite (HR l'); auto with arith stalmarck.
Qed.

Lemma nthTailProp3 :
 forall (n : nat) (l : list rZ),
 length l <= n -> nthTail n l = nthTail (S n) l.
intros n l H; rewrite (nthTailProp2 n l H); apply sym_eq; apply nthTailProp2;
 auto with arith stalmarck.
Qed.

Lemma DilemmaContradAux :
 forall (n : nat) (S : State) (L : list triplet) (a b : rZ),
 validEquation L a b ->
 eqStateRz S a (rZComp b) ->
 (forall a : rZ,
  In a (nthTail n (varTriplets L)) ->
  eqStateRz S a rZTrue \/ eqStateRz S a rZFalse) ->
 ex (fun S' : State => stalmarckP S L S' /\ contradictory S').
simple induction n.
simpl in |- *; intros S L a b V Eq H;
 elim (stateAssignContrad S L H a b V Eq); intros S' HS'.
elim HS'; intros HS'1 HS'2; exists S'; auto with stalmarck.
intros n' HR S L a b V Eq H.
elim (Nat.le_gt_cases (length (varTriplets L)) n'); intros Hn'.
apply (HR S L a b); auto with stalmarck.
rewrite (nthTailProp3 n' (varTriplets L)); auto with stalmarck.
elim (HR (addEq (myNth n' (varTriplets L) rZTrue, rZTrue) S) L a b); auto with stalmarck.
intros S1 HS1; elim HS1; intros HS11 HS12.
elim (HR (addEq (myNth n' (varTriplets L) rZTrue, rZFalse) S) L a b); auto with stalmarck.
intros S2 HS2; elim HS2; intros HS21 HS22.
exists (interState S1 S2); split; auto with stalmarck.
apply
 stalmarckPSplit
  with
    (a := myNth n' (varTriplets L) rZTrue)
    (b := rZTrue)
    (S2 := S1)
    (S3 := S2); auto with stalmarck.
unfold interState in |- *; case (eqStateRzContrDec S1); auto with stalmarck.
intros Abs; absurd (forall a b : rZ, eqStateRz S1 a b); auto with stalmarck.
intros c d; unfold contradictory in HS12; elim HS12; intros e He;
 eapply eqStateRzContr; eauto with stalmarck.
rewrite (nthTailProp1 n' (varTriplets L)); auto with stalmarck; simpl in |- *; intros c Hc;
 elim Hc; intros Hc'.
rewrite Hc'; right; auto with stalmarck.
elim (H c); [ left | right | idtac ]; auto with stalmarck.
rewrite (nthTailProp1 n' (varTriplets L)); auto with stalmarck; simpl in |- *; intros c Hc;
 elim Hc; intros Hc'.
rewrite Hc'; left; auto with stalmarck.
elim (H c); [ left | right | idtac ]; auto with stalmarck.
Qed.

Theorem DilemmaContrad :
 forall (S : State) (L : list triplet) (a b : rZ),
 validEquation L a b ->
 eqStateRz S a (rZComp b) ->
 ex (fun S' : State => stalmarckP S L S' /\ contradictory S').
intros S L a b V Eq;
 apply (DilemmaContradAux (length (varTriplets L)) S L a b); 
 auto with stalmarck.
rewrite (nthTailProp2 (length (varTriplets L)) (varTriplets L)); auto with stalmarck.
intros a' H; inversion H.
Qed.

Theorem stalmarckComplete :
 forall e : Expr,
 Tautology e ->
 match makeTriplets (norm e) with
 | tRC l s n =>
     ex
       (fun S : State =>
        stalmarckP (addEq (s, rZFalse) nil) l S /\ contradictory S)
 end.
intros e; generalize (refl_equal (makeTriplets (norm e)));
 pattern (makeTriplets (norm e)) at -2 in |- *; case (makeTriplets (norm e)).
intros l r r0 H H1.
elim (DilemmaContrad (addEq (r, rZFalse) nil) l r rZTrue); auto with stalmarck.
intros S HS; exists S; auto with stalmarck.
elim (TautoRTauto e); intros Thm1 Thm2.
elim (rTautotTauto (norm e)); intros Thm3 Thm4.
generalize Thm3; unfold tTautology in |- *; rewrite <- H; simpl in |- *; auto with stalmarck.
Qed.
