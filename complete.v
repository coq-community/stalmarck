
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
left; apply eqStateRzTrans with (b := rZTrue); auto.
right; apply eqStateRzTrans with (b := rZTrue); auto.
cut (rZTrue = rZComp rZFalse); [ intros T; rewrite T | simpl in |- * ]; auto.
right; apply eqStateRzTrans with (b := rZFalse); auto.
cut (rZFalse = rZComp rZTrue); [ intros T; rewrite T | simpl in |- * ]; auto.
left; apply eqStateRzTrans with (b := rZFalse); auto.
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
apply (stateAssignedProp1 S L); auto.
lapply (stateAssignedProp1 S L H a (rZComp b) H2); auto.
rewrite (rZCompInv b); auto; intros Z; elim Z; simpl in |- *; auto.
lapply (stateAssignedProp1 S L H (rZComp a) b H2); auto.
intros Z; elim Z; intros Z1; auto; right; rewrite <- (rZCompInv a); auto.
rewrite <- (rZCompInv a); rewrite <- (rZCompInv b).
lapply (stateAssignedProp1 S L H (rZComp a) (rZComp b) H2); auto.
intros Z; elim Z; simpl in |- *; auto.
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
 simpl in |- *; auto.
cut (inTriplets r L); [ intros Hr | apply inTripletsIn with (2 := Ht) ];
 simpl in |- *; auto.
cut (inTriplets (rZComp r) L);
 [ intros Hr2 | apply inTripletsIn with (2 := Ht) ]; 
 simpl in |- *; auto.
cut (inTriplets rZFalse L); [ intros Hz | apply inTripletsFalse ]; auto.
elim (H q);
 [ intros Hq; case b
 | intros Hq; case b
 | apply varTripletTriplet2 with (1 := Ht) ]; auto.
exists (p, r); simpl in |- *; split; [ split | apply doTripletAndPqT ]; auto.
exists (p, r); simpl in |- *; split; [ split | apply doTripletEqPqT ]; auto.
exists (p, rZFalse); simpl in |- *; split; [ split | apply doTripletAndPqF ];
 auto.
exists (p, rZComp r); simpl in |- *; split; [ split | apply doTripletEqPqF ];
 auto.
Qed.

Definition RealizeTripletsDec :
  forall (f : rNat -> bool) (L : list triplet),
  {realizeTriplets f L} + {~ realizeTriplets f L}.
simple induction L.
left; auto.
intros t L' HR.
elim HR; intros H.
cut (tEval f t = tEval f t); auto; pattern (tEval f t) at 2 in |- *;
 case (tEval f t).
intros Ht; left; auto.
intros Ht; right; unfold realizeTriplets in |- *; red in |- *; intros Abs.
absurd (tEval f t = true); auto.
rewrite Ht; simpl in |- *; auto with bool.
apply Abs; simpl in |- *; auto.
right; red in |- *; intros Abs.
absurd (realizeTriplets f L'); auto;
 apply realizeTripletIncl with (L1 := t :: L'); auto with datatypes.
Qed.

Lemma negRealizeTriplets :
 forall (f : rNat -> bool) (L : list triplet),
 ~ realizeTriplets f L -> ex (fun t : triplet => In t L /\ tEval f t = false).
simple induction L.
intros Abs; absurd (realizeTriplets f nil); auto.
intros t L' HR Abs.
cut (tEval f t = tEval f t); auto; pattern (tEval f t) at 2 in |- *;
 case (tEval f t).
intros Ht.
case (RealizeTripletsDec f L'); intros HL'.
absurd (realizeTriplets f (t :: L')); auto.
elim (HR HL'); intros t0 H; elim H; exists t0; simpl in |- *; auto.
intros H; exists t; auto with datatypes.
Qed.

Definition eqStateRzContrDec2 :
  forall S : State, {contradictory S} + {~ contradictory S}.
intros S; case (eqStateRzContrDec S); intros A; unfold contradictory in |- *;
 [ left | right; red in |- *; intros B ].
exists (rZPlus zero); auto.
elim B; intros a Ha; auto.
absurd (forall a b : rZ, eqStateRz S a b); auto.
intros c b; apply (eqStateRzContr a); auto.
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
exists S; auto.
elim (Realizable2 S HS); intros f Hf; elim Hf; intros Hf1 Hf2.
elim (negRealizeTriplets f L);
 [ intros t Ht; elim Ht; intros Ht1 Ht2 | idtac ].
elim (stateAssignedDoTriplet S L H t Ht1); intros p; case p; intros c d T;
 elim T; intros T2 HS'; elim T2; intros Hc Hd.
exists (addEq (c, d) S); split; auto.
apply doTripletsTrans with (t := t) (S2 := addEq (c, d) S); auto.
unfold contradictory in |- *; exists d.
apply eqStateRzTrans with (b := c); auto.
cut (eqStateRz S c (rZComp d)); auto.
elim (stateAssignedProp2 S L H c d); auto.
intros Hcd.
elim (realizeStateEvalEquiv f S (addEq (c, d) S) t); auto; intros Thm1 Thm2.
rewrite Ht2 in Thm1; absurd (false = true); [ auto with bool | apply Thm1 ].
apply realizeStateAddEq; auto.
eapply realizeStateInv; eauto.
red in |- *; intros Abs; unfold validEquation in Hab1.
lapply (realizeStateInv f S Hf1 a (rZComp b)); auto.
rewrite (Hab1 f Abs Hf2); rewrite (rZEvalCompInv b f).
case (rZEval f b); auto with bool.
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
intros l; case l; simpl in |- *; intros; auto; absurd (0 < 0);
 auto with arith.
intros n' HR l; case l; simpl in |- *;
 [ intros H; absurd (S n' < 0) | intros t l' H; rewrite (HR l') ];
 auto with arith.
Qed.

Lemma nthTailProp2 :
 forall (n : nat) (l : list rZ), length l <= n -> nthTail n l = nil.
simple induction n.
intros l; case l; simpl in |- *; auto; intros t l' H;
 absurd (S (length l') <= 0); auto with arith.
intros n' HR l; case l; simpl in |- *; auto.
intros t l' H; rewrite (HR l'); auto with arith.
Qed.

Lemma nthTailProp3 :
 forall (n : nat) (l : list rZ),
 length l <= n -> nthTail n l = nthTail (S n) l.
intros n l H; rewrite (nthTailProp2 n l H); apply sym_eq; apply nthTailProp2;
 auto with arith.
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
elim HS'; intros HS'1 HS'2; exists S'; auto.
intros n' HR S L a b V Eq H.
elim (le_or_lt (length (varTriplets L)) n'); intros Hn'.
apply (HR S L a b); auto.
rewrite (nthTailProp3 n' (varTriplets L)); auto.
elim (HR (addEq (myNth n' (varTriplets L) rZTrue, rZTrue) S) L a b); auto.
intros S1 HS1; elim HS1; intros HS11 HS12.
elim (HR (addEq (myNth n' (varTriplets L) rZTrue, rZFalse) S) L a b); auto.
intros S2 HS2; elim HS2; intros HS21 HS22.
exists (interState S1 S2); split; auto.
apply
 stalmarckPSplit
  with
    (a := myNth n' (varTriplets L) rZTrue)
    (b := rZTrue)
    (S2 := S1)
    (S3 := S2); auto.
unfold interState in |- *; case (eqStateRzContrDec S1); auto.
intros Abs; absurd (forall a b : rZ, eqStateRz S1 a b); auto.
intros c d; unfold contradictory in HS12; elim HS12; intros e He;
 eapply eqStateRzContr; eauto.
rewrite (nthTailProp1 n' (varTriplets L)); auto; simpl in |- *; intros c Hc;
 elim Hc; intros Hc'.
rewrite Hc'; right; auto.
elim (H c); [ left | right | idtac ]; auto.
rewrite (nthTailProp1 n' (varTriplets L)); auto; simpl in |- *; intros c Hc;
 elim Hc; intros Hc'.
rewrite Hc'; left; auto.
elim (H c); [ left | right | idtac ]; auto.
Qed.

Theorem DilemmaContrad :
 forall (S : State) (L : list triplet) (a b : rZ),
 validEquation L a b ->
 eqStateRz S a (rZComp b) ->
 ex (fun S' : State => stalmarckP S L S' /\ contradictory S').
intros S L a b V Eq;
 apply (DilemmaContradAux (length (varTriplets L)) S L a b); 
 auto.
rewrite (nthTailProp2 (length (varTriplets L)) (varTriplets L)); auto.
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
elim (DilemmaContrad (addEq (r, rZFalse) nil) l r rZTrue); auto.
intros S HS; exists S; auto.
elim (TautoRTauto e); intros Thm1 Thm2.
elim (rTautotTauto (norm e)); intros Thm3 Thm4.
generalize Thm3; unfold tTautology in |- *; rewrite <- H; simpl in |- *; auto.
Qed.
