
(****************************************************************************
                                                                           
          Stalmarck  : BoolAux                                             
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Some standard properties  on booleans *)
Require Export Bool.

Lemma de_morgan1 : forall b1 b2 : bool, negb (b1 || b2) = negb b1 && negb b2.
simple destruct b1; simple destruct b2; simpl in |- *; auto.
Qed.

Lemma de_morgan2 : forall b1 b2 : bool, negb (b1 && b2) = negb b1 || negb b2.
simple destruct b1; simple destruct b2; simpl in |- *; auto.
Qed.

Lemma de_morgan3 : forall b1 b2 : bool, b1 && b2 = negb (negb b1 || negb b2).
simple destruct b1; simple destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma de_morgan4 : forall b1 b2 : bool, b1 || b2 = negb (negb b1 && negb b2).
simple destruct b1; simple destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma implb_b_true : forall b : bool, implb b true = true.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma implb_b_false : forall b : bool, implb b false = negb b.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma implb_true_b : forall b : bool, implb true b = b.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma implb_false_b : forall b : bool, implb false b = true.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma implb_elim : forall b1 b2 : bool, implb b1 b2 = negb (b1 && negb b2).
simple destruct b1; simple destruct b2; simpl in |- *; auto.
Qed.

Lemma eqb_true_b : forall b : bool, eqb true b = b.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma eqb_b_true : forall b : bool, eqb b true = b.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma eqb_b_false : forall b : bool, eqb b false = negb b.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma eqb_false_b : forall b : bool, eqb false b = negb b.
simple destruct b; simpl in |- *; auto.
Qed.

Lemma eqb_com : forall b1 b2 : bool, eqb b1 b2 = eqb b2 b1.
simple destruct b1; simple destruct b2; simpl in |- *; auto.
Qed.

Lemma orb_false_1 : forall b b' : bool, b || b' = false -> b = false.
intros b b'; case b; case b'; auto; absurd (true = false); auto.
Qed.

Lemma orb_false_2 : forall b b' : bool, b || b' = false -> b' = false.
intros b b'; case b; case b'; auto; absurd (true = false); auto.
Qed.
Hint Resolve de_morgan1 de_morgan2 de_morgan3 de_morgan4.
Hint Resolve implb_b_true implb_b_false implb_true_b implb_false_b implb_elim.
Hint Resolve eqb_true_b eqb_b_true eqb_b_false eqb_false_b eqb_com.