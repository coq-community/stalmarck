
(****************************************************************************
                                                                           
          Stalmarck  : algoStalmarck                                         
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
****************************************************************************)
Require Export algoDilemma1.
Section ostal.
Variable getT : rZ -> list triplet.
Variable LL : list triplet.
Hypothesis getTCorrect : forall a : rZ, incl (getT a) LL.
Variable n : nat.
(*We iterate saturaturing from level n1 to n1+m*)

Fixpoint stalN (L : list rZ) (n1 m : nat) {struct m} : 
 rArray vM -> mbDT :=
  fun Ar =>
  match dilemmaN getT n L n n1 Ar with
  | quatuor Ar2 true L2 T2 => quatuor _ _ _ _ Ar2 true L2 T2
  | quatuor Ar2 false L2 T2 =>
      match m with
      | O => quatuor _ _ _ _ Ar2 false L2 T2
      | S m1 =>
          match stalN nil (S n1) m1 Ar2 with
          | quatuor Ar4 b4 L4 T4 =>
              quatuor _ _ _ _ Ar4 b4 (appendRz L2 L4) (appTrace T2 T4)
          end
      end
  end.

Theorem stalNCorrect :
 forall (L : list rZ) (n1 m : nat) (Ar : rArray vM) (S : State),
 FStalCorrect Ar LL S (stalN L n1 m Ar).
intros L n1 m; generalize n1 L; elim m; simpl in |- *; auto; clear n1 L.
intros n1 L Ar S;
 generalize (dilemmaNCorrect getT LL getTCorrect n L n n1 Ar).
case (dilemmaN getT n L n n1 Ar); auto.
intros Ar1 b1 L1 T1; case b1; auto.
intros n0 H' n1 L Ar S0.
generalize (dilemmaNCorrect getT LL getTCorrect n L n n1 Ar).
case (dilemmaN getT n L n n1 Ar); auto.
intros Ar1 b1 L1 T1; case b1; auto.
intros H'0.
generalize (H' (S n1) nil Ar1).
case (stalN nil (S n1) n0 Ar1).
intros r b l t H'1.
apply FStalCorrectComp with (Ar' := Ar1); auto.
Qed.

(* We first do a propagation then a dilemma1 .. then dilemma m*)

Definition stal (m : nat) (Ar : rArray vM) (a b : rZ) : mbDT :=
  match addEqMem Ar a b with
  | triple Ar1 true L1 => quatuor _ _ _ _ Ar true nil emptyTrace
  | triple Ar1 false L1 =>
      match stalN L1 0 m Ar1 with
      | quatuor Ar2 b2 L2 T2 => quatuor _ _ _ _ Ar2 b2 (appendRz L1 L2) T2
      end
  end.
Opaque addEqMem.

Theorem stalCorrect :
 forall (m : nat) (Ar : rArray vM) (a b : rZ) (S : State),
 wellFormedArray Ar ->
 rArrayState Ar S ->
 match stal m Ar a b with
 | quatuor Ar' false L T => True
 | quatuor Ar' true L T =>
     exists S' : State,
       stalmarckP (addEq (a, b) S) LL S' /\
       contradictory S' /\ evalTrace (addEq (a, b) S) T S'
 end.
intros m Ar a b S H' H'0; unfold stal in |- *.
generalize (addEqMemCorrect Ar a b S).
case (addEqMem Ar a b).
intros Ar1 b1 L1; case b1.
intros H'1; exists (addEq (pair a b) S); repeat (split; auto).
intros H'1; elim H'1;
 [ intros H'4 H'5; elim H'5; intros H'6 H'7; elim H'7; intros H'8 H'9;
    clear H'7 H'5 H'1
 | clear H'1
 | clear H'1 ]; auto.
generalize (stalNCorrect L1 0 m Ar1).
case (stalN L1 0 m Ar1).
intros Ar2 b2 L2 T2; case b2; auto.
unfold FStalCorrect in |- *; simpl in |- *; auto.
Qed.
Transparent addEqMem.
End ostal.
