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

(** * algoRun

Pierre Letouzey & Laurent Thery

Some examples of computing with stalmarck inside Coq
*)

From Coq Require Import ZArith.
From Stalmarck Require Export algoStalmarck.
From Stalmarck Require Export algoTrace.
From Stalmarck Require Export makeTriplet.

Section orun.
Eval compute in
  (makeTriplets
     (norm (Node Or (V (rnext zero)) (normalize.N (V (rnext zero)))))).

Definition run (m : nat) (e : Expr) :=
  match makeTriplets (norm e) with
  | tRC L r n =>
      letP _ _ (buildL L)
        (fun Ar =>
         letP _ _ (nat_of_P (valRz r))
           (fun n =>
            stal (getT Ar) n m (rArrayInit _ (fun r => class nil)) r rZFalse))
  end.
Eval compute in
  (run 0 (Node Or (V (rnext zero)) (normalize.N (V (rnext zero))))).
Opaque addEqMem.
Opaque stal.

Theorem runCorrect :
 forall (m : nat) (e : Expr),
 match run m e with
 | quatuor Ar' false L T => True
 | quatuor Ar' true L T => Tautology e
 end.
intros m e; unfold run in |- *.
CaseEq (makeTriplets (norm e)).
intros l r r0 H'; unfold letP in |- *.
generalize
 (stalCorrect (getT (buildL l)) l (getTCorrect l) (nat_of_P (valRz r)) m
    (rArrayInit vM (fun _ : rNat => class nil)) r rZFalse nil rIwF
    initCorrect).
case
 (stal (getT (buildL l)) (nat_of_P (valRz r)) m
    (rArrayInit vM (fun _ : rNat => class nil)) r rZFalse); 
 auto with stalmarck.
intros Ar1 b1 L1 T1; case b1; auto with stalmarck.
intros H'0; Elimc H'0; intros S' E; Elimc E; intros H'0 H'1; Elimc H'1;
 intros H'1 H'2.
case (TautoRTauto e).
intros H'3 H'4; apply H'4.
case (rTautotTauto (norm e)).
intros H'5 H'6; apply H'6; auto with stalmarck.
red in |- *; rewrite H'.
apply stalmarckGivesValidEquation with (S := S'); auto with stalmarck.
Qed.
Transparent addEqMem.
Transparent stal.

Let t1 :
  Tautology (Node Or (V (rnext zero)) (normalize.N (V (rnext zero)))) :=
  runCorrect 0 (Node Or (V (rnext zero)) (normalize.N (V (rnext zero)))).

Let t2 :
  Tautology
    (Node Impl
       (Node ANd (Node Impl (V (rnext zero)) (V (rnext (rnext zero))))
          (Node Impl (V (rnext (rnext (rnext zero))))
             (V (rnext (rnext (rnext (rnext zero)))))))
       (Node Impl
          (Node ANd (V (rnext zero)) (V (rnext (rnext (rnext zero)))))
          (Node ANd (V (rnext (rnext zero)))
             (V (rnext (rnext (rnext (rnext zero)))))))) :=
  runCorrect 0
    (Node Impl
       (Node ANd (Node Impl (V (rnext zero)) (V (rnext (rnext zero))))
          (Node Impl (V (rnext (rnext (rnext zero))))
             (V (rnext (rnext (rnext (rnext zero)))))))
       (Node Impl
          (Node ANd (V (rnext zero)) (V (rnext (rnext (rnext zero)))))
          (Node ANd (V (rnext (rnext zero)))
             (V (rnext (rnext (rnext (rnext zero)))))))).

Definition getB (a : mbDT) : bool := match a with
                                     | quatuor _ b _ _ => b
                                     end.

Theorem runC :
 forall (m : nat) (e : Expr), getB (run m e) = true -> Tautology e.
intros m e; generalize (runCorrect m e).
case (run m e); auto with stalmarck.
intros r b l t; case b; simpl in |- *; auto with stalmarck.
intros H' H'0; discriminate.
Qed.

Theorem F1 :
 Tautology (Node Or (V (rnext zero)) (normalize.N (V (rnext zero)))).
apply (runC 0); exact (refl_equal true).
Qed.

Theorem F2 :
 Tautology
   (Node Impl
      (Node ANd (Node Impl (V (rnext zero)) (V (rnext (rnext zero))))
         (Node Impl (V (rnext (rnext (rnext zero))))
            (V (rnext (rnext (rnext (rnext zero)))))))
      (Node Impl (Node ANd (V (rnext zero)) (V (rnext (rnext (rnext zero)))))
         (Node ANd (V (rnext (rnext zero)))
            (V (rnext (rnext (rnext (rnext zero)))))))).
apply (runC 0); exact (refl_equal true).
Qed.

Theorem F3 :
 Tautology
   (normalize.N
      (Node ANd
         (Node Or (normalize.N (V (P_of_succ_nat 2))) (V (P_of_succ_nat 1)))
         (Node ANd
            (Node Or (normalize.N (V (P_of_succ_nat 9)))
               (V (P_of_succ_nat 3)))
            (Node ANd
               (Node Or (normalize.N (V (P_of_succ_nat 7)))
                  (V (P_of_succ_nat 10)))
               (Node ANd
                  (Node Or (normalize.N (V (P_of_succ_nat 5)))
                     (V (P_of_succ_nat 8)))
                  (Node ANd
                     (Node Or (normalize.N (V (P_of_succ_nat 1)))
                        (V (P_of_succ_nat 4)))
                     (Node ANd
                        (Node Or (normalize.N (V (P_of_succ_nat 6)))
                           (V (P_of_succ_nat 2)))
                        (Node ANd
                           (Node Or (normalize.N (V (P_of_succ_nat 11)))
                              (normalize.N (V (P_of_succ_nat 3))))
                           (Node ANd
                              (Node Or (normalize.N (V (P_of_succ_nat 4)))
                                 (V (P_of_succ_nat 5)))
                              (Node ANd
                                 (Node Or (V (P_of_succ_nat 6))
                                    (V (P_of_succ_nat 7)))
                                 (Node ANd
                                    (Node Or
                                       (normalize.N (V (P_of_succ_nat 8)))
                                       (V (P_of_succ_nat 9)))
                                    (Node ANd
                                       (normalize.N (V (P_of_succ_nat 10)))
                                       (V (P_of_succ_nat 11)))))))))))))).
apply (runC 0); exact (refl_equal true).
Qed.
Check 0.
(*
Theorem F4:
  (Tautology
     (Node
        Impl
        (Node
           ANd
           (Node
              ANd
              (Node
                 ANd
                 (Node
                    ANd
                    (Node
                       ANd
                       (Node
                          ANd
                          (Node
                             ANd
                             (Node
                                ANd
                                (Node
                                   ANd
                                   (Node
                                      ANd
                                      (Node
                                         ANd
                                         (Node
                                            ANd
                                            (Node
                                               ANd
                                               (Node
                                                  ANd
                                                  (Node
                                                     ANd
                                                     (Node
                                                        ANd
                                                        (Node
                                                           Eq
                                                           (V
                                                              (anti_convert
                                                                 (23)))
                                                           (Node
                                                              ANd
                                                              (V
                                                                 (anti_convert
                                                                    (18)))
                                                              (V
                                                                 (anti_convert
                                                                    (17)))))
                                                        (Node
                                                           Eq
                                                           (V
                                                              (anti_convert
                                                                 (22)))
                                                           (Node
                                                              Or
                                                              (Node
                                                                 ANd
                                                                 (Node
                                                                    Or
                                                                    (V
                                                                       (anti_convert
                                                                          (11)))
                                                                    (V
                                                                       (anti_convert
                                                                          (10))))
                                                                 (V
                                                                    (anti_convert
                                                                       (23))))
                                                              (Node
                                                                 ANd
                                                                 (V
                                                                    (anti_convert
                                                                       (11)))
                                                                 (V
                                                                    (anti_convert
                                                                       (10)))))))
                                                     (Node
                                                        Eq
                                                        (V (anti_convert (21)))
                                                        (Node
                                                           Or
                                                           (Node
                                                              ANd
                                                              (Node
                                                                 Or
                                                                 (V
                                                                    (anti_convert
                                                                       (9)))
                                                                 (V
                                                                    (anti_convert
                                                                       (8))))
                                                              (V
                                                                 (anti_convert
                                                                    (22))))
                                                           (Node
                                                              ANd
                                                              (V
                                                                 (anti_convert
                                                                    (9)))
                                                              (V
                                                                 (anti_convert
                                                                    (8)))))))
                                                  (Node
                                                     Eq (V (anti_convert (20)))
                                                     (Node
                                                        Or
                                                        (Node
                                                           ANd
                                                           (Node
                                                              Or
                                                              (V
                                                                 (anti_convert
                                                                    (7)))
                                                              (V
                                                                 (anti_convert
                                                                    (6))))
                                                           (V
                                                              (anti_convert
                                                                 (21))))
                                                        (Node
                                                           ANd
                                                           (V
                                                              (anti_convert (7)))
                                                           (V
                                                              (anti_convert (6)))))))
                                               (Node
                                                  Eq (V (anti_convert (19)))
                                                  (Node
                                                     Or
                                                     (Node
                                                        ANd
                                                        (Node
                                                           Or
                                                           (V
                                                              (anti_convert (5)))
                                                           (V
                                                              (anti_convert (4))))
                                                        (V (anti_convert (20))))
                                                     (Node
                                                        ANd
                                                        (V (anti_convert (5)))
                                                        (V (anti_convert (4)))))))
                                            (Node
                                               Eq (V (anti_convert (30)))
                                               (Node
                                                  Or
                                                  (Node
                                                     ANd
                                                     (Node
                                                        Or
                                                        (V (anti_convert (3)))
                                                        (V (anti_convert (2))))
                                                     (V (anti_convert (19))))
                                                  (Node
                                                     ANd (V (anti_convert (3)))
                                                     (V (anti_convert (2)))))))
                                         (Node
                                            Eq (V (anti_convert (29)))
                                            (N
                                               (Node
                                                  Eq (V (anti_convert (3)))
                                                  (N
                                                     (Node
                                                        Eq
                                                        (V (anti_convert (2)))
                                                        (V (anti_convert (19)))))))))
                                      (Node
                                         Eq (V (anti_convert (28)))
                                         (N
                                            (Node
                                               Eq (V (anti_convert (5)))
                                               (N
                                                  (Node
                                                     Eq (V (anti_convert (4)))
                                                     (V (anti_convert (20)))))))))
                                   (Node
                                      Eq (V (anti_convert (27)))
                                      (N
                                         (Node
                                            Eq (V (anti_convert (7)))
                                            (N
                                               (Node
                                                  Eq (V (anti_convert (6)))
                                                  (V (anti_convert (21)))))))))
                                (Node
                                   Eq (V (anti_convert (26)))
                                   (N
                                      (Node
                                         Eq (V (anti_convert (9)))
                                         (N
                                            (Node
                                               Eq (V (anti_convert (8)))
                                               (V (anti_convert (22)))))))))
                             (Node
                                Eq (V (anti_convert (25)))
                                (N
                                   (Node
                                      Eq (V (anti_convert (11)))
                                      (N
                                         (Node
                                            Eq (V (anti_convert (10)))
                                            (V (anti_convert (23)))))))))
                          (Node
                             Eq (V (anti_convert (24)))
                             (N
                                (Node
                                   Eq (V (anti_convert (18)))
                                   (V (anti_convert (17)))))))
                       (Node
                          Eq (V (anti_convert (16)))
                          (Node
                             ANd (V (anti_convert (17))) (V (anti_convert (18))))))
                    (Node
                       Eq (V (anti_convert (15)))
                       (Node
                          Or
                          (Node
                             Or
                             (Node
                                ANd (V (anti_convert (16)))
                                (V (anti_convert (10))))
                             (Node
                                ANd (V (anti_convert (16)))
                                (V (anti_convert (11)))))
                          (Node
                             ANd (V (anti_convert (10))) (V (anti_convert (11)))))))
                 (Node
                    Eq (V (anti_convert (14)))
                    (Node
                       Or
                       (Node
                          Or
                          (Node
                             ANd (V (anti_convert (15))) (V (anti_convert (8))))
                          (Node
                             ANd (V (anti_convert (15))) (V (anti_convert (9)))))
                       (Node ANd (V (anti_convert (8))) (V (anti_convert (9)))))))
              (Node
                 Eq (V (anti_convert (13)))
                 (Node
                    Or
                    (Node
                       Or
                       (Node ANd (V (anti_convert (14))) (V (anti_convert (6))))
                       (Node ANd (V (anti_convert (14))) (V (anti_convert (7)))))
                    (Node ANd (V (anti_convert (6))) (V (anti_convert (7)))))))
           (Node
              Eq (V (anti_convert (12)))
              (Node
                 Or
                 (Node
                    Or (Node ANd (V (anti_convert (13))) (V (anti_convert (4))))
                    (Node ANd (V (anti_convert (13))) (V (anti_convert (5)))))
                 (Node ANd (V (anti_convert (4))) (V (anti_convert (5)))))))
        (Node
           ANd
           (Node
              ANd
              (Node
                 ANd
                 (Node
                    ANd
                    (Node
                       ANd
                       (Node
                          ANd
                          (Node
                             Eq (V (anti_convert (24)))
                             (N
                                (Node
                                   Or
                                   (Node
                                      ANd (N (V (anti_convert (18))))
                                      (N (V (anti_convert (17)))))
                                   (Node
                                      ANd (V (anti_convert (18)))
                                      (V (anti_convert (17)))))))
                          (Node
                             Eq (V (anti_convert (25)))
                             (N
                                (Node
                                   Or
                                   (Node
                                      ANd
                                      (Node
                                         Or
                                         (Node
                                            ANd (N (V (anti_convert (11))))
                                            (N (V (anti_convert (10)))))
                                         (Node
                                            ANd (V (anti_convert (11)))
                                            (V (anti_convert (10)))))
                                      (N (V (anti_convert (16)))))
                                   (Node
                                      ANd (V (anti_convert (16)))
                                      (N
                                         (Node
                                            Or
                                            (Node
                                               ANd (N (V (anti_convert (11))))
                                               (N (V (anti_convert (10)))))
                                            (Node
                                               ANd (V (anti_convert (11)))
                                               (V (anti_convert (10)))))))))))
                       (Node
                          Eq (V (anti_convert (26)))
                          (N
                             (Node
                                Or
                                (Node
                                   ANd
                                   (Node
                                      Or
                                      (Node
                                         ANd (N (V (anti_convert (9))))
                                         (N (V (anti_convert (8)))))
                                      (Node
                                         ANd (V (anti_convert (9)))
                                         (V (anti_convert (8)))))
                                   (N (V (anti_convert (15)))))
                                (Node
                                   ANd (V (anti_convert (15)))
                                   (N
                                      (Node
                                         Or
                                         (Node
                                            ANd (N (V (anti_convert (9))))
                                            (N (V (anti_convert (8)))))
                                         (Node
                                            ANd (V (anti_convert (9)))
                                            (V (anti_convert (8)))))))))))
                    (Node
                       Eq (V (anti_convert (27)))
                       (N
                          (Node
                             Or
                             (Node
                                ANd
                                (Node
                                   Or
                                   (Node
                                      ANd (N (V (anti_convert (7))))
                                      (N (V (anti_convert (6)))))
                                   (Node
                                      ANd (V (anti_convert (7)))
                                      (V (anti_convert (6)))))
                                (N (V (anti_convert (14)))))
                             (Node
                                ANd (V (anti_convert (14)))
                                (N
                                   (Node
                                      Or
                                      (Node
                                         ANd (N (V (anti_convert (7))))
                                         (N (V (anti_convert (6)))))
                                      (Node
                                         ANd (V (anti_convert (7)))
                                         (V (anti_convert (6)))))))))))
                 (Node
                    Eq (V (anti_convert (28)))
                    (N
                       (Node
                          Or
                          (Node
                             ANd
                             (Node
                                Or
                                (Node
                                   ANd (N (V (anti_convert (5))))
                                   (N (V (anti_convert (4)))))
                                (Node
                                   ANd (V (anti_convert (5)))
                                   (V (anti_convert (4)))))
                             (N (V (anti_convert (13)))))
                          (Node
                             ANd (V (anti_convert (13)))
                             (N
                                (Node
                                   Or
                                   (Node
                                      ANd (N (V (anti_convert (5))))
                                      (N (V (anti_convert (4)))))
                                   (Node
                                      ANd (V (anti_convert (5)))
                                      (V (anti_convert (4)))))))))))
              (Node
                 Eq (V (anti_convert (29)))
                 (N
                    (Node
                       Or
                       (Node
                          ANd
                          (Node
                             Or
                             (Node
                                ANd (N (V (anti_convert (3))))
                                (N (V (anti_convert (2)))))
                             (Node
                                ANd (V (anti_convert (3)))
                                (V (anti_convert (2)))))
                          (N (V (anti_convert (12)))))
                       (Node
                          ANd (V (anti_convert (12)))
                          (N
                             (Node
                                Or
                                (Node
                                   ANd (N (V (anti_convert (3))))
                                   (N (V (anti_convert (2)))))
                                (Node
                                   ANd (V (anti_convert (3)))
                                   (V (anti_convert (2)))))))))))
           (Node
              Eq (V (anti_convert (30)))
              (Node
                 Or
                 (Node
                    Or (Node ANd (V (anti_convert (3))) (V (anti_convert (12))))
                    (Node ANd (V (anti_convert (2))) (V (anti_convert (12)))))
                 (Node ANd (V (anti_convert (3))) (V (anti_convert (2))))))))).
Check (S O).
apply (runC 0); exact (refl_equal bool true).
Check nat.
Qed.
*)
End orun.
