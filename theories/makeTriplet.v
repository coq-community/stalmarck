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
                                                                           
          Stalmarck  :  makeTriplet                                         
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of the transformation from rExpr to list of triplets *)
Require Export equalBefore.
(* Computing triplets return the list of triplets, the top signed variable
    and the next free variable *)

Inductive tripletResult : Set :=
    tRC : list triplet -> rZ -> rNat -> tripletResult.
(* Given an expression e and an indice of free variable, computes the list of triplets *)

Fixpoint makeTripletsFun (l : list triplet) (n : rNat) 
 (e : rExpr) {struct e} : tripletResult :=
  match e with
  | rV i => tRC l (rZPlus i) n
  | rN p =>
      match makeTripletsFun l n p with
      | tRC l' s' n' => tRC l' (rZComp s') n'
      end
  | rNode node p q =>
      match makeTripletsFun l n p with
      | tRC l' s' n' =>
          match makeTripletsFun l' n' q with
          | tRC l2 s2 n2 =>
              tRC (Triplet node (rZPlus n2) s' s2 :: l2) 
                (rZPlus n2) (rnext n2)
          end
      end
  end.

(* To compute the list, we start with an empty list and the indice is maxVar *)

Definition makeTriplets (e : rExpr) : tripletResult :=
  makeTripletsFun nil (rnext (maxVar e)) e.

Ltac DCase _a :=
  generalize (refl_equal _a); pattern _a at -1 in |- *; case _a.

Ltac CaseMake _a _b _c := DCase (makeTripletsFun _a _b _c).

Ltac RecExpr :=
  simple induction e; simpl in |- *;
   [ intros r l l' n n' s' A; inversion A; clear A
   | intros r H' l l' n n' s'; CaseMake l n r; intros l0 r0 r1 A B;
      inversion B; clear B
   | intros r r0 H' r1 A l l' n n' s'; CaseMake l n r0; intros l0 r2 r3 B;
      CaseMake l0 r3 r1; intros l2 r4 r5 C D; inversion D; 
      clear D ]; auto with stalmarck.

Lemma makeTripletsFunMax :
 forall (e : rExpr) (l l' : list triplet) (n n' : rNat) (s' : rZ),
 makeTripletsFun l n e = tRC l' s' n' -> rlt (maxVar e) n -> rVlt s' n'.
RecExpr.
intro H'3. lapply (H' l l0 n n' r0);
  [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ];
  auto with stalmarck.
rewrite <- H2; auto with stalmarck.
red in |- *. auto with stalmarck.
Qed.

Lemma makeTripletsFunIncr :
 forall (e : rExpr) (l l' : list triplet) (n n' : rNat) (s' : rZ),
 makeTripletsFun l n e = tRC l' s' n' -> rlt n (rnext n').
RecExpr.
lapply (H' l l0 n n' r0); auto with stalmarck. rewrite <- H2; auto with stalmarck.
lapply (H' l l0 n r3 r2); [ intros H'9 | auto with stalmarck ].
lapply (A l0 l2 r3 r5 r4); [ intros H'10 | auto with stalmarck ].
apply rltTrans with (y := rnext r3); auto with stalmarck.
Qed.
Global Hint Resolve makeTripletsFunIncr : stalmarck.

Lemma makeTripletsFunIncl :
 forall (e : rExpr) (l l' : list triplet) (n n' : rNat) (s' : rZ),
 makeTripletsFun l n e = tRC l' s' n' -> incl l l'.
RecExpr.
auto with datatypes stalmarck.
lapply (H' l l' n r1 r0); auto with stalmarck. rewrite <- H0; auto with stalmarck.
lapply (H' l l0 n r3 r2); [ intros H'9 | idtac ]; auto with stalmarck.
lapply (A l0 l2 r3 r5 r4); [ intros H'10 | idtac ]; auto with stalmarck.
apply incl_tran with l0; auto with stalmarck.
apply incl_tran with l2; auto with datatypes stalmarck.
Qed.
Global Hint Resolve makeTripletsFunIncr : stalmarck.

Lemma maxVarTripletsRlt :
 forall (e : rExpr) (l l' : list triplet) (n n' : rNat) (s' : rZ),
 makeTripletsFun l n e = tRC l' s' n' ->
 rlt (maxVar e) n -> rlt (maxVarTriplets l) n -> rlt (maxVarTriplets l') n'.
RecExpr; intros H'0 H'1. 
rewrite <- H2; rewrite <- H0.
lapply (H' l l0 n r1 r0);
 [ intros H'9; lapply H'9;
    [ intros H'10; lapply H'10; [ clear H'10 H'9 | clear H'10 H'9 ]
    | clear H'9 ]
 | idtac ]; auto with stalmarck.
simpl in |- *.
apply rmaxRlt; auto with stalmarck.
apply rmaxRlt; auto with stalmarck.
apply rmaxRlt; auto with stalmarck.
apply rltTrans with (y := r3); auto with stalmarck.
change (rVlt r2 r3) in |- *.
eapply makeTripletsFunMax; eauto with stalmarck.
eapply rmaxRltLeft; eauto with stalmarck.
eauto with stalmarck.
apply rltTrans with (y := r5); auto with stalmarck.
change (rVlt r4 r5) in |- *.
eapply makeTripletsFunMax; eauto with stalmarck.
apply rltTransRnext2 with (m := n); eauto with stalmarck.
eapply rmaxRltRight; eauto with stalmarck.
apply rltTrans with (y := r5); auto with stalmarck.
eapply A; eauto with stalmarck.
apply rltTransRnext2 with (m := n); auto with stalmarck.
eapply rmaxRltRight; eauto with stalmarck.
eauto with stalmarck.
eapply H'; eauto with stalmarck.
eapply rmaxRltLeft; eauto with stalmarck.
Qed.

Theorem extendEvalMakeTripletsFun :
 forall (e : rExpr) (l l' : list triplet) (n n' : rNat) (s' : rZ),
 makeTripletsFun l n e = tRC l' s' n' ->
 forall f : rNat -> bool,
 rlt (maxVar e) n ->
 rlt (maxVarTriplets l) n ->
 realizeTriplets f l ->
 exists g : rNat -> bool,
   equalBefore n f g /\ realizeTriplets g l' /\ rEval f e = rZEval g s'.
RecExpr; intros f H'4 H'5 H'6.
exists f; split; [ idtac | split ]; auto with stalmarck; try rewrite <- H0; red in |- *;
 auto with stalmarck.
rewrite H0 in A.
elim (H' l l' n r1 r0 A f); auto with stalmarck.
intros g E; elim E; intros H'15 H'16; elim H'16; intros H'17 H'18;
 clear H'16 E.
rewrite H'18; exists g; split; [ idtac | split ]; simpl in |- *; auto with stalmarck.
case r0; simpl in |- *; auto with stalmarck.
intros r2; case (g r2); auto with stalmarck.
cut (rlt (maxVar r0) n);
 [ intros Rlt1 | apply rmaxRltLeft with (p := maxVar r1); auto with stalmarck ].
cut (rlt (maxVar r1) n);
 [ intros Rlt2 | apply rmaxRltRight with (m := maxVar r0); auto with stalmarck ].
cut (rlt n (rnext r3)); [ intros Rlt3 | eauto with stalmarck ].
cut (rlt (rmax (maxVar r0) (maxVar r1)) r3);
 [ intros Rllt0 | apply rltTransRnext2 with (m := n); auto with stalmarck ].
elim (H' l l0 n r3 r2 B f); auto with stalmarck.
intros g E; elim E; intros H'17 H'18; elim H'18; intros H'19 H'20;
 clear H'18 E.
elim (A l0 l2 r3 r5 r4 C g); auto with stalmarck.
intros g0 E; elim E; intros H'18 H'21; elim H'21; intros H'22 H'23;
 clear H'21 E.
2: apply rltTransRnext2 with (m := n); auto with stalmarck.
2: apply maxVarTripletsRlt with (1 := B); auto with stalmarck.
cut (rlt r3 (rnext r5)); [ intros Rlt4 | eauto with stalmarck ].
exists (extendFun r5 g0 (rBoolOpFun r (rEval f r0) (rEval g r1))); split;
 [ idtac | split ]; auto with stalmarck.
apply (equalBeforeTrans n) with (y := g); auto with stalmarck.
apply equalBeforeLt with (m := r3); auto with stalmarck.
apply (equalBeforeTrans r3) with (y := g0); auto with stalmarck.
red in |- *; simpl in |- *; auto with stalmarck.
intros t H'7; elim H'7;
 [ intros H'8; rewrite <- H'8; clear H'7 | intros H'8; clear H'7 ]; 
 auto with stalmarck.
unfold tEval in |- *.
rewrite (extendFunrZEval g0 r5 r2 (rBoolOpFun r (rEval f r0) (rEval g r1)));
 auto with stalmarck.
rewrite (extendFunrZEval g0 r5 r4 (rBoolOpFun r (rEval f r0) (rEval g r1)));
 auto with stalmarck.
rewrite extendFunrZEvalExact; auto with stalmarck.
rewrite H'20; rewrite H'23; auto with stalmarck; auto with stalmarck.
rewrite <- (equalBeforerZEval g g0 r3 r2); auto with stalmarck.
case (rBoolOpFun r (rZEval g r2) (rZEval g0 r4)); auto with stalmarck.
eapply makeTripletsFunMax; eauto with stalmarck.
eapply makeTripletsFunMax; eauto with stalmarck.
eapply rmaxRltRight; eauto with stalmarck.
red in |- *; apply rltTransRnext2 with (m := r3); auto with stalmarck.
change (rVlt r2 r3) in |- *.
apply makeTripletsFunMax with (e := r0) (l := l) (l' := l0) (n := n); auto with stalmarck.
cut
 (realizeTriplets (extendFun r5 g0 (rBoolOpFun r (rEval f r0) (rEval g r1)))
    l2); auto with stalmarck.
apply supportTriplets with (f := g0); auto with stalmarck.
apply equalBeforeExtend; auto with stalmarck.
apply rnextMono; auto with stalmarck.
eapply maxVarTripletsRlt; eauto with stalmarck.
eapply rmaxRltRight; eauto with stalmarck.
eapply maxVarTripletsRlt; eauto with stalmarck.
rewrite extendFunrZEvalExact; auto with stalmarck.
rewrite (equalBeforeREval f g r1); auto with stalmarck.
apply equalBeforeLt with (m := n); auto with stalmarck.
Qed.

Theorem extendEvalMakeTriplets :
 forall (f : rNat -> bool) (e : rExpr) (l : list triplet) (n : rNat) (s : rZ),
 makeTriplets e = tRC l s n ->
 exists g : rNat -> bool,
   equalBefore (rnext (maxVar e)) f g /\
   realizeTriplets g l /\ rEval f e = rZEval g s.
intros f e l n s H'.
apply extendEvalMakeTripletsFun with (l := nil (A:=triplet)) (n' := n);
 simpl in |- *; auto with stalmarck.
Qed.

Theorem equalBeforeMakeTripletsFun :
 forall (e : rExpr) (l l' : list triplet) (n n' : rNat) (s' : rZ),
 makeTripletsFun l n e = tRC l' s' n' ->
 forall f g : rNat -> bool,
 rlt (maxVar e) n ->
 rlt (maxVarTriplets l) n ->
 equalBefore n f g ->
 realizeTriplets f l' -> realizeTriplets g l' -> equalBefore n' f g.
RecExpr; intros f g H'4 H'5 H'6 H'7 H'8.
apply H' with (l := l) (l' := l') (n := n) (s' := r0); auto with stalmarck.
rewrite <- H0; rewrite <- H2; auto with stalmarck.
cut (rlt n (rnext r3)); [ intros Rle0 | eapply makeTripletsFunIncr; eauto with stalmarck ].
cut (equalBefore r5 f g); [ intros eB0 | idtac ].
apply equalBeforeNext; auto with stalmarck.
cut (tEval f (Triplet r (rZPlus r5) r2 r4) = true); [ simpl in |- * | idtac ].
cut (tEval g (Triplet r (rZPlus r5) r2 r4) = true); [ simpl in |- * | idtac ].
rewrite (equalBeforerZEval f g r5 r4); auto with stalmarck.
rewrite (equalBeforerZEval f g r5 r2); auto with stalmarck.
case (f r5); auto with stalmarck; case (g r5); auto with stalmarck;
 case (rBoolOpFun r (rZEval g r2) (rZEval g r4)); auto with stalmarck.
red in |- *; apply rltTransRnext2 with (m := r3); auto with stalmarck.
change (rVlt r2 r3) in |- *.
eapply makeTripletsFunMax; eauto with stalmarck.
apply rmaxRltLeft with (p := maxVar r1); auto with stalmarck.
eapply makeTripletsFunIncr; eauto with stalmarck.
eapply makeTripletsFunMax; eauto with stalmarck.
apply rmaxRltRight with (m := maxVar r0); auto with stalmarck.
apply rltTransRnext2 with (m := n); auto with stalmarck.
apply H'8; auto with datatypes stalmarck.
apply H'7; auto with datatypes stalmarck.
rewrite H0 in H'7.
rewrite H0 in H'8.
apply A with (1 := C); auto with stalmarck.
apply rmaxRltRight with (m := maxVar r0); auto with stalmarck.
apply rltTransRnext2 with (m := n); auto with stalmarck.
eapply maxVarTripletsRlt; eauto with stalmarck.
apply rmaxRltLeft with (p := maxVar r1); auto with stalmarck.
apply H' with (1 := B); auto with stalmarck.
apply rmaxRltLeft with (p := maxVar r1); auto with stalmarck.
apply realizeTripletIncl with (L1 := l'); auto with stalmarck.
rewrite <- H0; auto with stalmarck.
apply incl_tran with (m := l2); auto with datatypes stalmarck.
eapply makeTripletsFunIncl; eauto with stalmarck.
apply realizeTripletIncl with (L1 := l'); auto with stalmarck.
rewrite <- H0; auto with stalmarck.
apply incl_tran with (m := l2); auto with datatypes stalmarck.
eapply makeTripletsFunIncl; eauto with stalmarck.
apply realizeTripletIncl with (L1 := l'); auto with stalmarck.
rewrite <- H0; auto with datatypes stalmarck.
apply realizeTripletIncl with (L1 := l'); auto with stalmarck.
rewrite <- H0; auto with datatypes stalmarck.
Qed.

Theorem equalBeforeMakeTriplets :
 forall (f g : rNat -> bool) (e : rExpr) (l : list triplet) 
   (n : rNat) (s : rZ),
 equalBefore (rnext (maxVar e)) f g ->
 realizeTriplets f l ->
 realizeTriplets g l -> makeTriplets e = tRC l s n -> rZEval f s = rZEval g s.
intros f g e l n s H' H'0 H'1 H'2.
apply equalBeforerZEval with (n := n); auto with stalmarck.
apply
 makeTripletsFunMax
  with (e := e) (l := nil (A:=triplet)) (l' := l) (n := rnext (maxVar e));
 auto with stalmarck.
apply
 equalBeforeMakeTripletsFun
  with
    (e := e)
    (l := nil (A:=triplet))
    (l' := l)
    (n := rnext (maxVar e))
    (s' := s); auto with stalmarck.
Qed.

Theorem rZEvalREvalMakeTriplets :
 forall (f g : rNat -> bool) (e : rExpr) (l : list triplet) 
   (n : rNat) (s : rZ),
 equalBefore (rnext (maxVar e)) f g ->
 realizeTriplets g l -> makeTriplets e = tRC l s n -> rZEval g s = rEval f e.
intros f g e l n s H' H'0 H'1.
elim (extendEvalMakeTriplets f e l n s);
 [ intros g0 E; elim E; intros H'8 H'9; elim H'9; intros H'10 H'11;
    rewrite H'11; clear H'9 E
 | idtac ]; auto with stalmarck.
apply equalBeforeMakeTriplets with (e := e) (l := l) (n := n); auto with stalmarck.
apply (equalBeforeTrans (rnext (maxVar e))) with (y := f); auto with stalmarck.
apply (equalBeforeSym (rnext (maxVar e))); auto with stalmarck.
Qed.

Theorem rZEvalEvalRZMakeTriplets :
 forall (f : rNat -> bool) (e : rExpr) (l : list triplet) (n : rNat) (s : rZ),
 realizeTriplets f l -> makeTriplets e = tRC l s n -> rEval f e = rZEval f s.
intros f e l n s H' H'0.
apply sym_equal; auto with stalmarck.
apply rZEvalREvalMakeTriplets with (l := l) (n := n); auto with stalmarck.
red in |- *; auto with stalmarck.
Qed.

(* A tautology for triplets is simply that top_variable := true is a valid equation *)

Definition tTautology (e : rExpr) :=
  match makeTriplets e with
  | tRC l s n => validEquation l s (rZPlus zero)
  end.
(* This definition is equivalent to the one of rTautology *)

Theorem rTautotTauto : forall e : rExpr, rTautology e <-> tTautology e.
intros e; unfold tTautology in |- *; unfold rTautology in |- *.
DCase (makeTriplets e).
intros l r r0 H'; split; intros H'1.
red in |- *; simpl in |- *; auto with stalmarck.
intros f H'0 fZ0; simpl in |- *.
rewrite fZ0; auto with stalmarck.
rewrite <- (H'1 f); auto with stalmarck.
apply rZEvalREvalMakeTriplets with (l := l) (n := r0); auto with stalmarck.
red in |- *; auto with stalmarck.
intros f fZ0.
red in H'1.
elim (extendEvalMakeTriplets f e l r0 r);
 [ intros g E; elim E; intros H'7 H'8; elim H'8; intros H'9 H'10; clear H'8 E
 | idtac ]; auto with stalmarck.
rewrite H'10.
rewrite (H'1 g); simpl in |- *; auto with stalmarck.
rewrite <- equalBeforeElim with (1 := H'7); auto with stalmarck.
rewrite <- equalBeforeElim with (1 := H'7); auto with stalmarck.
Qed.
(* The top variable occurs in the list of triplets *)

Theorem makeTripletsIn :
 forall e : rExpr,
 match makeTriplets e with
 | tRC l s n => l <> nil -> inTriplets s l
 end.
unfold makeTriplets in |- *; intros e; elim e; simpl in |- *; auto with stalmarck.
intros r H'; case H'; auto with stalmarck.
intros r; case (makeTripletsFun nil (rnext (maxVar r)) r); auto with stalmarck.
intros l r0 H' H'0 H'1.
apply inTripletsComp; auto with stalmarck.
intros r r0 H' r1 H'0.
case (makeTripletsFun nil (rnext (rmax (maxVar r0) (maxVar r1))) r0).
intros l r2 r3.
case (makeTripletsFun l r3 r1); simpl in |- *; auto with stalmarck.
Qed.
