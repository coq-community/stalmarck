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

(** * equalBefore

Pierre Letouzey & Laurent Thery

Definition of equality on booleans up to a certain number
*)

From Coq Require Import Relation_Definitions.
From Stalmarck Require Export triplet.

(** f and g gives same value for rNat less than m *)
Definition equalBefore (n : rNat) (f g : rNat -> bool) :=
  forall m : rNat, rlt m n -> f m = g m.

Lemma equalBeforeElim :
 forall (n m : rNat) (f g : rNat -> bool),
 equalBefore n f g -> rlt m n -> f m = g m.
Proof.
intros n m f g H' H'1; red in H'; auto with stalmarck.
Qed.

Lemma equalBeforeTrans :
 forall n : rNat, transitive (rNat -> bool) (equalBefore n).
Proof.
intros n; red in |- *; auto with stalmarck.
intros x y z H' H'0; red in |- *; auto with stalmarck.
intros m H'1; apply trans_eq with (y := y m); auto with stalmarck.
Qed.

Lemma equalBeforeLt :
 forall (n m : rNat) (f g : rNat -> bool),
 rlt n (rnext m) -> equalBefore m f g -> equalBefore n f g.
Proof.
intros n m f g H' H'0; red in |- *; red in H'0; auto with stalmarck.
intros m0 H'1; apply H'0; auto with stalmarck.
apply rltTransRnext2 with (m := n); auto with stalmarck.
Qed.

Lemma equalBeforeSym :
 forall n : rNat, symmetric (rNat -> bool) (equalBefore n).
Proof.
intros n; red in |- *.
intros x y H'; red in H'; red in |- *; auto with stalmarck.
intros m H'0; apply sym_eq; auto with stalmarck.
Qed.

#[export] Hint Resolve equalBeforeSym : stalmarck.

(** same value as f for element smaller than m, s otherwise *)
Definition extendFun (n : rNat) (g : rNat -> bool) 
  (s : bool) (m : rNat) := match rltDec m n with
                           | left _ => g m
                           | _ => s
                           end.

Lemma equalBeforeExtend :
 forall (g : rNat -> bool) (n m : rNat) (s : bool),
 rlt n (rnext m) -> equalBefore n g (extendFun m g s).
Proof.
intros g n m s H; simpl in |- *; auto with stalmarck.
red in |- *; auto with stalmarck.
intros p H'; unfold extendFun in |- *; case (rltDec p m); auto with stalmarck.
intros s0; case s0; auto with stalmarck.
intros H'0; absurd (rlt (rnext m) n); auto with stalmarck.
apply rltAntiSym; auto with stalmarck.
apply rltTransRnext1 with (m := p); auto with stalmarck.
intros H'0; rewrite <- H'0 in H.
case (rNextInv n p); auto with stalmarck.
intros H'1; absurd (p = n); auto with stalmarck.
apply rltDef2; auto with stalmarck.
intros H'1; absurd (rlt n p); auto with stalmarck.
apply rltAntiSym; auto with stalmarck.
Qed.

#[export] Hint Resolve equalBeforeExtend : stalmarck.

Lemma extendFunrZEvalExact :
 forall (g : rNat -> bool) (n : rNat) (p : rZ) (s : bool),
 valRz p = n ->
 rZEval (extendFun n g s) p =
 match p with
 | rZPlus p => s
 | rZMinus _ => negb s
 end.
Proof.
intros g n p; case p; unfold extendFun in |- *; simpl in |- *; auto with stalmarck;
 intros r s H; case (rltDec r n); auto with stalmarck; rewrite H; 
 intros; absurd (rlt n n); auto with stalmarck.
Qed.

Lemma extendFunrZEval :
 forall (g : rNat -> bool) (n : rNat) (p : rZ) (s : bool),
 rVlt p n -> rZEval (extendFun n g s) p = rZEval g p.
Proof.
intros g n p; case p; unfold rVlt in |- *; simpl in |- *; auto with stalmarck.
intros r s H'.
unfold extendFun in |- *.
case (rltDec r n); auto with stalmarck.
intros s0; case s0; auto with stalmarck.
intros H'0; absurd (rlt n r); auto with stalmarck.
apply rltAntiSym; auto with stalmarck.
intros H'0; absurd (r = n); auto with stalmarck.
apply rltDef2; auto with stalmarck.
intros r s H'.
unfold extendFun in |- *.
case (rltDec r n); auto with stalmarck.
intros s0; case s0; auto with stalmarck.
intros H'0; absurd (rlt n r); auto with stalmarck.
apply rltAntiSym; auto with stalmarck.
intros H'0; absurd (r = n); auto with stalmarck.
apply rltDef2; auto with stalmarck.
Qed.

Lemma equalBeforerZEval :
 forall (f g : rNat -> bool) (n : rNat) (p : rZ),
 rVlt p n -> equalBefore n f g -> rZEval f p = rZEval g p.
Proof.
intros f g n p; case p; unfold rVlt in |- *; simpl in |- *; auto with stalmarck.
intros r H' H'0; red in H'0; auto with stalmarck.
rewrite (H'0 r); auto with stalmarck.
Qed.

Theorem equalBeforeNext :
 forall (f g : rNat -> bool) (n : rNat),
 equalBefore n f g -> f n = g n -> equalBefore (rnext n) f g.
Proof.
intros f g n H' H'0; red in H'; red in |- *; auto with stalmarck.
intros m H'1; case (rNextInv m n); auto with stalmarck.
intros H'2; rewrite H'2; auto with stalmarck.
Qed.

Lemma equalBeforeTEval :
 forall (f g : rNat -> bool) (t : triplet),
 equalBefore (rnext (maxVarTriplet t)) f g -> tEval f t = tEval g t.
Proof.
intros f g t; case t; simpl in |- *; auto with stalmarck.
intros r r0 r1 r2 H'; red in H'.
cut (rZEval f r0 = rZEval g r0); [ intros Eq1; rewrite Eq1 | idtac ]; auto with stalmarck.
cut (rZEval f r1 = rZEval g r1); [ intros Eq2; rewrite Eq2 | idtac ]; auto with stalmarck.
cut (rZEval f r2 = rZEval g r2); [ intros Eq3; rewrite Eq3 | idtac ]; auto with stalmarck.
generalize H'; case r2; simpl in |- *; auto with stalmarck; intros r3 H'0; rewrite H'0;
 simpl in |- *; auto with stalmarck.
generalize H'; case r1; simpl in |- *; auto with stalmarck; intros r3 H'0; rewrite H'0;
 simpl in |- *; auto with stalmarck.
apply rltTransRnext1 with (m := rmax (valRz r0) r3); auto with stalmarck.
apply rltTransRnext1 with (m := rmax (valRz r0) r3); auto with stalmarck.
generalize H'; case r0; simpl in |- *; auto with stalmarck; intros r3 H'0; rewrite H'0;
 simpl in |- *; auto with stalmarck.
apply rltTransRnext1 with (m := rmax r3 (valRz r1)); auto with stalmarck.
apply rltTransRnext1 with (m := rmax r3 (valRz r1)); auto with stalmarck.
Qed.

#[export] Hint Resolve equalBeforeTEval : stalmarck.

(** Only values under maxVarTriplets are important for realizability *)
Lemma supportTriplets :
 forall (f g : rNat -> bool) (l : list triplet),
 realizeTriplets f l ->
 equalBefore (rnext (maxVarTriplets l)) f g -> realizeTriplets g l.
Proof.
intros f g l; elim l; simpl in |- *; auto with stalmarck.
intros a l0 H' H'0 H'1.
red in |- *; simpl in |- *; auto with stalmarck.
intros t H'2; Elimc H'2; intros H'2; [ rewrite <- H'2 | idtac ]; auto with stalmarck.
apply trans_eq with (y := tEval f a); auto with stalmarck.
apply sym_eq.
apply equalBeforeTEval; auto with stalmarck.
apply equalBeforeLt with (2 := H'1); auto with stalmarck.
red in H'0; auto with datatypes stalmarck.
lapply H'; clear H';
 [ intros H'; lapply H'; clear H'; [ intros H' | idtac ] | idtac ]; 
 auto with stalmarck.
apply equalBeforeLt with (2 := H'1); auto with stalmarck.
red in |- *; red in H'0; auto with datatypes stalmarck.
Qed.

#[export] Hint Resolve supportTriplets : stalmarck.

Theorem inLt :
 forall (e : rExpr) (n : rNat), inRExpr n e -> rlt n (rnext (maxVar e)).
Proof.
simple induction e; intros.
inversion H.
inversion H.
inversion H; simpl in |- *; auto with stalmarck.
inversion H0; simpl in |- *; auto with stalmarck.
inversion H1; simpl in |- *; auto with stalmarck.
apply rltTransRnext1 with (m := maxVar r0); auto with stalmarck.
apply rltTransRnext1 with (m := maxVar r1); auto with stalmarck.
Qed.

Theorem equalBeforeREval :
 forall (f g : rNat -> bool) (e : rExpr),
 equalBefore (rnext (maxVar e)) f g -> rEval f e = rEval g e.
Proof.
intros f g e H'.
apply support; auto with stalmarck.
intros n H'0.
apply equalBeforeElim with (n := rnext (maxVar e)); auto with stalmarck.
apply inLt; auto with stalmarck.
Qed.
