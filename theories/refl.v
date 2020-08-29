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
                                                                           
          Stalmarck  :  refl                                                    
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
construct a function from Expr -> Prop*)
Require Import ZArith.
Require Import normalize.
Require Import Classical.
Require Import sTactic.
Section refl.
Variable fmap : rNat -> Prop.
Hypothesis fmapO : fmap zero.
(* Standard translation of boolean expression to Propositions, f is the function
 that gives meaning to boolean variables *)

Fixpoint ExprToProp (e : Expr) : Prop :=
  match e with
  | V n => fmap n
  | normalize.N e' => ~ ExprToProp e'
  | Node ANd e1' e2' => ExprToProp e1' /\ ExprToProp e2'
  | Node Or e1' e2' => ExprToProp e1' \/ ExprToProp e2'
  | Node Impl e1' e2' => ExprToProp e1' -> ExprToProp e2'
  | Node normalize.Eq e1' e2' => ExprToProp e1' <-> ExprToProp e2'
  end.
(* A variable n is in a boolean expression *)

Inductive inExpr (n : rNat) : Expr -> Prop :=
  | inV : inExpr n (V n)
  | inN : forall e : Expr, inExpr n e -> inExpr n (normalize.N e)
  | inNodeLeft :
      forall (i : boolOp) (e1 e2 : Expr),
      inExpr n e1 -> inExpr n (Node i e1 e2)
  | inNodeRight :
      forall (i : boolOp) (e1 e2 : Expr),
      inExpr n e2 -> inExpr n (Node i e1 e2).
Hint Resolve inV inN inNodeLeft inNodeRight : stalmarck.
(* This is of course decidable *)

Definition inExprDec :
  forall (a : rNat) (e : Expr), {inExpr a e} + {~ inExpr a e}.
intros a e; elim e.
intros r; case (rNatDec a r).
intros H'; rewrite <- H'; auto with stalmarck.
intros H'; right; red in |- *; intros H'0; case H'; inversion H'0; auto with stalmarck.
intros e0 H'; case H'; intros H'0; auto with stalmarck.
right; red in |- *; intros H'1; case H'0; inversion H'1; auto with stalmarck.
intros b e0 H' e1 H'0; case H'; intros H'1; auto with stalmarck.
case H'0; intros H'2; auto with stalmarck.
right; red in |- *; intros H'3; generalize H'2 H'1; inversion H'3; intuition.
Defined.
(* There is a function that gives true to all the variable whose interpretation
    by f are True *)

Theorem ExprToPropF :
 forall e : Expr,
 exists f : rNat -> bool,
   f zero = true /\
   (forall n : rNat, inExpr n e -> fmap n -> f n = true) /\
   (forall n : rNat, inExpr n e -> ~ fmap n -> f n = false).
intros e; elim e; simpl in |- *; auto with stalmarck.
intros r.
case (rNatDec r zero); auto with stalmarck.
intros H'; exists (fun n : rNat => true).
rewrite H'; split; auto with stalmarck; split; auto with stalmarck.
intros n H'0; inversion H'0; auto with stalmarck.
intros H'1; case H'1; auto with stalmarck.
intros H'; case (classic (fmap r)); intros H'1.
exists (fun n : rNat => true); simpl in |- *; split; auto with stalmarck; split; auto with stalmarck.
intros n H'0; inversion H'0; auto with stalmarck.
intros H'2; case H'2; auto with stalmarck.
exists
 (fun n : rNat =>
  match rNatDec r n with
  | left _ => false
  | right _ => true
  end); simpl in |- *.
split.
case (rNatDec r zero); auto with stalmarck.
split; intros n H'0; inversion H'0; case (rNatDec r r); auto with stalmarck.
intros H'2 H'3; case H'1; auto with stalmarck.
case H'2; auto with stalmarck.
intros e0 H'; Elimc H'; intros f E; Elimc E; intros H' H'0; Elimc H'0;
 intros H'0 H'1.
exists f; split; auto with stalmarck.
split; intros n H'2; inversion H'2; auto with stalmarck.
intros b e0 H' e1 H'0.
Elimc H'; intros f E; Elimc E; intros H' H'1; Elimc H'1; intros H'1 H'2.
Elimc H'0; intros f0 E; Elimc E; intros H'0 H'3; Elimc H'3; intros H'3 H'4.
exists
 (fun n : rNat =>
  match inExprDec n e0 with
  | left _ => f n
  | right _ => f0 n
  end); simpl in |- *.
split.
case (inExprDec zero e0); auto with stalmarck.
split; intros n H'5 H'6; inversion H'5; case (inExprDec n e0); auto with stalmarck.
intros H'7; case H'7; auto with stalmarck.
Qed.
(* The precedent condition is sufficient to insure correctness of the translation *)

Theorem ExprToPropF2 :
 forall (e : Expr) (f : rNat -> bool),
 (forall n : rNat, inExpr n e -> fmap n -> f n = true) ->
 (forall n : rNat, inExpr n e -> ~ fmap n -> f n = false) ->
 (Eval f e = true -> ExprToProp e) /\ (Eval f e = false -> ~ ExprToProp e).
intros e; Elimc e; simpl in |- *; auto with stalmarck.
intros r f H' H'0; split; case (classic (fmap r)); auto with stalmarck.
intros H'1 H'2; absurd (f r = false); auto with stalmarck.
rewrite H'2; red in |- *; intros H'3; discriminate.
intros H'1 H'2; absurd (f r = true); auto with stalmarck.
rewrite H'2; red in |- *; intros H'3; discriminate.
intros e H' f H'0 H'1; split; intros H'2; auto with stalmarck.
elim (H' f); [ intros H'6 H'7; apply H'7 | idtac | idtac ]; auto with stalmarck.
generalize H'2; case (Eval f e); auto with stalmarck.
red in |- *; intros H'3; Contradict H'3.
elim (H' f); [ intros H'4 H'5; apply H'4 | idtac | idtac ]; auto with stalmarck.
generalize H'2; case (Eval f e); auto with stalmarck.
intros b e H' e0 H'0 f H'1 H'2.
generalize (H' f) (H'0 f); clear H' H'0; case b; simpl in |- *.
case (Eval f e); simpl in |- *; auto with stalmarck.
case (Eval f e0); simpl in |- *; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
split.
elim H'; auto with stalmarck.
elim H'0; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; intros H'4; Elimc H'4; intros H'4 H'5.
absurd (ExprToProp e0); auto with stalmarck.
elim H'0; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; intros H'4; Elimc H'4; intros H'4 H'5.
absurd (ExprToProp e); auto with stalmarck.
elim H'; auto with stalmarck.
case (Eval f e); simpl in |- *; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
elim H'; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
elim H'0; auto with stalmarck.
red in |- *; intros H'4; Elimc H'4; intros H'4.
absurd (ExprToProp e); auto with stalmarck.
elim H'; auto with stalmarck.
absurd (ExprToProp e0); auto with stalmarck.
elim H'0; auto with stalmarck.
case (Eval f e); case (Eval f e0); simpl in |- *; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
elim H'0; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; intros H'4.
absurd (ExprToProp e0); auto with stalmarck.
elim H'0; auto with stalmarck.
elim H'; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
elim H'0; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
intros H'4; absurd (ExprToProp e); auto with stalmarck.
elim H'; auto with stalmarck.
case (Eval f e); case (Eval f e0); simpl in |- *; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; split; elim H'0; elim H'; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; intros H'4; absurd (ExprToProp e); auto with stalmarck.
red in |- *; intros H'5; absurd (ExprToProp e0); auto with stalmarck.
elim H'0; auto with stalmarck.
elim H'4; auto with stalmarck.
elim H'; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; intros H'4; absurd (ExprToProp e); auto with stalmarck.
elim H'; auto with stalmarck.
cut (ExprToProp e0); auto with stalmarck.
elim H'4; auto with stalmarck.
elim H'0; auto with stalmarck.
intros H' H'0; split; intros H'3; try discriminate.
red in |- *; split; intros H'4.
absurd (ExprToProp e); auto with stalmarck; elim H'; auto with stalmarck.
absurd (ExprToProp e0); auto with stalmarck; elim H'0; auto with stalmarck.
Qed.
(* If e is a tautoly then its translated is True *)

Theorem ExprToPropTautology : forall e : Expr, Tautology e -> ExprToProp e.
intros e H'.
elim (ExprToPropF e); intros f E; elim E; intros H'1 H'2; elim H'2;
 intros H'3 H'4; clear H'2 E.
elim (ExprToPropF2 e f); [ intros H'7 H'8; apply H'7 | idtac | idtac ]; auto with stalmarck.
Qed.
End refl.

(* We define arrays  on Prop in order to build the function for variables*)
Section rA.

Inductive POption : Type :=
  | PSome : Prop -> POption
  | PNone : POption.

Inductive rTreeP : Type :=
  | rEmptyP : rTreeP
  | rSplitP : POption -> rTreeP -> rTreeP -> rTreeP.

Fixpoint rTreeGetP (t : rTreeP) (r : rNat) {struct r} : POption :=
  match r, t with
  | _, rEmptyP => PNone
  | BinPos.xH, rSplitP a _ _ => a
  | BinPos.xO p, rSplitP _ t' _ => rTreeGetP t' p
  | BinPos.xI p, rSplitP _ _ t' => rTreeGetP t' p
  end.

Fixpoint rTreeSetP (t : rTreeP) (r : rNat) {struct r} : 
 Prop -> rTreeP :=
  fun a : Prop =>
  match r, t with
  | BinPos.xH, rEmptyP => rSplitP (PSome a) rEmptyP rEmptyP
  | BinPos.xO p, rEmptyP => rSplitP PNone (rTreeSetP rEmptyP p a) rEmptyP
  | BinPos.xI p, rEmptyP => rSplitP PNone rEmptyP (rTreeSetP rEmptyP p a)
  | BinPos.xH, rSplitP _ t'1 t'2 => rSplitP (PSome a) t'1 t'2
  | BinPos.xO p, rSplitP b t'1 t'2 => rSplitP b (rTreeSetP t'1 p a) t'2
  | BinPos.xI p, rSplitP b t'1 t'2 => rSplitP b t'1 (rTreeSetP t'2 p a)
  end.

Theorem rTreeDef1P :
 forall (t : rTreeP) (m : rNat) (v : Prop),
 rTreeGetP (rTreeSetP t m v) m = PSome v.
intros t m; generalize t; Elimc m; simpl in |- *; clear t.
intros p H' t v; case t; auto with stalmarck.
intros p H' t v; case t; auto with stalmarck.
intros t v; case t; auto with stalmarck.
Qed.

Theorem rTreeDef2 :
 forall (t : rTreeP) (m1 m2 : rNat) (v : Prop),
 m1 <> m2 -> rTreeGetP (rTreeSetP t m1 v) m2 = rTreeGetP t m2.
intros t m; generalize t; Elimc m; simpl in |- *; clear t.
intros p H' t m2 v; case m2; simpl in |- *; case t; auto with stalmarck.
intros p0 H'0; rewrite H'; auto with stalmarck.
elim p0; simpl in |- *; auto with stalmarck.
Contradict H'0; rewrite H'0; auto with stalmarck.
intros a r1 r2 p0 H'0; rewrite H'; auto with stalmarck.
Contradict H'0; rewrite H'0; auto with stalmarck.
intros p0 H'0; elim p0; simpl in |- *; auto with stalmarck.
intros p H' t m2 v; case m2; simpl in |- *; case t; auto with stalmarck.
intros p0 H'0; elim p0; simpl in |- *; auto with stalmarck.
intros p0 H'0; rewrite H'; auto with stalmarck.
elim p0; simpl in |- *; auto with stalmarck.
Contradict H'0; rewrite H'0; auto with stalmarck.
intros a r1 r2 p0 H'0; rewrite H'; auto with stalmarck.
Contradict H'0; rewrite H'0; auto with stalmarck.
intros t m2 v; case m2; simpl in |- *; auto with stalmarck.
case t; intros p H'; elim p; simpl in |- *; auto with stalmarck.
case t; intros p H'; elim p; simpl in |- *; auto with stalmarck.
intros H'; Contradict H'; auto with stalmarck.
Qed.

Inductive rArrayP : Type :=
    rArrayMakeP : rTreeP -> (rNat -> Prop) -> rArrayP.

Definition rArrayGetP (ar : rArrayP) (r : rNat) :=
  match ar with
  | rArrayMakeP t f => match rTreeGetP t r with
                       | PSome a => a
                       | _ => f r
                       end
  end.

Definition rArraySetP (ar : rArrayP) (r : rNat) (v : Prop) :=
  match ar with
  | rArrayMakeP t f => rArrayMakeP (rTreeSetP t r v) f
  end.

Theorem rArrayDef1P :
 forall (Ar : rArrayP) (m : rNat) (v : Prop),
 rArrayGetP (rArraySetP Ar m v) m = v.
intros Ar m v; case Ar; simpl in |- *.
intros r a; rewrite (rTreeDef1P r m v); auto with stalmarck.
Qed.

Theorem rArrayDef2P :
 forall (Ar : rArrayP) (m1 m2 : rNat) (v : Prop),
 m1 <> m2 -> rArrayGetP (rArraySetP Ar m1 v) m2 = rArrayGetP Ar m2.
intros Ar m1 m2 v H'; case Ar; simpl in |- *.
intros r a; rewrite (rTreeDef2 r m1 m2 v); auto with stalmarck.
Qed.

Definition rArrayInitP (f : rNat -> Prop) := rArrayMakeP rEmptyP f.

Theorem rArrayDefP :
 forall (m : rNat) (f : rNat -> Prop), rArrayGetP (rArrayInitP f) m = f m.
intros m f; simpl in |- *; auto with stalmarck.
elim m; simpl in |- *; auto with stalmarck.
Qed.
End rA.
