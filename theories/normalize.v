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
                                                                           
          Stalmarck  :  normalize                                          
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 We define our notion of boolean expression (Expr) with the connectors
 And Or Impl Eq, then we define the notion of reduced boolean expression
(rExpr) with only the connectors And and Eq.
   We define the normalization of Expr -> rExpr and show that it conserves
   the semantic of the formula *)
Require Export BoolAux.
Require Export rZ.
(* Here is the full set of boolean operator  (True is (V zero) !!!)*)

Inductive boolOp : Set :=
  | ANd : boolOp
  | Or : boolOp
  | Impl : boolOp
  | Eq : boolOp.
(* The boolean expression *)

Inductive Expr : Set :=
  | V : rNat -> Expr
  | N : Expr -> Expr
  | Node : boolOp -> Expr -> Expr -> Expr.

(*The semantics of  boolean operators *)

Definition boolOpFun (n : boolOp) :=
  match n with
  | ANd => andb
  | Or => orb
  | Impl => implb
  | normalize.Eq => eqb
  end.
(* A valuation function *)

Fixpoint Eval (f : rNat -> bool) (e : Expr) {struct e} : bool :=
  match e with
  | V n => f n
  | normalize.N p => negb (Eval f p)
  | Node n p q => boolOpFun n (Eval f p) (Eval f q)
  end.
(* The reduced set *)

Inductive rBoolOp : Set :=
  | rAnd : rBoolOp
  | rEq : rBoolOp.

Definition rBoolOpFun (n : rBoolOp) :=
  match n with
  | rAnd => andb
  | rEq => eqb
  end.

Inductive rExpr : Set :=
  | rV : rNat -> rExpr
  | rN : rExpr -> rExpr
  | rNode : rBoolOp -> rExpr -> rExpr -> rExpr.
(* the valuation function *)

Fixpoint rEval (f : rNat -> bool) (x : rExpr) {struct x} : bool :=
  match x with
  | rV n => f n
  | rN x => negb (rEval f x)
  | rNode n x1 x2 => rBoolOpFun n (rEval f x1) (rEval f x2)
  end.
(*Compute the maximum variable in an expression *)

Fixpoint maxVar (e : rExpr) : rNat :=
  match e with
  | rV n => n
  | rN p => maxVar p
  | rNode n p q => rmax (maxVar p) (maxVar q)
  end.
(* Check if a variable is in an expression *)

Inductive inRExpr (n : rNat) : rExpr -> Prop :=
  | inRV : inRExpr n (rV n)
  | inRN : forall e : rExpr, inRExpr n e -> inRExpr n (rN e)
  | inRNodeLeft :
      forall (i : rBoolOp) (e1 e2 : rExpr),
      inRExpr n e1 -> inRExpr n (rNode i e1 e2)
  | inRNodeRight :
      forall (i : rBoolOp) (e1 e2 : rExpr),
      inRExpr n e2 -> inRExpr n (rNode i e1 e2).
#[export] Hint Resolve inRV inRN inRNodeLeft inRNodeRight : stalmarck.
(* Two valuation functions that gives the same value to variables of a formula
   gives the same value to the formula *)

Theorem support :
 forall (f g : rNat -> bool) (e : rExpr),
 (forall n : rNat, inRExpr n e -> f n = g n) -> rEval f e = rEval g e.
intros f g e.
elim e; intros; simpl in |- *; auto with stalmarck; rewrite H; auto with stalmarck; rewrite H0; auto with stalmarck.
Qed.
#[export] Hint Resolve support : stalmarck.

(* Normalization from Expr -> rExpr 
   we first define it for each operator, than norm does the dispatching *)

Definition normNot (p : rExpr) :=
  match p with
  | rN p1 => p1
  | p1 => rN p1
  end.

Lemma normNotEval :
 forall (p : rExpr) (f : rNat -> bool),
 rEval f (normNot p) = negb (rEval f p).
intros; case p; simpl in |- *; auto with stalmarck; intros; rewrite negb_elim; auto with stalmarck.
Qed.

Definition normOr (p q : rExpr) :=
  match p, q with
  | rN p1, rN q1 => rN (rNode rAnd p1 q1)
  | rN p1, q1 => rN (rNode rAnd p1 (rN q1))
  | p1, rN q1 => rN (rNode rAnd (rN p1) q1)
  | p1, q1 => rN (rNode rAnd (rN p1) (rN q1))
  end.

Lemma normOrEval :
 forall (p q : rExpr) (f : rNat -> bool),
 rEval f (normOr p q) = rEval f p || rEval f q.
intros; case p; case q; intros; simpl in |- *; auto with bool stalmarck;
 try rewrite de_morgan2; try rewrite negb_elim; auto with stalmarck.
Qed.

Definition normImpl (p q : rExpr) :=
  match p, q with
  | rN p1, rN q1 => rN (rNode rAnd (rN p1) q1)
  | rN p1, q1 => rN (rNode rAnd (rN p1) (rN q1))
  | p1, rN q1 => rN (rNode rAnd p1 q1)
  | p1, q1 => rN (rNode rAnd p1 (rN q1))
  end.

Lemma normImplEval :
 forall (p q : rExpr) (f : rNat -> bool),
 rEval f (normImpl p q) = implb (rEval f p) (rEval f q).
intros; case p; case q; intros; simpl in |- *; auto with stalmarck; rewrite implb_elim;
 rewrite negb_elim; auto with stalmarck.
Qed.

Fixpoint norm (e : Expr) : rExpr :=
  match e with
  | V n => rV n
  | normalize.N p => normNot (norm p)
  | Node n1 p q =>
      match n1 with
      | ANd => rNode rAnd (norm p) (norm q)
      | Or => normOr (norm p) (norm q)
      | Impl => normImpl (norm p) (norm q)
      | normalize.Eq => rNode rEq (norm p) (norm q)
      end
  end.
(* In the normalization we kept the semantic *)

Theorem normEval :
 forall (f : rNat -> bool) (e : Expr), Eval f e = rEval f (norm e).
simple induction e; clear e; simpl in |- *; auto with stalmarck.
intros p H; rewrite normNotEval; rewrite H; auto with stalmarck.
intros b p Hp q Hq; case b; rewrite Hp; rewrite Hq; auto with stalmarck;
 rewrite normOrEval || rewrite normImplEval; auto with stalmarck.
Qed.

(* Definition of what it is to be a tautology 
   (remember that we code True as (V zero) *)

Definition Tautology (e : Expr) :=
  forall f : rNat -> bool, f zero = true -> Eval f e = true.

Definition rTautology (e : rExpr) :=
  forall f : rNat -> bool, f zero = true -> rEval f e = true.
(* We didn't change the notion of tautology *)

Theorem TautoRTauto : forall e : Expr, Tautology e <-> rTautology (norm e).
intros e; unfold Tautology in |- *; unfold rTautology in |- *; split.
intros H' f; rewrite <- normEval; auto with stalmarck.
intros H' f; rewrite normEval; auto with stalmarck.
Qed.
