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
                                                                           
          Stalmarck  : stateExtra                                           
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
****************************************************************************
Some extra results concerning mostly realizability of states *)
Require Export stateDec.

(* Auxillary function,  if  for the state S, i =+/- n returns ~ (f n)  otherwise (f n) *)

Definition fnAux (S : State) (f : rNat -> bool) (i : rZ) 
  (n : rNat) :=
  match eqStateRzDec S (rZPlus n) i with
  | left _ => negb (f n)
  | right _ =>
      match eqStateRzDec S (rZMinus n) i with
      | left _ => negb (f n)
      | right _ => f n
      end
  end.
(* fnAux returns the opposite valuation for elements in relation with i *)

Lemma RealizableAux1 :
 forall (S : State) (f : rNat -> bool) (i j : rZ),
 eqStateRz S j i -> rZEval (fnAux S f i) j = negb (rZEval f j).
simple destruct j; intros n Eq; unfold fnAux in |- *; simpl in |- *.
case (eqStateRzDec S (rZPlus n) i); auto with stalmarck.
intros Abs; absurd (eqStateRz S (rZPlus n) i); auto with stalmarck.
case (eqStateRzDec S (rZPlus n) i); auto with stalmarck.
case (eqStateRzDec S (rZMinus n) i); auto with stalmarck.
intros Abs; absurd (eqStateRz S (rZMinus n) i); auto with stalmarck.
Qed.
(* For the other the valuation remains the same *)

Lemma RealizableAux2 :
 forall (S : State) (f : rNat -> bool) (i j : rZ),
 ~ eqStateRz S j i ->
 ~ eqStateRz S (rZComp j) i -> rZEval (fnAux S f i) j = rZEval f j.
simple destruct j; intros n Eq1 Eq2; unfold fnAux in |- *; simpl in |- *;
 case (eqStateRzDec S (rZPlus n) i); case (eqStateRzDec S (rZMinus n) i);
 auto with stalmarck; intros;
 (absurd (eqStateRz S (rZPlus n) i); auto with stalmarck; fail) ||
   absurd (eqStateRz S (rZMinus n) i); auto with stalmarck.
Qed.

Lemma negbElim : forall b b' : bool, negb b = negb b' -> b = b'.
simple destruct b; simple destruct b'; simpl in |- *; auto with stalmarck.
Qed.
Hint Immediate negbElim : stalmarck.
(* Realizability does not change using fnAux *)

Lemma RealizableAux3 :
 forall (S : State) (f : rNat -> bool) (i : rZ),
 realizeState f S -> realizeState (fnAux S f i) S.
unfold realizeState in |- *; intros S f i H j k H1.
case (eqStateRzDec S k i); intros H2.
rewrite (RealizableAux1 S f i k); auto with stalmarck; rewrite (RealizableAux1 S f i j);
 [ rewrite (H j k H1) | apply eqStateRzTrans with (b := k) ]; 
 auto with stalmarck.
case (eqStateRzDec S (rZComp k) i); intros H3.
apply negbElim; rewrite <- (rZEvalCompInv j (fnAux S f i));
 rewrite <- (rZEvalCompInv k (fnAux S f i)).
rewrite (RealizableAux1 S f i (rZComp k)); auto with stalmarck;
 rewrite (RealizableAux1 S f i (rZComp j)); auto with stalmarck;
 [ rewrite (rZEvalCompInv j f); rewrite (rZEvalCompInv k f);
    rewrite (H j k H1)
 | apply eqStateRzTrans with (b := rZComp k) ]; auto with stalmarck.
rewrite (RealizableAux2 S f i k); auto with stalmarck; rewrite (RealizableAux2 S f i j);
 auto with stalmarck.
red in |- *; intro; absurd (eqStateRz S k i); auto with stalmarck;
 apply eqStateRzTrans with (b := j); auto with stalmarck; apply eqStateRzSym; 
 auto with stalmarck.
red in |- *; intro; absurd (eqStateRz S (rZComp k) i); auto with stalmarck;
 apply eqStateRzTrans with (b := rZComp j); auto with stalmarck; apply eqStateRzSym; 
 auto with stalmarck.
Qed.

Lemma EqboolDec : forall b b' : bool, {b = b'} + {negb b = b'}.
simple destruct b; simple destruct b'; simpl in |- *; auto with stalmarck.
Qed.
(* For every state that is not contradictory , there is a valuation
   that realizes it *)

Theorem Realizable :
 forall S : State,
 ~ contradictory S -> exists f : rNat -> bool, realizeState f S.
simple induction S.
intros Abs; exists (fun n : rNat => true); auto with stalmarck.
intros p; case p; intros i j l HR Abs.
cut (~ contradictory l).
intros Abs'; elim (HR Abs'); intros f Hf.
case (eqStateRzDec l j i); intros Lij.
exists f; apply (realizeStateIncl f l (pair i j :: l)); auto with stalmarck;
 apply (inclStateAddEqInv i j l l); auto with stalmarck.
case (EqboolDec (rZEval f i) (rZEval f j)); intros Fij.
exists f; lapply (realizeStateAddEq f l Hf i j); auto with stalmarck.
exists (fnAux l f i);
 lapply (realizeStateAddEq (fnAux l f i) l (RealizableAux3 l f i Hf) i j);
 auto with stalmarck.
rewrite (RealizableAux1 l f i i); auto with stalmarck; rewrite Fij.
rewrite (RealizableAux2 l f i j); auto with stalmarck.
red in |- *; intros Abs1; absurd (contradictory (pair i j :: l)); auto with stalmarck.
unfold contradictory in |- *; exists i; auto with stalmarck;
 apply eqStateRzTrans with (b := rZComp j); auto with stalmarck.
red in |- *; unfold contradictory in |- *; intros Abs1; elim Abs1;
 intros a Pa.
absurd (contradictory (pair i j :: l)); auto with stalmarck; unfold contradictory in |- *;
 exists a; auto with stalmarck.
Qed.
(* The opposite of a valuation that realizes a state still does it *)

Lemma RealizeNegb :
 forall (S : State) (f : rNat -> bool),
 realizeState f S -> realizeState (fun n : rNat => negb (f n)) S.
unfold realizeState in |- *; intros S f Hf i j Hij; generalize (Hf i j Hij);
 case i; case j; simpl in |- *; intros n m Hnm; rewrite Hnm; 
 auto with stalmarck.
Qed.
Hint Resolve RealizeNegb : stalmarck.
(* Same as Realizable but with the constrain that (f zero)=true *)

Theorem Realizable2 :
 forall S : State,
 ~ contradictory S ->
 exists f : rNat -> bool, realizeState f S /\ f zero = true.
intros S HS; elim (Realizable S HS); intros f Hf.
case (EqboolDec (f zero) true); intros H.
exists f; auto with stalmarck.
exists (fun n : rNat => negb (f n)); split; auto with bool stalmarck.
Qed.
(* If an equation is not valid, there is a valuation that refutes it *)

Theorem RealizableCstr :
 forall (S : State) (i j : rZ),
 ~ eqStateRz S i j ->
 exists f : rNat -> bool, realizeState f S /\ negb (rZEval f i) = rZEval f j.
intros S i j Hij; elim (Realizable S); [ intros f Pf | idtac ].
case (eqStateRzDec S (rZComp j) i); intros Hij'.
exists f; split; auto with stalmarck; rewrite (realizeStateInvComp f S Pf j i); auto with stalmarck;
 rewrite <- (rZCompInv j); auto with stalmarck.
case (EqboolDec (rZEval f i) (rZEval f j)); intros Fij.
exists (fnAux S f i); split; auto with stalmarck;
 [ apply RealizableAux3
 | rewrite (RealizableAux1 S f i i); auto with stalmarck; rewrite (RealizableAux2 S f i j) ];
 auto with stalmarck.
rewrite Fij; case (rZEval f j); simpl in |- *; auto with stalmarck.
exists f; split; auto with stalmarck.
red in |- *; intros Contr; elim Contr; intros a Pa; absurd (eqStateRz S i j);
 auto with stalmarck; apply eqStateRzContr with (a := a); auto with stalmarck.
Qed.
(* Realizability implies inclusion *)

Theorem realizeStateInclInv :
 forall S1 S2 : State,
 (forall f : rNat -> bool,
  f zero = true -> realizeState f S2 -> realizeState f S1) -> 
 inclState S1 S2.
intros S1 S2 H; apply inclStateIn; intros i j Pij1.
case (eqStateRzDec S2 j i); intros Pij2; auto with stalmarck.
elim (RealizableCstr S2 i j); auto with stalmarck; intros f Pf; elim Pf; intros Pf1 Pf2.
case (EqboolDec (f zero) true); intros P0.
generalize (H f P0 Pf1); unfold realizeState in |- *; intros H1.
rewrite (H1 i j) in Pf2; auto with stalmarck.
generalize Pf2; case (rZEval f j); simpl in |- *; intros Abs; inversion Abs.
generalize (H (fun n : rNat => negb (f n)) P0 (RealizeNegb S2 f Pf1));
 unfold realizeState in |- *; intros H1.
generalize (H1 i j Pij1) Pf2; case i; case j; simpl in |- *; intros n m Abs1;
 rewrite Abs1; case (f n); simpl in |- *; intros Abs2; 
 inversion Abs2.
Qed.
