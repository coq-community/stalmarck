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
                                                                           
          Stalmarck  : PolyListAux                                         
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 Definition of rem a function that removes elt from polymorphic lists *)
Require Import Arith.
Require Import List.
Section Auxrem.
Variable A : Set.
Variable ADec : forall a b : A, {a = b} + {a <> b}.

Theorem NotInCons1 :
 forall (a b : A) (L : list A), ~ In a (b :: L) -> ~ In a L.
intros a b L H'; red in |- *; intros H'0; apply H'; simpl in |- *; auto.
Qed.

Theorem map_id :
 forall f : A -> A,
 (forall x : A, f (f x) = x) -> forall L : list A, map f (map f L) = L.
intros f H' L; elim L; simpl in |- *; auto.
intros a l H'0.
rewrite H'; rewrite H'0; auto.
Qed.

Fixpoint rem (a : A) (L : list A) {struct L} : list A :=
  match L with
  | nil => nil
  | b :: L1 =>
      match ADec a b with
      | left _ => rem a L1
      | right _ => b :: rem a L1
      end
  end.

Theorem remNotIn : forall (a : A) (L : list A), ~ In a (rem a L).
intros a L; elim L; simpl in |- *; auto.
intros a0 l H'; case (ADec a a0); auto.
intros H'0; red in |- *; intros H'1; case H'1; auto.
Qed.

Theorem remIn :
 forall (a b : A) (L : list A), In b L -> a <> b -> In b (rem a L).
intros a b L; elim L; simpl in |- *; auto.
intros a0 l H' H'0 H'1; case (ADec a a0); case H'0; auto with datatypes.
intros H'2 H'3; case H'1; rewrite H'3; auto.
intros H'2; rewrite H'2; auto with datatypes.
Qed.

Theorem remEq : forall (a : A) (L : list A), ~ In a L -> rem a L = L.
intros a L; elim L; simpl in |- *; auto.
intros a0 l H' H'0; case (ADec a a0); auto with datatypes.
intros H'1; case H'0; auto.
intros H'1; rewrite H'; auto.
Qed.

Theorem remSizeLess :
 forall (a : A) (L : list A), In a L -> length (rem a L) < length L.
intros a L; elim L; simpl in |- *; auto.
intros H'; elim H'.
intros a0 l H' H'0; case (ADec a a0); simpl in |- *; auto with datatypes.
intros H'1; case (In_dec ADec a l); auto with arith.
intros H'2; rewrite remEq; auto.
intros H'1; case H'0; auto with arith.
intros H'2; case H'1; auto.
Qed.
End Auxrem.
Global Hint Resolve remSizeLess remEq remIn remNotIn : core.
