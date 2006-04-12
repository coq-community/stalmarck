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
                                                                           
          Stalmarck  : OrderedListEq_ex                                    
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 How to use OrderedList *)
Require Import OrderedListEq.

(* For Nat *)
Require Import Arith.

Definition CNat : forall a b : nat, {a < b} + {b < a} + {a = b}.
fix 1; intros a; case a; [ idtac | intros a' ]; intros b; case b;
 try intros b'.
right; auto.
left; left; auto with arith.
left; right; auto with arith.
case (CNat a' b'); intros s; [ case s; clear s; intros s | idtac ].
left; left; auto with arith.
left; right; auto with arith.
right; auto.
Defined.

Let appnat := appendf _ lt (fun x y : nat => x = y) CNat.

Definition eqTriv :
  forall a b : nat,
  (fun x y : nat => x = y :>nat) a b ->
  {(fun x y : nat => x = y :>nat) a b} +
  {~ (fun x y : nat => x = y :>nat) a b}.
intros a b H'; left; auto.
Defined.

Let getminnat :=
  getMin _ lt (fun x y : nat => x = y) CNat (fun x y : nat => x = y) eqTriv.

Let internat := interf _ lt (fun x y : nat => x = y) CNat.

Let l1 := 1 :: 3 :: 5 :: 7 :: nil.

Let l2 := 2 :: 3 :: 5 :: 6 :: nil.
Eval compute in (appnat l1 l2).
Eval compute in (getminnat l1 l2).
Eval compute in (internat l1 l2).

(* For Z *)
Require Import ZArith.
Require Import Omega.

Definition CZ : forall a b : Z, {(a < b)%Z} + {(b < a)%Z} + {a = b}.
intros a b; CaseEq (a - b)%Z.
intros H'; right; auto with zarith.
left; right; auto with zarith.
apply Zlt_O_minus_lt; auto.
rewrite H; auto with zarith.
red in |- *; simpl in |- *; auto.
intros p H'; left; left.
apply Zlt_O_minus_lt; auto with zarith.
rewrite <- (Zopp_involutive (b - a)); auto with zarith.
replace (- (b - a))%Z with (a - b)%Z; auto with zarith.
rewrite H'; red in |- *; simpl in |- *; auto.
Defined.

Let appZ := appendf _ Zlt (fun x y : Z => x = y) CZ.

Definition eqTrivZ :
  forall a b : Z,
  (fun x y : Z => x = y :>Z) a b ->
  {(fun x y : Z => x = y :>Z) a b} + {~ (fun x y : Z => x = y :>Z) a b}.
intros a b H'; left; auto.
Defined.

Let getminZ :=
  getMin _ Zlt (fun x y : Z => x = y) CZ (fun x y : Z => x = y) eqTrivZ.

Let interZ := interf _ Zlt (fun x y : Z => x = y) CZ.

Let Zl1 :=
  (- Z_of_nat 3)%Z :: (- Z_of_nat 1)%Z :: Z_of_nat 5 :: Z_of_nat 7 :: nil.

Let Zl2 :=
  (- Z_of_nat 3)%Z :: (- Z_of_nat 2)%Z :: Z_of_nat 5 :: Z_of_nat 6 :: nil.
Eval compute in (appZ Zl1 Zl2).
Eval compute in (getminZ Zl1 Zl2).
Eval compute in (interZ Zl1 Zl2).