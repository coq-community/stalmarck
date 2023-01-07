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

(** * OrderedListEq_ex

Pierre Letouzey & Laurent Thery

How to use OrderedList
*)

From Stalmarck Require Import OrderedListEq.
From Coq Require Import Arith. (* For Nat *)

Definition CNat : forall a b : nat, {a < b} + {b < a} + {a = b}.
fix CNat 1; intros a; case a; [ idtac | intros a' ]; intros b; case b;
 try intros b'.
right; auto.
left; left; auto with arith.
left; right; auto with arith.
case (CNat a' b'); intros s; [ case s; clear s; intros s | idtac ].
left; left; auto with arith.
left; right; auto with arith.
right; auto.
Defined.

#[local] Definition appnat := appendf _ lt (fun x y : nat => x = y) CNat.

Definition eqTriv :
  forall a b : nat,
  (fun x y : nat => x = y :>nat) a b ->
  {(fun x y : nat => x = y :>nat) a b} +
  {~ (fun x y : nat => x = y :>nat) a b}.
intros a b H'; left; auto.
Defined.

#[local] Definition getminnat :=
  getMin _ lt (fun x y : nat => x = y) CNat (fun x y : nat => x = y) eqTriv.

#[local] Definition internat := interf _ lt (fun x y : nat => x = y) CNat.

#[local] Definition l1 := 1 :: 3 :: 5 :: 7 :: nil.

#[local] Definition l2 := 2 :: 3 :: 5 :: 6 :: nil.

Eval compute in (appnat l1 l2).
Eval compute in (getminnat l1 l2).
Eval compute in (internat l1 l2).

From Coq Require Import ZArith. (* For Z *)

Definition CZ : forall a b : Z, {(a < b)%Z} + {(b < a)%Z} + {a = b}.
intros a b; CaseEq (a - b)%Z.
intros H'; right; auto with zarith.
left; right; auto with zarith.
intros p H'; left; left.
apply Zlt_O_minus_lt; auto with zarith.
Defined.

#[local] Definition appZ := appendf _ Z.lt (fun x y : Z => x = y) CZ.

Definition eqTrivZ :
  forall a b : Z,
  (fun x y : Z => x = y :>Z) a b ->
  {(fun x y : Z => x = y :>Z) a b} + {~ (fun x y : Z => x = y :>Z) a b}.
intros a b H'; left; auto.
Defined.

#[local] Definition getminZ :=
  getMin _ Z.lt (fun x y : Z => x = y) CZ (fun x y : Z => x = y) eqTrivZ.

#[local] Definition interZ := interf _ Z.lt (fun x y : Z => x = y) CZ.

#[local] Definition Zl1 :=
  (- Z_of_nat 3)%Z :: (- Z_of_nat 1)%Z :: Z_of_nat 5 :: Z_of_nat 7 :: nil.

#[local] Definition Zl2 :=
  (- Z_of_nat 3)%Z :: (- Z_of_nat 2)%Z :: Z_of_nat 5 :: Z_of_nat 6 :: nil.

Eval compute in (appZ Zl1 Zl2).
Eval compute in (getminZ Zl1 Zl2).
Eval compute in (interZ Zl1 Zl2).
