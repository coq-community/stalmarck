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

(** * sTactic

Laurent Thery

Some simple tactics
*)

#[export] Set Asymmetric Patterns.

Theorem Contradict1 : forall a b : Prop, b -> (a -> ~ b) -> ~ a.
intuition.
Qed.

Theorem Contradict2 : forall a b : Prop, b -> ~ b -> a.
intuition.
Qed.

Theorem Contradict3 : forall a : Prop, a -> ~ ~ a.
auto.
Qed.
(* Contradict is used to contradict an hypothesis H
  if we have H:~A |- B the result is |- A
  if we have H:~A |- ~B the result is H:B |- A
*)

Ltac Contradict name :=
  (apply (fun a : Prop => Contradict1 a _ name); clear name; intros name) ||
    (apply (fun a : Prop => Contradict2 a _ name); clear name);
   try apply Contradict3.

(* Same as Case but keeps an equality *)

Ltac CaseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.
(* Same as Case but cleans the case variable  *)

Ltac Casec name := case name; clear name.
(* Same as Elim but cleans the elim variable  *)

Ltac Elimc name := elim name; clear name.

Create HintDb stalmarck.
