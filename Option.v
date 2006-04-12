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
                                                                           
          Stalmarck  : Option                                              
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 An optional type to handle partial function *)

Inductive Option (A : Set) : Set :=
  | Some : forall x : A, Option A
  | None : Option A.
(* Equality on option values  *)

Inductive eqOption (A : Set) (eq : A -> A -> Prop) :
Option A -> Option A -> Prop :=
  | eqOptionSome :
      forall a b : A, eq a b -> eqOption A eq (Some A a) (Some A b)
  | eqOptionNone : eqOption A eq (None A) (None A).
Hint Resolve eqOptionSome eqOptionNone.
(* Compatibility theorem *)

Theorem SomeComp : forall (A : Set) (a b : A), a = b -> Some A a = Some A b.
intros A a b H'; rewrite H'; auto.
Qed.
Hint Resolve SomeComp.