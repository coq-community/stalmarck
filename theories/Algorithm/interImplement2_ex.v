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

(** * interImplement2_ex

Pierre Letouzey & Laurent Thery

How to use our module on ordered list
*)

From Stalmarck Require Import interImplement2.
From Coq Require Import ZArith.

#[local] Definition A := rArrayInit _ (fun n : rNat => class nil).

#[local] Definition d2 := rZPlus (P_of_succ_nat 2).

#[local] Definition d3 := rZPlus (P_of_succ_nat 3).

#[local] Definition d4 := rZPlus (P_of_succ_nat 4).

#[local] Definition BP := addEqMem A d2 d3.

#[local] Definition B := match BP with
         | triple B _ _ => B
         end.

#[local] Definition LB := match BP with
          | triple _ _ LB => LB
          end.

#[local] Definition CP := addEqMem B d3 d4.

#[local] Definition C := match CP with
         | triple B _ _ => B
         end.

#[local] Definition LC := appendRz match CP with
                   | triple _ _ LB => LB
                   end LB.

#[local] Definition DP := addEqMem A d2 d4.

#[local] Definition D := match DP with
         | triple B _ _ => B
         end.

#[local] Definition LD := match DP with
          | triple _ _ LB => LB
          end.

#[local] Definition EP := interMem C D A LC LD.

#[local] Definition E := fst EP.

Eval compute in (evalZ E (rZComp d4)).
