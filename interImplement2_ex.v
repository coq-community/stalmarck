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
                                                                           
          Stalmarck  :   interImplement2_ex                               
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
How to use our module on ordered list*)
Require Import interImplement2.
Require Import ZArith.

Local Definition A := rArrayInit _ (fun n : rNat => class nil).

Local Definition d2 := rZPlus (P_of_succ_nat 2).

Local Definition d3 := rZPlus (P_of_succ_nat 3).

Local Definition d4 := rZPlus (P_of_succ_nat 4).

Local Definition BP := addEqMem A d2 d3.

Local Definition B := match BP with
         | triple B _ _ => B
         end.

Local Definition LB := match BP with
          | triple _ _ LB => LB
          end.

Local Definition CP := addEqMem B d3 d4.

Local Definition C := match CP with
         | triple B _ _ => B
         end.

Local Definition LC := appendRz match CP with
                   | triple _ _ LB => LB
                   end LB.

Local Definition DP := addEqMem A d2 d4.

Local Definition D := match DP with
         | triple B _ _ => B
         end.

Local Definition LD := match DP with
          | triple _ _ LB => LB
          end.

Local Definition EP := interMem C D A LC LD.

Local Definition E := fst EP.
Eval compute in (evalZ E (rZComp d4)).
