
(****************************************************************************
                                                                           
          Stalmarck  :   interImplement2_ex                               
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
How to use our module on ordered list*)
Require Import interImplement2.
Require Import ZArith.

Let A := rArrayInit _ (fun n : rNat => class nil).

Let d2 := rZPlus (P_of_succ_nat 2).

Let d3 := rZPlus (P_of_succ_nat 3).

Let d4 := rZPlus (P_of_succ_nat 4).

Let BP := addEqMem A d2 d3.

Let B := match BP with
         | triple B _ _ => B
         end.

Let LB := match BP with
          | triple _ _ LB => LB
          end.

Let CP := addEqMem B d3 d4.

Let C := match CP with
         | triple B _ _ => B
         end.

Let LC := appendRz match CP with
                   | triple _ _ LB => LB
                   end LB.

Let DP := addEqMem A d2 d4.

Let D := match DP with
         | triple B _ _ => B
         end.

Let LD := match DP with
          | triple _ _ LB => LB
          end.

Let EP := interMem C D A LC LD.

Let E := fst EP.
Eval compute in (evalZ E (rZComp d4)).