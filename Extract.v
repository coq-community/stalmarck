Require Import algoRun.
Require Import ZArith.

Definition eqOp := normalize.Eq. (* To circumvent the clash with Datatypes.Eq *)

Extraction "run.ml" run checkTracef zero P_of_succ_nat eqOp.