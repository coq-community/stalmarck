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