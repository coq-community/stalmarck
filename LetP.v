(****************************************************************************
                                                                           
          Stalmarck  :  LetP                                               
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 A let that is left untouched by Simpl *)

Definition LetP : forall (A B : Set) (h : A), (forall u : A, u = h -> B) -> B.
intros A B h H'.
apply H' with (u := h).
auto.
Defined.