
(****************************************************************************
                                                                           
          Stalmarck  :  stalt                                           
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
****************************************************************************
Implementation of the Stalt tactic *)

(* The `Stalt' tactic inspired by the Ring tactic *)

(* We have just inserted here the extracted code *)

(*-------------------------------------------------------------------*)
type prop = unit
let prop = ()

type arity = unit
let arity = ()

type positive =
    XI of positive
  | XO of positive
  | XH

type rNat = positive

type rBoolOp =
    RAnd
  | REq

type rExpr =
    RV of rNat
  | RN of rExpr
  | RNode of rBoolOp * rExpr * rExpr

type 'A list =
    Nil
  | Cons of 'A * 'A list

type rZ =
    RZPlus of rNat
  | RZMinus of rNat

type triplet =
    Triplet of rBoolOp * rZ * rZ * rZ

type tripletResult =
    TRC of triplet list * rZ * rNat

let rZComp = function
  RZPlus m -> RZMinus m
| RZMinus m -> RZPlus m

let rec add_un = function
  XI x' -> XO (add_un x')
| XO x' -> XI x'
| XH -> XO XH

let rnext =
  add_un

let rec makeTripletsFun l n = function
  RV i -> TRC (l, (RZPlus i), n)
| RN p ->
    (match makeTripletsFun l n p with
       TRC (n1, s1, l1) -> TRC (n1, (rZComp s1), l1))
| RNode (q, p, node) ->
    (match makeTripletsFun l n p with
       TRC (n1, s1, l1) ->
         (match makeTripletsFun n1 l1 node with
            TRC (n2, s2, l2) -> TRC ((Cons ((Triplet (q, (RZPlus l2),
              s1, s2)), n2)), (RZPlus l2), (rnext l2))))

type relation =
    EGAL
  | INFERIEUR
  | SUPERIEUR

let rec compare x y r =
  match x with
    XI x' ->
      (match y with
         XI y' -> compare x' y' r
       | XO y' -> compare x' y' SUPERIEUR
       | XH -> SUPERIEUR)
  | XO x' ->
      (match y with
         XI y' -> compare x' y' INFERIEUR
       | XO y' -> compare x' y' r
       | XH -> SUPERIEUR)
  | XH ->
      (match y with
         XI y' -> INFERIEUR
       | XO y' -> INFERIEUR
       | XH -> r)

type sumbool =
    Left
  | Right

let rltDec n m =
  (match compare n m EGAL with
     EGAL -> (fun _ _ _ -> Right)
   | INFERIEUR -> (fun _ _ _ -> Left)
   | SUPERIEUR -> (fun _ _ _ -> Right)) prop prop prop

let rmax n m =
  match rltDec n m with
    Left -> m
  | Right -> n

let rec maxVar = function
  RV n -> n
| RN p -> maxVar p
| RNode (q, p, n) -> rmax (maxVar p) (maxVar n)

let makeTriplets e =
  makeTripletsFun Nil (rnext (maxVar e)) e

type boolOp =
    ANd
  | Or
  | Impl
  | Eq

type expr =
    V of rNat
  | N of expr
  | Node of boolOp * expr * expr

let normNot p = match p with
  RV r -> RN p
| RN p1 -> p1
| RNode (r1, r0, r) -> RN p

let normOr p q =
  match p with
    RV r ->
      (match q with
         RV r0 -> RN (RNode (RAnd, (RN p), (RN q)))
       | RN q1 -> RN (RNode (RAnd, (RN p), q1))
       | RNode (r2, r1, r0) -> RN (RNode (RAnd, (RN p), (RN q))))
  | RN p1 ->
      (match q with
         RV r -> RN (RNode (RAnd, p1, (RN q)))
       | RN q1 -> RN (RNode (RAnd, p1, q1))
       | RNode (r1, r0, r) -> RN (RNode (RAnd, p1, (RN q))))
  | RNode (r1, r0, r) ->
      (match q with
         RV r2 -> RN (RNode (RAnd, (RN p), (RN q)))
       | RN q1 -> RN (RNode (RAnd, (RN p), q1))
       | RNode (r4, r3, r2) -> RN (RNode (RAnd, (RN p), (RN q))))

let normImpl p q =
  match p with
    RV r ->
      (match q with
         RV r0 -> RN (RNode (RAnd, p, (RN q)))
       | RN q1 -> RN (RNode (RAnd, p, q1))
       | RNode (r2, r1, r0) -> RN (RNode (RAnd, p, (RN q))))
  | RN p1 ->
      (match q with
         RV r -> RN (RNode (RAnd, (RN p1), (RN q)))
       | RN q1 -> RN (RNode (RAnd, (RN p1), q1))
       | RNode (r1, r0, r) -> RN (RNode (RAnd, (RN p1), (RN q))))
  | RNode (r1, r0, r) ->
      (match q with
         RV r2 -> RN (RNode (RAnd, p, (RN q)))
       | RN q1 -> RN (RNode (RAnd, p, q1))
       | RNode (r4, r3, r2) -> RN (RNode (RAnd, p, (RN q))))

let rec norm = function
  V n -> RV n
| N p -> normNot (norm p)
| Node (q, p, n1) ->
    (match q with
       ANd -> RNode (RAnd, (norm p), (norm n1))
     | Or -> normOr (norm p) (norm n1)
     | Impl -> normImpl (norm p) (norm n1)
     | Eq -> RNode (REq, (norm p), (norm n1)))

let letP h u =
  u h

type 'A option =
    Some of 'A
  | None

type 'A rTree =
    REmpty
  | RSplit of 'A option * 'A rTree * 'A rTree

type 'A rArray =
    RArrayMake of 'A rTree * (rNat -> 'A)

let rec rTreeSet t r a =
  match r with
    XI p ->
      (match t with
         REmpty -> RSplit (None, REmpty, (rTreeSet REmpty p a))
       | RSplit (t'2, t'1, b) -> RSplit (t'2, t'1, (rTreeSet b p a)))
  | XO p ->
      (match t with
         REmpty -> RSplit (None, (rTreeSet REmpty p a), REmpty)
       | RSplit (t'2, t'1, b) -> RSplit (t'2, (rTreeSet t'1 p a), b))
  | XH ->
      (match t with
         REmpty -> RSplit ((Some a), REmpty, REmpty)
       | RSplit (t'2, t'1, r0) -> RSplit ((Some a), t'1, r0))

let rArraySet ar r v =
  match ar with
    RArrayMake (f, t) -> RArrayMake ((rTreeSet f r v), t)

let valRz = function
  RZPlus b -> b
| RZMinus b -> b

let rec rTreeGet t = function
  XI p ->
    (match t with
       REmpty -> None
     | RSplit (t', r1, r0) -> rTreeGet r0 p)
| XO p ->
    (match t with
       REmpty -> None
     | RSplit (o, t', r0) -> rTreeGet t' p)
| XH -> (match t with
           REmpty -> None
         | RSplit (o, r0, a) -> o)

let rArrayGet ar r =
  match ar with
    RArrayMake (f, t) ->
      (match rTreeGet f r with
         Some a -> a
       | None -> t r)

let rec buildL = function
  Nil -> RArrayMake (REmpty, (fun r -> Nil))
| Cons (l1, t) ->
    (match l1 with
       Triplet (r, q, p, r0) ->
         letP
           (letP
             (letP (buildL t) (fun ar1 ->
               rArraySet ar1 (valRz q) (Cons (l1,
                 (rArrayGet ar1 (valRz q)))))) (fun ar2 ->
             rArraySet ar2 (valRz p) (Cons (l1,
               (rArrayGet ar2 (valRz p)))))) (fun ar3 ->
           rArraySet ar3 (valRz r0) (Cons (l1,
             (rArrayGet ar3 (valRz r0))))))

type nat =
    O
  | S of nat

let rec plus n m =
  match n with
    O -> m
  | S p -> S (plus p m)

let rec positive_to_nat x pow2 =
  match x with
    XI x' -> plus pow2 (positive_to_nat x' (plus pow2 pow2))
  | XO x' -> positive_to_nat x' (plus pow2 pow2)
  | XH -> pow2

let convert x =
  positive_to_nat x (S O)

let liftRz f = function
  RZPlus a' -> f a'
| RZMinus a' -> rZComp (f a')

let samePolRz a b =
  liftRz (fun c -> b) a

type vM =
    Ref of rZ
  | Class of rZ list

let evalN ar v =
  match rArrayGet ar v with
    Ref p -> p
  | Class l -> RZPlus v

let evalZ ar v =
  samePolRz v (evalN ar (valRz v))

type 'A sumor =
    Inleft of 'A
  | Inright

let rltEDec n m =
  (match compare n m EGAL with
     EGAL -> (fun _ _ _ -> Inright)
   | INFERIEUR -> (fun _ _ _ -> Inleft Left)
   | SUPERIEUR -> (fun _ _ _ -> Inleft Right)) prop prop prop

let rZltEDec a b =
  rltEDec (valRz a) (valRz b)

let getClassN ar v =
  match rArrayGet ar v with
    Ref r -> Nil
  | Class l -> l

type ('C, 'B, 'A) triple =
    Triple of 'A * 'B * 'C

let mbDOp x1 x0 x =
  Triple (x1, x0, x)

let rec rArraySetList ar a = function
  Nil -> ar
| Cons (ml', m) ->
    rArraySet (rArraySetList ar a m) (valRz ml') (Ref
      (samePolRz ml' a))

let appendf ltADec =
  let rec aux1 l1 l2 =
    match l1 with
      Nil -> (match l2 with
                Nil -> l2
              | Cons (a, l) -> l2)
    | Cons (t1, a) ->
        (match l2 with
           Nil -> l1
         | Cons (t2, b) ->
             (match ltADec t1 t2 with
                Inleft s ->
                  (match s with
                     Left -> Cons (t1, (aux1 a (Cons (t2, b))))
                   | Right ->
                       let rec aux2 = function
                         Nil -> Cons (t1, a)
                       | Cons (t3, c) ->
                           (match ltADec t1 t3 with
                              Inleft s0 ->
                                (match s0 with
                                   Left -> Cons (t1,
                                     (aux1 a (Cons (t3, c))))
                                 | Right -> Cons (t3, (aux2 c)))
                            | Inright -> Cons (t1, (aux1 a c)))
                       in aux2 (Cons (t2, b)))
              | Inright -> Cons (t1, (aux1 a b))))
  in aux1

let appendRz =
  appendf rZltEDec

let map f =
  let rec map0 = function
    Nil -> Nil
  | Cons (t, a) -> Cons ((f t), (map0 a))
  in map0

let fappendf ltADec f =
  let rec aux1 l1 l2 =
    match l1 with
      Nil -> (match l2 with
                Nil -> map f l2
              | Cons (a, l) -> map f l2)
    | Cons (t1, a) ->
        (match l2 with
           Nil -> l1
         | Cons (t2, b) ->
             (match ltADec t1 t2 with
                Inleft s ->
                  (match s with
                     Left -> Cons (t1, (aux1 a (Cons (t2, b))))
                   | Right ->
                       let rec aux2 = function
                         Nil -> Cons (t1, a)
                       | Cons (t3, c) ->
                           (match ltADec t1 t3 with
                              Inleft s0 ->
                                (match s0 with
                                   Left -> Cons (t1,
                                     (aux1 a (Cons (t3, c))))
                                 | Right -> Cons ((f t3), (aux2 c)))
                            | Inright -> Cons (t1, (aux1 a c)))
                       in aux2 (Cons (t2, b)))
              | Inright -> Cons (t1, (aux1 a b))))
  in aux1

let fappendRz pol =
  fappendf rZltEDec (samePolRz pol)

let updateArray a b pol la lb ar =
  rArraySet
    (rArraySetList ar (samePolRz pol (RZPlus a))
      (appendRz (Cons ((RZPlus b), Nil)) lb)) a (Class
    (fappendRz pol la (appendRz (Cons ((RZPlus b), Nil)) lb)))

type bool =
    True
  | False

let rNatDec n m =
  (match compare n m EGAL with
     EGAL -> (fun _ _ _ -> Left)
   | INFERIEUR -> (fun _ _ _ -> Right)
   | SUPERIEUR -> (fun _ _ _ -> Right)) prop prop prop

let rZDec a b =
  match a with
    RZPlus r ->
      (match b with
         RZPlus a' -> (fun b' ->
           match rNatDec a' b' with
             Left -> Left
           | Right -> Right)
       | RZMinus r0 -> (fun r1 -> Right)) r
  | RZMinus r ->
      (match b with
         RZPlus r0 -> (fun r1 -> Right)
       | RZMinus a' -> (fun b' ->
           match rNatDec a' b' with
             Left -> Left
           | Right -> Right)) r

let addEqMem ar a b =
  letP (evalZ ar a) (fun a' ->
    letP (evalZ ar b) (fun b' ->
      match rZltEDec a' b' with
        Inleft rLt ->
          (match rLt with
             Left ->
               letP (getClassN ar (valRz a')) (fun la' ->
                 letP (getClassN ar (valRz b')) (fun lb' ->
                   mbDOp
                     (updateArray (valRz a') (valRz b')
                       (samePolRz a' b') la' lb' ar) False (Cons (a',
                     (Cons (b', lb'))))))
           | Right ->
               letP (getClassN ar (valRz a')) (fun la' ->
                 letP (getClassN ar (valRz b')) (fun lb' ->
                   mbDOp
                     (updateArray (valRz b') (valRz a')
                       (samePolRz b' a') lb' la' ar) False (Cons (b',
                     (Cons (a', la')))))))
      | Inright ->
          (match rZDec a' b' with
             Left -> mbDOp ar False Nil
           | Right -> mbDOp ar True Nil)))

type ('D, 'C, 'B, 'A) quatuor =
    Quatuor of 'A * 'B * 'C * 'D

type trace =
    EmptyTrace
  | TripletTrace of triplet
  | SeqTrace of trace * trace
  | DilemmaTrace of rZ * rZ * trace * trace

let addEqMem2 ar a b c d =
  match addEqMem ar a b with
    Triple (ar', b', l') ->
      (match b' with
         True -> mbDOp ar' b' l'
       | False ->
           (match addEqMem ar' c d with
              Triple (ar'', b'', l'') ->
                mbDOp ar'' b'' (appendRz l' l'')))

let zero =
  XH

let rZFalse =
  RZMinus zero

let rZTrue =
  RZPlus zero

let doTripletF ar = function
  Triplet (b, p, q, r) ->
    letP (evalZ ar p) (fun p' ->
      letP (evalZ ar q) (fun q' ->
        letP (evalZ ar r) (fun r' ->
          match b with
            RAnd ->
              (match rZDec p' (rZComp q') with
                 Left -> Some (addEqMem2 ar r' rZFalse q' rZTrue)
               | Right ->
                   (match rZDec p' (rZComp r') with
                      Left -> Some (addEqMem2 ar r' rZTrue q' rZFalse)
                    | Right ->
                        (match rZDec q' r' with
                           Left -> Some (addEqMem ar p' r')
                         | Right ->
                             (match rZDec q' (rZComp r') with
                                Left -> Some (addEqMem ar p' rZFalse)
                              | Right ->
                                  (match rZDec p' rZTrue with
                                     Left -> Some
                                       (addEqMem2 ar r' rZTrue q'
                                         rZTrue)
                                   | Right ->
                                       (match rZDec q' rZTrue with
                                          Left -> Some
                                            (addEqMem ar p' r')
                                        | Right ->
                                            (match rZDec q' rZFalse with
                                               Left -> Some
                                                 (addEqMem ar p'
                                                   rZFalse)
                                             | Right ->
                                                 (match rZDec r' rZTrue with
                                                    Left -> Some
                                                      (addEqMem ar p'
                                                        q')
                                                  | Right ->
                                                      (match rZDec r'
                                                              rZFalse with
                                                         Left -> Some
                                                           (addEqMem ar
                                                             p'
                                                             rZFalse)
                                                       | Right -> None)))))))))
          | REq ->
              (match rZDec p' q' with
                 Left -> Some (addEqMem ar r' rZTrue)
               | Right ->
                   (match rZDec p' (rZComp q') with
                      Left -> Some (addEqMem ar r' rZFalse)
                    | Right ->
                        (match rZDec p' r' with
                           Left -> Some (addEqMem ar q' rZTrue)
                         | Right ->
                             (match rZDec p' (rZComp r') with
                                Left -> Some (addEqMem ar q' rZFalse)
                              | Right ->
                                  (match rZDec q' r' with
                                     Left -> Some
                                       (addEqMem ar p' rZTrue)
                                   | Right ->
                                       (match rZDec q' (rZComp r') with
                                          Left -> Some
                                            (addEqMem ar p' rZFalse)
                                        | Right ->
                                            (match rZDec p' rZTrue with
                                               Left -> Some
                                                 (addEqMem ar q' r')
                                             | Right ->
                                                 (match rZDec p'
                                                          rZFalse with
                                                    Left -> Some
                                                      (addEqMem ar q'
                                                        (rZComp r'))
                                                  | Right ->
                                                      (match rZDec q'
                                                              rZTrue with
                                                         Left -> Some
                                                           (addEqMem ar
                                                             p' r')
                                                       | Right ->
                                                           (match 
                                                            rZDec q'
                                                              rZFalse with
                                                              Left ->
                                                              Some
                                                              (addEqMem
                                                              ar p'
                                                              (rZComp
                                                              r'))
                                                            | Right ->
                                                              (match 
                                                              rZDec r'
                                                              rZTrue with
                                                                
                                                              Left ->
                                                              Some
                                                              (addEqMem
                                                              ar p' q')
                                                              | 
                                                              Right ->
                                                              (match 
                                                              rZDec r'
                                                              rZFalse with
                                                                
                                                              Left ->
                                                              Some
                                                              (addEqMem
                                                              ar p'
                                                              (rZComp
                                                              q'))
                                                              | 
                                                              Right ->
                                                              None)))))))))))))))

let rec doTripletFs l ar =
  match l with
    Nil -> Quatuor (ar, False, Nil, EmptyTrace)
  | Cons (l1, a) ->
      (match doTripletF ar l1 with
         Some x ->
           (match x with
              Triple (l', b', ar') ->
                (match b' with
                   True ->
                     (match ar' with
                        Nil -> Quatuor (l', True, ar', (TripletTrace
                          l1))
                      | Cons (r, l0) -> Quatuor (l', True, ar',
                          (TripletTrace l1)))
                 | False ->
                     (match ar' with
                        Nil -> doTripletFs a l'
                      | Cons (r, l0) ->
                          (match doTripletFs a l' with
                             Quatuor (t'', l'', b'', ar'') -> Quatuor
                               (t'', l'', (appendRz ar' b''), (SeqTrace
                               ((TripletTrace l1), ar'')))))))
       | None -> doTripletFs a ar)

let appTrace t1 t2 =
  match t1 with
    EmptyTrace ->
      (match t2 with
         EmptyTrace -> t2
       | TripletTrace t -> t2
       | SeqTrace (t0, t) -> t2
       | DilemmaTrace (r0, r, t0, t) -> t2)
  | TripletTrace t ->
      (match t2 with
         EmptyTrace -> t1
       | TripletTrace t0 -> SeqTrace (t1, t2)
       | SeqTrace (t3, t0) -> SeqTrace (t1, t2)
       | DilemmaTrace (r0, r, t3, t0) -> SeqTrace (t1, t2))
  | SeqTrace (t0, t) ->
      (match t2 with
         EmptyTrace -> t1
       | TripletTrace t3 -> SeqTrace (t1, t2)
       | SeqTrace (t4, t3) -> SeqTrace (t1, t2)
       | DilemmaTrace (r0, r, t4, t3) -> SeqTrace (t1, t2))
  | DilemmaTrace (r0, r, t0, t) ->
      (match t2 with
         EmptyTrace -> t1
       | TripletTrace t3 -> SeqTrace (t1, t2)
       | SeqTrace (t4, t3) -> SeqTrace (t1, t2)
       | DilemmaTrace (r2, r1, t4, t3) -> SeqTrace (t1, t2))

let doTripletsR getT =
  let rec doTripletsR0 l ar =
    match l with
      Nil -> Quatuor (ar, False, Nil, EmptyTrace)
    | Cons (l1, a) ->
        (match doTripletFs (getT l1) ar with
           Quatuor (t', l', b', ar') ->
             (match l' with
                True -> Quatuor (t', True, b', ar')
              | False ->
                  (match doTripletsR0 a t' with
                     Quatuor (t'', l'', b'', ar'') -> Quatuor (t'',
                       l'', (appendRz b' b''), (appTrace ar' ar'')))))
  in doTripletsR0

let doTripletsN getT =
  let rec doTripletsN0 l n ar =
    match doTripletsR getT l ar with
      Quatuor (t', l', b', ar') ->
        (match l' with
           True -> Quatuor (t', True, b', ar')
         | False ->
             (match b' with
                Nil -> Quatuor (t', False, Nil, ar')
              | Cons (r, l0) ->
                  (match n with
                     O -> Quatuor (t', l', b', ar')
                   | S n0 ->
                       (match doTripletsN0 b' n0 t' with
                          Quatuor (t'', l'', b'', ar'') -> Quatuor
                            (t'', l'', (appendRz b' b''),
                            (appTrace ar' ar''))))))
  in doTripletsN0

let dT a b t1 t2 =
  match t1 with
    EmptyTrace ->
      (match t2 with
         EmptyTrace -> EmptyTrace
       | TripletTrace t -> DilemmaTrace (a, b, t1, t2)
       | SeqTrace (t0, t) -> DilemmaTrace (a, b, t1, t2)
       | DilemmaTrace (r0, r, t0, t) -> DilemmaTrace (a, b, t1, t2))
  | TripletTrace t -> DilemmaTrace (a, b, t1, t2)
  | SeqTrace (t0, t) -> DilemmaTrace (a, b, t1, t2)
  | DilemmaTrace (r0, r, t0, t) -> DilemmaTrace (a, b, t1, t2)

type ('B, 'A) prod =
    Pair of 'A * 'B

let getEquiv ar a =
  match rArrayGet ar a with
    Ref r ->
      (match r with
         RZPlus r0 ->
           (match rArrayGet ar r0 with
              Ref r1 -> Pair (Nil, True)
            | Class l -> Pair ((Cons ((RZPlus r0), l)), False))
       | RZMinus r0 ->
           (match rArrayGet ar r0 with
              Ref r1 -> Pair (Nil, True)
            | Class l -> Pair ((Cons ((RZPlus r0), l)), True)))
  | Class l -> Pair ((Cons ((RZPlus a), l)), False)

let getMin ltADec testDec =
  let rec aux1 l1 l2 =
    match l1 with
      Nil -> (match l2 with
                Nil -> None
              | Cons (a, l) -> None)
    | Cons (t1, a) ->
        (match l2 with
           Nil -> None
         | Cons (t2, b) ->
             (match ltADec t1 t2 with
                Inleft s ->
                  (match s with
                     Left -> aux1 a (Cons (t2, b))
                   | Right ->
                       let rec aux2 = function
                         Nil -> None
                       | Cons (t3, c) ->
                           (match ltADec t1 t3 with
                              Inleft s0 ->
                                (match s0 with
                                   Left -> aux1 a (Cons (t3, c))
                                 | Right -> aux2 c)
                            | Inright ->
                                (match testDec t1 t3 prop with
                                   Left -> Some t1
                                 | Right -> aux2 c))
                       in aux2 (Cons (t2, b)))
              | Inright ->
                  (match testDec t1 t2 prop with
                     Left -> Some t1
                   | Right -> aux1 a b)))
  in aux1

let getMinId =
  getMin rZltEDec (fun a b _ -> rZDec a b)

let getMinInv =
  getMin rZltEDec (fun a b _ -> rZDec a (rZComp b))

let getEquivMin ar1 ar2 a =
  match getEquiv ar1 a with
    Pair (l, l1) ->
      (match l1 with
         True ->
           (match getEquiv ar2 a with
              Pair (l0, l2) ->
                (match l2 with
                   True ->
                     (match getMinId l l0 with
                        Some b -> rZComp b
                      | None -> RZPlus zero)
                 | False ->
                     (match getMinInv l l0 with
                        Some b -> rZComp b
                      | None -> RZPlus zero)))
       | False ->
           (match getEquiv ar2 a with
              Pair (l0, l2) ->
                (match l2 with
                   True ->
                     (match getMinInv l l0 with
                        Some b -> b
                      | None -> RZPlus zero)
                 | False ->
                     (match getMinId l l0 with
                        Some b -> b
                      | None -> RZPlus zero))))

let rec addInterAux ar1 ar2 l ar3 =
  match l with
    Nil -> Pair (ar3, Nil)
  | Cons (l1, a) ->
      (match addInterAux ar1 ar2 a ar3 with
         Pair (l2, ar3') ->
           (match addEqMem l2 (RZPlus (valRz l1))
                    (getEquivMin ar1 ar2 (valRz l1)) with
              Triple (l2', b, ar3'') -> Pair (l2',
                (appendRz ar3' ar3''))))

let interf ltADec =
  let rec aux1 l1 l2 =
    match l1 with
      Nil -> (match l2 with
                Nil -> Nil
              | Cons (a, l) -> Nil)
    | Cons (t1, a) ->
        (match l2 with
           Nil -> Nil
         | Cons (t2, b) ->
             (match ltADec t1 t2 with
                Inleft s ->
                  (match s with
                     Left -> aux1 a (Cons (t2, b))
                   | Right ->
                       let rec aux2 = function
                         Nil -> Nil
                       | Cons (t3, c) ->
                           (match ltADec t1 t3 with
                              Inleft s0 ->
                                (match s0 with
                                   Left -> aux1 a (Cons (t3, c))
                                 | Right -> aux2 c)
                            | Inright -> Cons (t1, (aux1 a c)))
                       in aux2 (Cons (t2, b)))
              | Inright -> Cons (t1, (aux1 a b))))
  in aux1

let interMem ar1 ar2 ar3 l1 l2 =
  addInterAux ar1 ar2 (interf rZltEDec l1 l2) ar3

let dilemma1 f ar a b =
  match addEqMem ar a b with
    Triple (l1, b0, ar1) ->
      (match b0 with
         True -> Quatuor (ar, False, Nil, EmptyTrace)
       | False ->
           (match addEqMem ar a (rZComp b) with
              Triple (l2, b1, ar2) ->
                (match b1 with
                   True -> Quatuor (ar, False, Nil, EmptyTrace)
                 | False ->
                     (match f ar1 l1 with
                        Quatuor (t1', l1', l, ar1') ->
                          (match l1' with
                             True ->
                               (match f ar2 l2 with
                                  Quatuor (t2', l2', l0, ar2') ->
                                    (match l2' with
                                       True -> Quatuor (ar, True, Nil,
                                         (dT a b ar1' ar2'))
                                     | False -> Quatuor (t2', False,
                                         (appendRz ar2 l0),
                                         (dT a b ar1' ar2'))))
                           | False ->
                               (match f ar2 l2 with
                                  Quatuor (t2', l2', l0, ar2') ->
                                    (match l2' with
                                       True -> Quatuor (t1', False,
                                         (appendRz ar1 l),
                                         (dT a b ar1' ar2'))
                                     | False ->
                                         (match interMem t1' t2' ar
                                                  (appendRz ar1 l)
                                                  (appendRz ar2 l0) with
                                            Pair (l', ar') ->
                                              (match ar' with
                                                 Nil -> Quatuor (l',
                                                   False, Nil,
                                                   EmptyTrace)
                                               | Cons (r, l3) ->
                                                   Quatuor (l', False,
                                                   ar',
                                                   (dT a b ar1' ar2')))))))))))

let rec dilemma1R f v n ar =
  match rArrayGet ar v with
    Ref r ->
      (match n with
         O -> Quatuor (ar, False, Nil, EmptyTrace)
       | S m -> dilemma1R f (rnext v) m ar)
  | Class l ->
      (match dilemma1 f ar (RZPlus v) rZTrue with
         Quatuor (t1, l1, l0, ar1) ->
           (match l1 with
              True -> Quatuor (t1, True, l0, ar1)
            | False ->
                (match n with
                   O -> Quatuor (t1, False, l0, ar1)
                 | S m ->
                     (match dilemma1R f (rnext v) m t1 with
                        Quatuor (t2, l2, b, ar2) -> Quatuor (t2, l2,
                          (appendRz l0 b), (appTrace ar1 ar2))))))

let dilemma1RR n =
  let rec dilemma1RR0 f n1 ar =
    match dilemma1R f zero n ar with
      Quatuor (t1, l1, l, ar1) ->
        (match l1 with
           True -> Quatuor (t1, True, l, ar1)
         | False ->
             (match l with
                Nil -> Quatuor (t1, False, Nil, ar1)
              | Cons (r, l0) ->
                  (match n1 with
                     O -> Quatuor (t1, False, l, ar1)
                   | S m ->
                       (match dilemma1RR0 f m t1 with
                          Quatuor (t2, l2, b, ar2) -> Quatuor (t2, l2,
                            (appendRz l b), (appTrace ar1 ar2))))))
  in dilemma1RR0

let dilemma1RRL getT n0 f lt n ar =
  match doTripletsN getT lt n ar with
    Quatuor (t1, l1, l, ar1) ->
      (match l1 with
         True -> Quatuor (t1, True, l, ar1)
       | False ->
           (match dilemma1RR n0 f n t1 with
              Quatuor (t2, l2, b, ar2) -> Quatuor (t2, l2,
                (appendRz l b), (appTrace ar1 ar2))))

let dilemmaN getT n =
  let rec dilemmaN0 l m = function
    O -> doTripletsN getT l m
  | S n1 -> dilemma1RRL getT n (fun l0 -> dilemmaN0 l0 m n1) l m
  in dilemmaN0

let stalN getT n =
  let rec stalN0 l n1 m ar =
    match dilemmaN getT n l n n1 ar with
      Quatuor (t2, l2, l0, ar2) ->
        (match l2 with
           True -> Quatuor (t2, True, l0, ar2)
         | False ->
             (match m with
                O -> Quatuor (t2, False, l0, ar2)
              | S m1 ->
                  (match stalN0 Nil (S n1) m1 t2 with
                     Quatuor (t4, l4, b4, ar4) -> Quatuor (t4, l4,
                       (appendRz l0 b4), (appTrace ar2 ar4)))))
  in stalN0

let stal getT n m ar a b =
  match addEqMem ar a b with
    Triple (l1, b0, ar1) ->
      (match b0 with
         True -> Quatuor (ar, True, Nil, EmptyTrace)
       | False ->
           (match stalN getT n ar1 O m l1 with
              Quatuor (t2, l2, b2, ar2) -> Quatuor (t2, l2,
                (appendRz ar1 b2), ar2)))

let getT ar r =
  rArrayGet ar (valRz r)

let rArrayInit f =
  RArrayMake (REmpty, f)

let run m e =
  match makeTriplets (norm e) with
    TRC (n, r, l) ->
      letP (buildL n) (fun ar ->
        letP (convert (valRz r)) (fun n0 ->
          stal (getT ar) n0 m (rArrayInit (fun r0 -> Class Nil)) r
            rZFalse))



(*-------------------------------------------------------------------*)


(* the linking code *) 

open Pp
open Util
open Term
open Termops
open Names
open Reduction
open Tacmach
open Tacticals
open Proof_type
open Proof_trees
open Printer
open Equality
open Vernacinterp
open Libobject
open Closure
open Tacred
open Tactics
open Pattern 
open Hiddentac
open Constrintern

(*i*)

(* First, we need to access some Coq constants
  We do that lazily, because this code can be linked before
  the constants are loaded in the environment
*)

let constant dir s =
  let dir = make_dirpath (List.map id_of_string (List.rev ("Coq"::dir))) in
  let id = id_of_string s in
  try 
    global_reference_in_absolute_module dir id
  with Not_found ->
    anomaly ("cannot find "^
	     (Libnames.string_of_qualid (Libnames.make_qualid dir id)))

(* From logic *)

let llogic = ["Init";"Logic"];;
let coq_eq = lazy (constant llogic "eq");;
let coq_and = lazy (constant llogic "and");;
let coq_or = lazy (constant llogic "or");;
let coq_not = lazy (constant llogic "not");;
let coq_True = lazy (constant llogic "True");;
let coq_False = lazy (constant llogic "False");;
let coq_iff = lazy (constant llogic "iff");;
let coq_I = lazy (constant llogic "I");;

(* From fast_integer *)

let pos_constant =
  Coqlib.gen_constant_in_modules "Staltac" Coqlib.zarith_base_modules
let coq_xO = lazy (pos_constant "xO");;
let coq_xI = lazy (pos_constant "xI");;
let coq_xH = lazy (pos_constant "xH");;

let stal_constant dir s =
  let id = id_of_string s in
  try 
    global_reference_in_absolute_module 
      (make_dirpath (List.map id_of_string (List.rev ("Stalmarck":: dir)))) id
  with _ ->
  try 
    global_reference_in_absolute_module  
      (make_dirpath (List.map id_of_string (List.rev dir))) id
  with _ -> 
    anomaly ("cannot find "^
	     (Libnames.string_of_qualid 
                (Libnames.make_qualid 
                   (make_dirpath (List.map id_of_string (List.rev dir))) id)))

(* From rZ *)

let coq_zero = lazy (stal_constant ["rZ"] "zero");;
let coq_rnext = lazy (stal_constant ["rZ"] "rnext");;
let coq_rNat = lazy (stal_constant ["rZ"] "rNat");;
let coq_rZPlus = lazy (stal_constant ["rZ"] "rZPlus");;
let coq_rZMinus = lazy (stal_constant ["rZ"] "rZMinus");;
let coq_rZPlus = lazy (stal_constant ["rZ"] "rZPlus");;

(* From normalize *)

let coq_Expr = lazy (stal_constant ["normalize"] "Expr");;
let coq_Node = lazy (stal_constant ["normalize"] "Node");;
let coq_N = lazy (stal_constant ["normalize"] "N");;
let coq_V = lazy (stal_constant ["normalize"] "V");;
let coq_Tautology = lazy (stal_constant ["normalize"] "Tautology");;
let coq_ANd = lazy (stal_constant ["normalize"] "ANd");;
let coq_Or = lazy (stal_constant ["normalize"] "Or");;
let coq_Impl = lazy (stal_constant ["normalize"] "Impl");;
let coq_Eq = lazy (stal_constant ["normalize"] "Eq");;
let coq_rand = lazy (stal_constant ["normalize"] "rAnd");;
let coq_req  = lazy (stal_constant ["normalize"] "rEq");;

(* From triplet *)

let coq_Triplet = lazy (stal_constant ["triplet"] "Triplet");;

(* From trace *)

let coq_emptyTrace = lazy (stal_constant ["trace"] "emptyTrace");;
let coq_seqTrace = lazy (stal_constant ["trace"] "seqTrace");;
let coq_dilemmaTrace = lazy (stal_constant ["trace"] "dilemmaTrace");;
let coq_tripletTrace = lazy (stal_constant ["trace"] "tripletTrace");;
let coq_Trace = lazy (stal_constant ["trace"] "Trace");;
let coq_checkTrace = lazy (stal_constant ["algoTrace"] "checkTrace");;

(* From refl *)

let coq_rArrayInitP = lazy (stal_constant ["refl"] "rArrayInitP");;
let coq_rArrayGetP = lazy (stal_constant ["refl"] "rArrayGetP");;
let coq_rArraySetP = lazy (stal_constant ["refl"] "rArraySetP");;
let coq_ExprToPropTautology = lazy (stal_constant ["refl"] "ExprToPropTautology");;

(* Some exception *)
exception Not_a_boolOp
exception Not_an_Expr
exception Not_a_Pos
exception Not_a_Tautology


(* Turn a caml boolOp into a Coq object *)

let mkBool =  function
   ANd -> Lazy.force coq_ANd
|  Eq ->  Lazy.force coq_Eq
|  Or -> Lazy.force coq_Or
|  Impl ->  Lazy.force coq_Impl

(* Turn a caml rBoolOp into a Coq object *)

let mkRbool =  function
   RAnd -> Lazy.force coq_rand
|  REq ->  Lazy.force coq_req

(* Turn a caml rNat into a Coq object *)

let rec mkRnat =  function
   (XO r) -> mkApp ((Lazy.force coq_xO) ,[| mkRnat r |])
|  (XI r) -> mkApp ((Lazy.force coq_xI) ,[| mkRnat r |])
|  XH     -> Lazy.force coq_xH


(* Turn a caml rZ into a Coq object *)

let mkRz = function
  (RZPlus a) -> mkApp ((Lazy.force coq_rZPlus) ,[| mkRnat a |])
| (RZMinus a) -> mkApp ((Lazy.force coq_rZMinus) ,[| mkRnat a |])


(* Turn a caml Expr into a Coq object *)

let rec mkExpr = function 
    | Node (b,t1,t2) ->
        mkApp ((Lazy.force coq_Node)
          ,[| mkBool b; mkExpr t1; mkExpr t2 |])
    | N t ->
        mkApp ((Lazy.force coq_N)
          ,[| mkExpr t |])
    | V n ->
        mkApp ((Lazy.force coq_V)
          ,[| mkRnat n |])


(* Turn a caml triplet into a Coq object *)

let mkTriplet = function
  Triplet (b, p, q, r) -> 
    mkApp ((Lazy.force coq_Triplet) ,[| mkRbool b;mkRz p;mkRz q; mkRz r |])


(* Turn a caml tTrace into a Coq object *)

let rec mkTrace = function
    EmptyTrace -> Lazy.force coq_emptyTrace
  | TripletTrace t ->
    mkApp ((Lazy.force coq_tripletTrace) ,[| mkTriplet t |])
  | SeqTrace (tr1, tr2) ->
    mkApp ((Lazy.force coq_seqTrace) ,[| mkTrace tr1;mkTrace tr2 |])
  | DilemmaTrace (a,b,tr1,tr2) ->
    mkApp ((Lazy.force coq_dilemmaTrace) ,[|mkRz a; mkRz b; 
                                           mkTrace tr1;mkTrace tr2|])

let isDependent t = dependent (mkRel 1) t

(* The conclusion is a propostion, convertConcl returns a pair
      composed of the Expr representing the proposition and
      a hash function containing the interpretation of the variable
*)
let convertConcl cl =
  let varhash  = (Hashtbl.create 17 : (constr, positive) Hashtbl.t) in
  let index = ref zero in
  let rec inspect p =   match (kind_of_term p) with
(* And *)
    | App (c,[|t1; t2|]) when c=(Lazy.force coq_and) -> 
             (Node (ANd,(inspect t1),(inspect t2)))
(* Or *)
    | App (c,[|t1; t2|]) when c=(Lazy.force coq_or) -> 
             (Node (Or,(inspect t1),(inspect t2)))
(* Eq *)
    | App (c,[|t1; t2|]) when c=(Lazy.force coq_iff) -> 
             (Node (Eq, (inspect t1),(inspect t2)))
(* Impl *)
    | Prod (c,t1,t2) when c=Names.Anonymous -> 
             (Node (Impl,(inspect t1),(inspect t2)))
    | Prod (c,t1,t2) when not(dependent (mkRel 1) t2) ->
             (Node (Impl,(inspect t1),(inspect t2)))
(* Not *)
    | App (c,[|t|]) when c=(Lazy.force coq_not) ->
             (N (inspect t))
(* True is interpreted as V 0 *)
    | Ind _ when p=(Lazy.force coq_True) ->
             (V zero)
(* False is interpreted as ~(V 0) *)
    | Ind _ when p=(Lazy.force coq_False) ->
             (N (V zero))
(* Otherwise we generate a new variable if we 
   haven't already encounter this term *) 
    | a ->
       begin 
         try (V (Hashtbl.find varhash p))
         with Not_found -> 
           begin
             index := rnext !index;     
             Hashtbl.add varhash p !index;
             (V !index)
           end
       end in
      (inspect cl,varhash)

(* Convert the hashtable into a function array *)
let buildEnv hash =
  let acc = ref (mkApp ((Lazy.force coq_rArrayInitP)
                ,[| mkLambda (Names.Anonymous, (Lazy.force coq_rNat),
                   (Lazy.force coq_True)) |])) in
  Hashtbl.iter  (fun c n ->
              acc := (mkApp ((Lazy.force coq_rArraySetP) 
                ,[| !acc;mkRnat n; c |]))) hash;
  (mkApp ((Lazy.force coq_rArrayGetP)  ,[| !acc |]))



(* Pop Proposition *)

let pop_prop_run gl =
  let rec get_hyps shyp = match shyp with
      [] -> errorlabstrm "popProp" (str "No proposition to generalize");
    | (is,cst)::shyp' ->  
         match (kind_of_term  (pf_type_of gl cst)) with
           Sort(Prop _) -> is
         | _            -> get_hyps shyp'
  in
  let v = (get_hyps (pf_hyps_types gl)) in
    tclTHEN (generalize [mkVar v]) (clear [v]) gl

(* Main function *)

let stalt_run gl =
  let concl = pf_concl gl in
(* We get the expression and the hastable *)
  let (res,hash) = convertConcl concl in
(* we run stalmarck *)
  let  Quatuor (_, b, _, tr) = run (S (S O)) res in
  match b with 
   | True -> 
(* we have reached a contradiction *)
(* we first convert the trace *)
       let vv = mkTrace tr in
(* then Expr representing the Propositon *)
       let vres = mkExpr res in
(* then we make use of the theorem ExprToPropTautology to give the proof *)


       exact_check (mkApp ((Lazy.force coq_ExprToPropTautology)
               ,[| buildEnv hash;
                Lazy.force coq_I;
                vres;
                mkApp ((Lazy.force coq_checkTrace) ,
                   [| vres;vv |])
               |])) gl
   | False -> error "StalT can't conclude"

TACTIC EXTEND StalT
 [ "StalT" ] -> [ stalt_run ]
END

TACTIC EXTEND PopProp
 [ "PopProp" ] -> [ pop_prop_run ]
END

