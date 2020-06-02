(****************************************************************************

          Stalmarck  :  stalt

          Pierre Letouzey & Laurent Thery

****************************************************************************
Implementation of the Stalt tactic *)

(* The `Stalt' tactic inspired by the Ring tactic *)

open Stal
open Pp
open CErrors
open Util
open Constr
open EConstr
open Termops
open Names
open Tacmach
open Tactics

(*i*)

(* First, we need to access some Coq constants
  We do that lazily, because this code can be linked before
  the constants are loaded in the environment
*)

let global_reference_in_absolute_module dir id =
  Nametab.global_of_path (Libnames.make_path dir id)

let constant dir s =
  let dir = DirPath.make (List.map Id.of_string (List.rev ("Coq"::dir))) in
  let id = Id.of_string s in
  try
    EConstr.of_constr (UnivGen.constr_of_monomorphic_global (global_reference_in_absolute_module dir id))
  with Not_found ->
    anomaly (Pp.str ("cannot find "^
	     (Libnames.string_of_qualid (Libnames.make_qualid dir id))))

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

let binnums = ["Numbers";"BinNums"];;
let coq_xO = lazy (constant binnums "xO");;
let coq_xI = lazy (constant binnums "xI");;
let coq_xH = lazy (constant binnums "xH");;

let stal_constant dir s =
  let id = Id.of_string s in
  try
    EConstr.of_constr (UnivGen.constr_of_monomorphic_global (global_reference_in_absolute_module
      (DirPath.make (List.map Id.of_string (List.rev ("Stalmarck" :: "Algorithm" :: dir)))) id))
  with _ ->
  try
    EConstr.of_constr (UnivGen.constr_of_monomorphic_global (global_reference_in_absolute_module
      (DirPath.make (List.map Id.of_string (List.rev dir))) id))
  with _ ->
    anomaly (Pp.str ("cannot find "^
	     (Libnames.string_of_qualid
                (Libnames.make_qualid
                   (DirPath.make (List.map Id.of_string (List.rev dir))) id))))

(* From rZ *)

let coq_zero = lazy (stal_constant ["rZ"] "zero");;
let coq_rnext = lazy (stal_constant ["rZ"] "rnext");;
let coq_rNat = lazy (stal_constant ["rZ"] "rNat");;
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
|  Eq0 ->  Lazy.force coq_Eq
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

let isDependent sigma t = dependent sigma (mkRel 1) t

(* The conclusion is a propostion, convertConcl returns a pair
      composed of the Expr representing the proposition and
      a hash function containing the interpretation of the variable
*)

module ConstrMap = Map.Make(Constr)

let convertConcl sigma cl =
  let varhash  = ref ConstrMap.empty in
  let index = ref zero in
  let rec inspect p =   match kind sigma p with
(* And *)
    | App (c,[|t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_and) ->
             (Node (ANd,(inspect t1),(inspect t2)))
(* Or *)
    | App (c,[|t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_or) ->
             (Node (Or,(inspect t1),(inspect t2)))
(* Eq *)
    | App (c,[|t1; t2|]) when EConstr.eq_constr sigma c (Lazy.force coq_iff) ->
             (Node (Eq0, (inspect t1),(inspect t2)))
(* Impl *)
    | Prod (c,t1,t2) when Context.binder_name c == Names.Anonymous ->
             (Node (Impl,(inspect t1),(inspect t2)))
    | Prod (c,t1,t2) when not(dependent sigma (mkRel 1) t2) ->
             (Node (Impl,(inspect t1),(inspect t2)))
(* Not *)
    | App (c,[|t|]) when EConstr.eq_constr sigma c (Lazy.force coq_not) ->
             (N (inspect t))
(* True is interpreted as V 0 *)
    | Ind _ when EConstr.eq_constr sigma p (Lazy.force coq_True) ->
             (V zero)
(* False is interpreted as ~(V 0) *)
    | Ind _ when EConstr.eq_constr sigma p (Lazy.force coq_False) ->
             (N (V zero))
(* Otherwise we generate a new variable if we
   haven't already encounter this term *)
    | a ->
       begin
         let p = EConstr.to_constr sigma p in
         try (V (ConstrMap.find p !varhash))
         with Not_found ->
           begin
             index := rnext !index;
             varhash := ConstrMap.add p !index !varhash;
             (V !index)
           end
       end in
  let term = inspect cl in
    (term,!varhash)

(* Convert the hashtable into a function array *)
let buildEnv hash =
  let acc = ref (mkApp ((Lazy.force coq_rArrayInitP)
                ,[| mkLambda (Context.make_annot Names.Anonymous Sorts.Relevant, (Lazy.force coq_rNat),
                   (Lazy.force coq_True)) |])) in
  ConstrMap.iter  (fun c n ->
              acc := (mkApp ((Lazy.force coq_rArraySetP)
                ,[| !acc;mkRnat n; EConstr.of_constr c |]))) hash;
  (mkApp ((Lazy.force coq_rArrayGetP)  ,[| !acc |]))



(* Pop Proposition *)

let pop_prop_run gl =
  let rec get_hyps shyp = match shyp with
      [] -> user_err ~hdr:"popProp" (str "No proposition to generalize");
    | (is,cst)::shyp' ->
         let sigma = project gl in
         match kind sigma (pf_unsafe_type_of gl cst) with
           Sort s when (match ESorts.kind sigma s with Sorts.Prop -> true | _ -> false) -> is
         | _            -> get_hyps shyp'
  in
  let v = Context.binder_name (get_hyps (pf_hyps_types gl)) in
  Proofview.V82.of_tactic (Tacticals.New.tclTHEN (generalize [mkVar v]) (clear [v])) gl

(* Main function *)

let stalt_run gl =
  let concl = pf_concl gl in
(* We get the expression and the hastable *)
  let (res,hash) = convertConcl (project gl) concl in
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
       let term = 
	 (mkApp ((Lazy.force coq_ExprToPropTautology)
		,[| buildEnv hash;
                    Lazy.force coq_I;
                    vres;
                    mkApp ((Lazy.force coq_checkTrace) ,
			   [| vres;vv |])
		 |]))
       in
	 (Proofview.V82.of_tactic (exact_check term)) gl
   | False -> CErrors.user_err (str "StalT can't conclude")
