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

(** * StalTac_ex
                                                           
Pierre Letouzey & Laurent Thery

Examples for the stalmarck tactic
*)

From Stalmarck Require Import StalTac.
From Coq Require Import Classical.

Theorem Praeclarum :
 forall x y z t : Prop, (x -> z) /\ (y -> t) -> x /\ y -> z /\ t.
Proof.
staltac.
Qed.

Theorem c2 : forall x y : Prop, x /\ y \/ x /\ ~ y \/ ~ x /\ y \/ ~ x /\ ~ y.
Proof.
staltac.
Qed.

Theorem puz002_1 :
 forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : Prop,
 ~
 ((~ v1 \/ v0) /\
  (~ v8 \/ v2) /\
  (~ v6 \/ v9) /\
  (~ v4 \/ v7) /\
  (~ v0 \/ v3) /\
  (~ v5 \/ v1) /\
  (~ v10 \/ ~ v2) /\
  (~ v3 \/ v4) /\ (v5 \/ v6) /\ (~ v7 \/ v8) /\ ~ v9 /\ v10).
Proof.
staltac.
Qed.

Theorem puz003_1 :
 forall
   v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
    v21 v22 v23 v24 v25 v26 v27 v28 v29 : Prop,
 ~
 ((~ v26 \/ ~ v0 \/ ~ v23 \/ v14) /\
  (~ v27 \/ ~ v0 \/ ~ v13 \/ v16) /\
  (~ v28 \/ ~ v0 \/ ~ v9 \/ v18) /\
  (~ v29 \/ ~ v0 \/ ~ v4 \/ v20) /\
  (~ v0 \/ ~ v0 \/ ~ v22 \/ v22) /\
  (~ v26 \/ ~ v29 \/ ~ v21 \/ v14) /\
  (~ v27 \/ ~ v29 \/ ~ v12 \/ v16) /\
  (~ v28 \/ ~ v29 \/ ~ v8 \/ v18) /\
  (~ v29 \/ ~ v29 \/ ~ v3 \/ v20) /\
  (~ v0 \/ ~ v29 \/ ~ v20 \/ v22) /\
  (~ v26 \/ ~ v28 \/ ~ v19 \/ v14) /\
  (~ v27 \/ ~ v28 \/ ~ v24 \/ v16) /\
  (~ v28 \/ ~ v28 \/ ~ v7 \/ v18) /\
  (~ v29 \/ ~ v28 \/ ~ v2 \/ v20) /\
  (~ v0 \/ ~ v28 \/ ~ v18 \/ v22) /\
  (~ v26 \/ ~ v27 \/ ~ v17 \/ v14) /\
  (~ v27 \/ ~ v27 \/ ~ v11 \/ v16) /\
  (~ v28 \/ ~ v27 \/ ~ v6 \/ v18) /\
  (~ v29 \/ ~ v27 \/ ~ v1 \/ v20) /\
  (~ v0 \/ ~ v27 \/ ~ v16 \/ v22) /\
  (~ v26 \/ ~ v26 \/ ~ v15 \/ v14) /\
  (~ v27 \/ ~ v26 \/ ~ v10 \/ v16) /\
  (~ v28 \/ ~ v26 \/ ~ v5 \/ v18) /\
  (~ v29 \/ ~ v26 \/ ~ v25 \/ v20) /\
  (~ v0 \/ ~ v26 \/ ~ v14 \/ v22) /\
  (~ v14 \/ ~ v0 \/ v14) /\
  (~ v16 \/ ~ v0 \/ v16) /\
  (~ v18 \/ ~ v0 \/ v18) /\
  (~ v20 \/ ~ v0 \/ v20) /\
  (~ v22 \/ ~ v0 \/ v22) /\
  (~ v14 \/ ~ v29 \/ v25) /\
  (~ v16 \/ ~ v29 \/ v1) /\
  (~ v18 \/ ~ v29 \/ v2) /\
  (~ v20 \/ ~ v29 \/ v3) /\
  (~ v22 \/ ~ v29 \/ v4) /\
  (~ v14 \/ ~ v28 \/ v5) /\
  (~ v16 \/ ~ v28 \/ v6) /\
  (~ v18 \/ ~ v28 \/ v7) /\
  (~ v20 \/ ~ v28 \/ v8) /\
  (~ v22 \/ ~ v28 \/ v9) /\
  (~ v14 \/ ~ v27 \/ v10) /\
  (~ v16 \/ ~ v27 \/ v11) /\
  (~ v18 \/ ~ v27 \/ v24) /\
  (~ v20 \/ ~ v27 \/ v12) /\
  (~ v22 \/ ~ v27 \/ v13) /\
  (~ v14 \/ ~ v26 \/ v15) /\
  (~ v16 \/ ~ v26 \/ v17) /\
  (~ v18 \/ ~ v26 \/ v19) /\
  (~ v20 \/ ~ v26 \/ v21) /\
  (~ v22 \/ ~ v26 \/ v23) /\ ~ v24 /\ v25 /\ v26 /\ v27 /\ v28 /\ v29).
Proof.
staltac.
Qed.

Theorem dubois20:
  forall v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60:Prop,
  ~ (
      (v39 \/ v40 \/ v1) /\
      (~ v39 \/ ~ v40 \/ v1) /\
      (v39 \/ ~ v40 \/ ~ v1) /\
      (~ v39 \/ v40 \/ ~ v1) /\
      (v1 \/ v41 \/ v2) /\
      (~ v1 \/ ~ v41 \/ v2) /\
      (v1 \/ ~ v41 \/ ~ v2) /\
      (~ v1 \/ v41 \/ ~ v2) /\
      (v2 \/ v42 \/ v3) /\
      (~ v2 \/ ~ v42 \/ v3) /\
      (v2 \/ ~ v42 \/ ~ v3) /\
      (~ v2 \/ v42 \/ ~ v3) /\
      (v3 \/ v43 \/ v4) /\
      (~ v3 \/ ~ v43 \/ v4) /\
      (v3 \/ ~ v43 \/ ~ v4) /\
      (~ v3 \/ v43 \/ ~ v4) /\
      (v4 \/ v44 \/ v5) /\
      (~ v4 \/ ~ v44 \/ v5) /\
      (v4 \/ ~ v44 \/ ~ v5) /\
      (~ v4 \/ v44 \/ ~ v5) /\
      (v5 \/ v45 \/ v6) /\
      (~ v5 \/ ~ v45 \/ v6) /\
      (v5 \/ ~ v45 \/ ~ v6) /\
      (~ v5 \/ v45 \/ ~ v6) /\
      (v6 \/ v46 \/ v7) /\
      (~ v6 \/ ~ v46 \/ v7) /\
      (v6 \/ ~ v46 \/ ~ v7) /\
      (~ v6 \/ v46 \/ ~ v7) /\
      (v7 \/ v47 \/ v8) /\
      (~ v7 \/ ~ v47 \/ v8) /\
      (v7 \/ ~ v47 \/ ~ v8) /\
      (~ v7 \/ v47 \/ ~ v8) /\
      (v8 \/ v48 \/ v9) /\
      (~ v8 \/ ~ v48 \/ v9) /\
      (v8 \/ ~ v48 \/ ~ v9) /\
      (~ v8 \/ v48 \/ ~ v9) /\
      (v9 \/ v49 \/ v10) /\
      (~ v9 \/ ~ v49 \/ v10) /\
      (v9 \/ ~ v49 \/ ~ v10) /\
      (~ v9 \/ v49 \/ ~ v10) /\
      (v10 \/ v50 \/ v11) /\
      (~ v10 \/ ~ v50 \/ v11) /\
      (v10 \/ ~ v50 \/ ~ v11) /\
      (~ v10 \/ v50 \/ ~ v11) /\
      (v11 \/ v51 \/ v12) /\
      (~ v11 \/ ~ v51 \/ v12) /\
      (v11 \/ ~ v51 \/ ~ v12) /\
      (~ v11 \/ v51 \/ ~ v12) /\
      (v12 \/ v52 \/ v13) /\
      (~ v12 \/ ~ v52 \/ v13) /\
      (v12 \/ ~ v52 \/ ~ v13) /\
      (~ v12 \/ v52 \/ ~ v13) /\
      (v13 \/ v53 \/ v14) /\
      (~ v13 \/~ v53 \/ v14) /\
      (v13 \/ ~ v53 \/ ~ v14) /\
      (~ v13 \/ v53 \/ ~ v14) /\
      (v14 \/ v54 \/ v15) /\
      (~ v14 \/ ~ v54 \/ v15) /\
      (v14 \/ ~ v54 \/ ~ v15) /\
      (~ v14 \/ v54 \/ ~ v15) /\
      (v15 \/ v55 \/ v16) /\
      (~ v15 \/ ~ v55 \/ v16) /\
      (v15 \/ ~ v55 \/ ~ v16) /\
      (~ v15 \/ v55 \/ ~ v16) /\
      (v16 \/ v56 \/ v17) /\
      (~ v16 \/ ~ v56 \/ v17) /\
      (v16 \/ ~ v56 \/ ~ v17) /\
      (~ v16 \/ v56 \/ ~ v17) /\
      (v17 \/ v57 \/ v18) /\
      (~ v17 \/ ~ v57 \/ v18) /\
      (v17 \/ ~ v57 \/ ~ v18) /\
      (~ v17 \/ v57 \/ ~ v18) /\
      (v18 \/ v58 \/ v19) /\
      (~ v18 \/ ~ v58 \/ v19) /\
      (v18 \/ ~ v58 \/ ~ v19) /\
      (~ v18 \/ v58 \/ ~ v19) /\
      (v19 \/ v59 \/ v60) /\
      (~ v19 \/ ~ v59 \/ v60) /\
      (v19 \/ ~ v59 \/ ~ v60) /\
      (~ v19 \/ v59 \/ ~ v60) /\
      (v20 \/ v59 \/ v60) /\
      (~ v20 \/ ~ v59 \/ v60) /\
      (v20 \/ ~ v59 \/ ~ v60) /\
      (~ v20 \/ v59 \/ ~ v60) /\
      (v21 \/ v58 \/ v20) /\
      (~ v21 \/ ~ v58 \/ v20) /\
      (v21 \/ ~ v58 \/ ~ v20) /\
      (~ v21 \/ v58 \/ ~ v20) /\
      (v22 \/ v57 \/ v21) /\
      (~ v22 \/ ~ v57 \/ v21) /\
      (v22 \/ ~ v57 \/ ~ v21) /\
      (~ v22 \/ v57 \/ ~ v21) /\
      (v23 \/ v56\/v22) /\
      (~ v23\/~ v56 \/ v22) /\
      (v23 \/ ~ v56 \/ ~ v22)/\
      (~ v23 \/ v56 \/ ~ v22) /\
      (v24 \/ v55 \/ v23) /\
      (~ v24 \/ ~ v55 \/ v23) /\
      (v24 \/ ~ v55 \/ ~ v23) /\
      (~ v24 \/ v55 \/ ~ v23) /\
      (v25 \/ v54 \/ v24) /\
      (~ v25 \/ ~ v54 \/ v24) /\
      (v25 \/ ~ v54 \/ ~ v24) /\
      (~ v25 \/ v54 \/ ~ v24) /\
      (v26 \/ v53 \/ v25) /\
      (~ v26 \/ ~ v53 \/ v25) /\
      (v26 \/ ~ v53 \/ ~ v25) /\
      (~ v26 \/ v53 \/ ~ v25) /\
      (v27 \/ v52 \/ v26) /\
      (~ v27 \/ ~ v52 \/ v26) /\
      (v27 \/ ~ v52 \/ ~ v26) /\
      (~ v27 \/ v52 \/ ~ v26) /\
      (v28 \/ v51 \/ v27) /\
      (~ v28 \/ ~ v51 \/ v27) /\
      (v28 \/ ~ v51 \/ ~ v27) /\
      (~ v28 \/ v51 \/ ~ v27) /\
      (v29 \/ v50 \/ v28) /\
      (~ v29 \/ ~ v50 \/ v28) /\
      (v29 \/ ~ v50 \/ ~ v28) /\
      (~ v29 \/ v50 \/ ~ v28) /\
      (v30 \/ v49 \/ v29) /\
      (~ v30 \/ ~ v49 \/ v29) /\
      (v30 \/ ~ v49 \/ ~ v29) /\
      (~ v30 \/ v49 \/ ~ v29) /\
      (v31 \/ v48 \/ v30) /\
      (~ v31 \/ ~ v48\/v30) /\
      (v31\/~ v48 \/ ~ v30) /\
      (~ v31 \/ v48 \/ ~ v30)/\
      (v32 \/ v47 \/ v31) /\
      (~ v32 \/ ~ v47 \/ v31) /\
      (v32 \/ ~ v47 \/ ~ v31) /\
      (~ v32 \/ v47 \/ ~ v31) /\
      (v33 \/ v46 \/ v32) /\
      (~ v33 \/ ~ v46 \/ v32) /\
      (v33 \/ ~ v46 \/ ~ v32) /\
      (~ v33 \/ v46 \/ ~ v32) /\
      (v34 \/ v45 \/ v33) /\
      (~ v34 \/ ~ v45 \/ v33) /\
      (v34 \/ ~ v45 \/ ~ v33) /\
      (~ v34 \/ v45 \/ ~ v33) /\
      (v35 \/ v44 \/ v34) /\
      (~ v35 \/ ~ v44 \/ v34) /\
      (v35 \/ ~ v44 \/ ~ v34) /\
      (~ v35 \/ v44 \/ ~ v34) /\
      (v36 \/ v43 \/ v35) /\
      (~ v36 \/ ~ v43 \/ v35) /\
      (v36 \/ ~ v43 \/ ~ v35) /\
      (~ v36 \/ v43 \/ ~ v35) /\
      (v37 \/ v42 \/ v36) /\
      (~ v37 \/ ~ v42 \/ v36) /\
      (v37 \/ ~ v42 \/ ~ v36) /\
      (~ v37 \/ v42 \/ ~ v36) /\
      (v38 \/ v41 \/ v37) /\
      (~ v38 \/ ~ v41 \/ v37) /\
      (v38 \/ ~ v41 \/ ~ v37) /\
      (~ v38 \/ v41 \/ ~ v37) /\
      (v39 \/ v40 \/ ~ v38) /\
      (~ v39 \/ ~ v40 \/ ~ v38) /\
      (v39 \/ ~ v40 \/ v38) /\
       (~ v39 \/ v40 \/ v38)).
Proof.
staltac.
Qed.
