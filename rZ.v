
(****************************************************************************
                                                                           
          Stalmarck  : rZ                                                  
                                                                           
          Pierre Letouzey & Laurent Thery                                  
                                                                           
***************************************************************************
 We define signed variable as follows:
     We first define rNat as an abbreviation for positive (from fast_integer)
    and rZ as an inductive type with 2 constructors:
       rZPlus: rNat ->rZ
      rZMinus: rNat ->rZ .

    We define usual operations on rZ, i.e. equality, comparison etc

    At the end we define functional arrays that will be used in implementation
*)
Require Import sTactic.
Require Import Relation_Definitions.
Require Import ZArith.
Require Import Inverse_Image.
Require Import Inclusion.
Require Import Wf_nat.
Require Import List.

Definition rNat := positive.

Definition zero := 1%positive.

Definition rnext : rNat -> rNat := Psucc.
(* rZ are signed rNat *)

Inductive rZ : Set :=
  | rZPlus : rNat -> rZ
  | rZMinus : rNat -> rZ.

(* We single out zero as being intepreted as True *)

Definition rZTrue := rZPlus zero.

Definition rZFalse := rZMinus zero.

(* Complementary *)

Definition rZComp (r : rZ) : rZ :=
  match r with
  | rZPlus m => rZMinus m
  | rZMinus m => rZPlus m
  end.

Theorem rZCompInv : forall m : rZ, rZComp (rZComp m) = m.
intros m; case m; simpl in |- *; auto.
Qed.

(* Comparison function *)

Definition rlt (a b : rNat) : Prop :=
  (a ?= b)%positive Datatypes.Eq = Datatypes.Lt.
(* Decidability over rNat *)

Definition rNatDec : forall n m : rNat, {n = m} + {n <> m}.
intros n m; generalize (nat_of_P_lt_Lt_compare_morphism n m);
 generalize (nat_of_P_gt_Gt_compare_morphism n m);
 generalize (Pcompare_Eq_eq n m); case ((n ?= m)%positive Datatypes.Eq).
intros H' H'0 H'1; left; auto.
intros H' H'0 H'1; right; red in |- *; intros H1;
 absurd (nat_of_P n < nat_of_P m); auto.
rewrite <- H1; auto with arith.
intros H' H'0 H'1; right; red in |- *; intros H1;
 absurd (nat_of_P n > nat_of_P m); auto.
rewrite <- H1; auto with arith.
Defined.
(* Order is decidable *)

Definition rltDec : forall m n : rNat, {rlt m n} + {rlt n m \/ m = n}.
intros n m; generalize (nat_of_P_lt_Lt_compare_morphism n m);
 generalize (nat_of_P_gt_Gt_compare_morphism n m);
 generalize (Pcompare_Eq_eq n m); case ((n ?= m)%positive Datatypes.Eq).
intros H' H'0 H'1; right; right; auto.
intros H' H'0 H'1; left; unfold rlt in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
intros H' H'0 H'1; right; left; unfold rlt in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
apply H'0; auto.
Defined.
(* An alternative version *)

Definition rltEDec : forall m n : rNat, {rlt m n} + {rlt n m} + {m = n}.
intros n m; generalize (nat_of_P_lt_Lt_compare_morphism n m);
 generalize (nat_of_P_gt_Gt_compare_morphism n m);
 generalize (Pcompare_Eq_eq n m); case ((n ?= m)%positive Datatypes.Eq).
intros H' H'0 H'1; right; auto.
intros H' H'0 H'1; left; left; unfold rlt in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
intros H' H'0 H'1; left; right; unfold rlt in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism; auto.
apply H'0; auto.
Defined.
(* Some properties of rlt *)

Theorem rltDef2 : forall m n : rNat, rlt m n -> m <> n.
unfold rlt in |- *; intros m n H'; red in |- *; intros H'0;
 rewrite <- H'0 in H'; rewrite Pcompare_refl in H'; 
 discriminate.
Qed.

Theorem rltTrans : transitive rNat rlt.
red in |- *; unfold rlt in |- *; intros x y z H1 H2.
apply nat_of_P_lt_Lt_compare_complement_morphism.
apply lt_trans with (nat_of_P y); apply nat_of_P_lt_Lt_compare_morphism; auto.
Qed.

Theorem rltNotRefl : forall a : rNat, ~ rlt a a.
intros a; unfold rlt in |- *; rewrite Pcompare_refl; red in |- *; intros;
 discriminate.
Qed.
Hint Resolve rltNotRefl.

Theorem rnextRlt : forall m : rNat, rlt m (rnext m).
intros m; unfold rlt, rnext in |- *.
apply nat_of_P_lt_Lt_compare_complement_morphism.
rewrite Pplus_one_succ_r; rewrite nat_of_P_plus_morphism;
 unfold nat_of_P in |- *; simpl in |- *; rewrite plus_comm; 
 simpl in |- *; auto with arith.
Qed.
Hint Resolve rnextRlt.

Theorem rnextNotZero : forall m : rNat, rlt zero (rnext m).
intros m; unfold nat_of_P, rnext, rlt in |- *; elim m; simpl in |- *; auto.
Qed.
Hint Resolve rnextNotZero.
(* Maximun of two rNat *)

Definition rmax : rNat -> rNat -> rNat.
intros n m; case (rltDec n m); intros Rlt0.
exact m.
exact n.
Defined.

Lemma rmaxRlt : forall n m p : rNat, rlt m n -> rlt p n -> rlt (rmax m p) n.
intros n m p; unfold rmax in |- *; case (rltDec m p); auto.
Qed.

Lemma rmaxRltLeft : forall n m p : rNat, rlt (rmax m p) n -> rlt m n.
intros n m p; unfold rmax in |- *; case (rltDec m p); auto; intros Rlt0.
intros Rlt1; apply rltTrans with (y := p); auto.
Qed.

Lemma rmaxRltRight : forall n m p : rNat, rlt (rmax m p) n -> rlt p n.
intros n m p; unfold rmax in |- *; case (rltDec m p); auto; intros Rlt0.
Casec Rlt0; intros Rlt0; auto.
intros Rlt1; apply rltTrans with (y := m); auto.
rewrite <- Rlt0; auto.
Qed.
(* Properties of rnext *)

Lemma rNextS : forall n : rNat, nat_of_P (rnext n) = S (nat_of_P n).
intros n; unfold rnext, nat_of_P in |- *; simpl in |- *.
rewrite Pmult_nat_succ_morphism; auto.
Qed.

Theorem rNextInv : forall n m : rNat, rlt n (rnext m) -> n = m \/ rlt n m.
intros n m H'.
generalize (nat_of_P_lt_Lt_compare_morphism _ _ H').
rewrite rNextS.
intros H'0; case (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H'0)).
intros H'1; right; red in |- *;
 apply nat_of_P_lt_Lt_compare_complement_morphism; 
 auto.
intros H'1; left; apply nat_of_P_inj; auto.
Qed.

Lemma rltTransRnext1 :
 forall n m p : rNat, rlt n (rnext m) -> rlt m p -> rlt n p.
intros n m p H' H'0; case (rNextInv n m); auto.
intros H'1; rewrite H'1; auto.
intros H'1; apply rltTrans with (y := m); auto.
Qed.

Lemma rltTransRnext2 :
 forall n m p : rNat, rlt n m -> rlt m (rnext p) -> rlt n p.
intros n m p H' H'0; case (rNextInv m p); auto.
intros H'1; rewrite <- H'1; auto.
intros H'1; apply rltTrans with (y := m); auto.
Qed.

Lemma rltRnext2Inv : forall n m : rNat, rlt (rnext n) (rnext m) -> rlt n m.
intros n m H'; case (rNextInv (rnext n) m); auto.
intros H'0; rewrite <- H'0; auto.
intros H'1; apply rltTrans with (y := rnext n); auto.
Qed.

Lemma rnextMono : forall m n : rNat, rlt m n -> rlt (rnext m) (rnext n).
intros m n H'.
case (rltDec (rnext m) n); intros Rlt0; auto.
apply rltTrans with (y := n); auto.
case Rlt0; intros Rlt1.
elim (rNextInv n m); auto; intros Rlt2; absurd (rlt m m); auto.
rewrite Rlt2 in H'; auto.
apply rltTrans with (y := n); auto.
rewrite <- Rlt1; auto.
Qed.
Hint Resolve rnextMono.

Lemma rltRmaxLeft : forall n m : rNat, rlt n (rnext (rmax n m)).
intros n m; unfold rmax in |- *; case (rltDec n m); auto; intros Rlt0.
apply rltTrans with (y := m); auto.
Qed.

Lemma rltRmaxRight : forall n m : rNat, rlt m (rnext (rmax n m)).
intros n m; unfold rmax in |- *; case (rltDec n m); auto; intros Rlt0.
Casec Rlt0; intros Rlt0; auto.
apply rltTrans with (y := n); auto.
rewrite <- Rlt0; auto.
Qed.
Hint Resolve rltRmaxLeft rltRmaxRight.

Theorem rltAntiSym : forall a b : rNat, rlt a b -> ~ rlt b a.
intros a b H'; red in |- *; intros H'0; absurd (rlt a a); auto.
apply rltTrans with (y := b); auto.
Qed.
(* The equality on rZ is decidable *)

Definition rZDec : forall a b : rZ, {a = b} + {a <> b}.
intros a b; case a; case b;
 try (intros; right; red in |- *; intros; discriminate); 
 intros a' b'; case (rNatDec a' b'); intros Eq1;
 try (left; rewrite Eq1; auto; fail); auto; intros; 
 right; red in |- *; intros Eq2; apply Eq1; inversion Eq2; 
 auto.
Defined.

(*Absolute value*)

Definition valRz (a : rZ) :=
  match a with
  | rZPlus b => b
  | rZMinus b => b
  end.

(* Order on rZ *)

Definition rZlt (a b : rZ) := rlt (valRz a) (valRz b).

(* Equality on rZ, two elements sont eqRz if they have same rNat *)

Definition eqRz (a b : rZ) := valRz a = valRz b.
Hint Unfold eqRz rZlt.
(* Basic properties of eqRz and rZlt *)

Theorem eqrZRefl : reflexive rZ eqRz.
red in |- *; intros a; case a; simpl in |- *; auto.
Qed.
Hint Resolve eqrZRefl.

Theorem eqrZSym : symmetric rZ eqRz.
red in |- *; intros a b; case a; case b; simpl in |- *; auto.
Qed.
Hint Resolve eqrZSym.

Theorem eqrZTrans : transitive rZ eqRz.
red in |- *; auto.
unfold eqRz in |- *; intros x y z H'; rewrite H'; auto.
Qed.
Hint Resolve eqrZTrans.

Definition rZltDec : forall a b : rZ, {rZlt a b} + {rZlt b a \/ eqRz a b}.
intros a b; exact (rltDec (valRz a) (valRz b)).
Defined.

Definition rZltEDec : forall a b : rZ, {rZlt a b} + {rZlt b a} + {eqRz a b}.
intros a b; exact (rltEDec (valRz a) (valRz b)); auto.
Defined.

Theorem rZltEqComp :
 forall a b c d : rZ, rZlt a b -> eqRz a c -> eqRz b d -> rZlt c d.
intros a b c d; unfold rZlt, eqRz in |- *; case a; case b; case c; case d;
 simpl in |- *; intros a' b' c' d' H'0 H'1 H'2; try rewrite <- H'1;
 try rewrite <- H'2; auto.
Qed.

Theorem rZltDef2 : forall a b : rZ, rZlt a b -> ~ eqRz a b.
intros a b H; unfold eqRz in |- *; apply rltDef2; auto.
Qed.
Hint Resolve rZltDef2.

Theorem rZltTrans : transitive rZ rZlt.
red in |- *.
intros x y z H' H'0; red in |- *; apply rltTrans with (y := valRz y); auto.
Qed.
Hint Resolve rZltTrans.

Theorem rZltNotRefl : forall a : rZ, ~ rZlt a a.
intros a; unfold rZlt in |- *; auto.
Qed.
Hint Resolve rZltNotRefl.

Theorem rZltAntiSym : forall a b : rZ, rZlt a b -> ~ rZlt b a.
intros a b H'; red in |- *; intros H'0; absurd (rZlt a a); auto.
apply rZltTrans with (y := b); auto.
Qed.
Hint Resolve rZltAntiSym.

Theorem NotEqComp : forall a : rZ, a <> rZComp a.
intros a; case a; red in |- *; intros H'; discriminate.
Qed.
Hint Resolve NotEqComp.

Theorem eqRzComp : forall a : rZ, eqRz a (rZComp a).
intros a; case a; auto.
Qed.
Hint Resolve eqRzComp.

Theorem valRzComp : forall a : rZ, valRz (rZComp a) = valRz a.
intros a; case a; auto.
Qed.

Theorem rZCompInvol : forall a : rZ, a = rZComp (rZComp a).
intros a; case a; simpl in |- *; auto.
Qed.
Hint Resolve rZCompInvol.

Theorem rZCompEq : forall a b : rZ, rZComp a = rZComp b -> a = b.
intros a b; case a; case b; simpl in |- *; auto; intros a' b' H; inversion H;
 auto.
Qed.

(* Minimum of two rZ, if they are equal we choose arbitrary the second one *)

Definition min (a b : rZ) : rZ :=
  match rZltDec a b with
  | left _ => a
  | right _ => b
  end.

(* Maximum of two rZ, if they are equal we choose arbitrary the first one *)

Definition max (a b : rZ) : rZ :=
  match rZltDec a b with
  | left _ => b
  | right _ => a
  end.
(* Same basic properties of min and max *)

Theorem minProp1 : forall a b : rZ, rZlt a b -> min a b = a.
intros a b; unfold min in |- *; case (rZltDec a b); simpl in |- *; auto.
intros H'; case H'; intros H'0 H'1.
absurd (rZlt b a); auto.
absurd (eqRz a b); auto.
Qed.

Theorem minProp2 : forall a b : rZ, rZlt b a -> min a b = b.
intros a b; unfold min in |- *; case (rZltDec a b); simpl in |- *; auto.
intros H'0 H'1; absurd (rZlt b a); auto.
Qed.

Theorem minProp3 : forall a b : rZ, rZlt a b -> min b a = a.
intros a b; unfold min in |- *; case (rZltDec b a); simpl in |- *; auto.
intros H'0 H'1; absurd (rZlt b a); auto.
Qed.

Theorem minProp4 : forall a b : rZ, rZlt b a -> min b a = b.
intros a b; unfold min in |- *; case (rZltDec b a); simpl in |- *; auto.
intros H'; case H'; intros H'0 H'1.
absurd (rZlt b a); auto.
absurd (eqRz b a); auto.
Qed.

Theorem minProp5 : forall a b : rZ, eqRz a b -> min a b = b.
intros a b; unfold min in |- *; case (rZltDec a b); simpl in |- *; auto.
intros H'0 H'1; absurd (eqRz a b); auto.
Qed.

Theorem minProp6 : forall a b : rZ, eqRz a b -> min b a = a.
intros a b; unfold min in |- *; case (rZltDec b a); simpl in |- *; auto.
intros H' H'0; absurd (eqRz b a); auto.
Qed.

Theorem maxProp1 : forall a b : rZ, rZlt a b -> max a b = b.
intros a b; unfold max in |- *; case (rZltDec a b); simpl in |- *; auto.
intros H'; case H'; intros H'0 H'1.
absurd (rZlt b a); auto.
absurd (eqRz a b); auto.
Qed.

Theorem maxProp2 : forall a b : rZ, rZlt b a -> max a b = a.
intros a b; unfold max in |- *; case (rZltDec a b); simpl in |- *; auto.
intros H'0 H'1; absurd (rZlt b a); auto.
Qed.

Theorem maxProp3 : forall a b : rZ, rZlt a b -> max b a = b.
intros a b; unfold max in |- *; case (rZltDec b a); simpl in |- *; auto.
intros H'0 H'1; absurd (rZlt b a); auto.
Qed.

Theorem maxProp4 : forall a b : rZ, rZlt b a -> max b a = a.
intros a b; unfold max in |- *; case (rZltDec b a); simpl in |- *; auto.
intros H'; case H'; intros H'0 H'1.
absurd (rZlt b a); auto.
absurd (eqRz b a); auto.
Qed.

Theorem maxProp5 : forall a b : rZ, eqRz a b -> max a b = a.
intros a b; unfold max in |- *; case (rZltDec a b); simpl in |- *; auto.
intros H' H'0; absurd (eqRz a b); auto.
Qed.

Theorem maxProp6 : forall a b : rZ, eqRz a b -> max b a = b.
intros a b; unfold max in |- *; case (rZltDec b a); simpl in |- *; auto.
intros H' H'0; absurd (eqRz b a); auto.
Qed.
(* Check if two rZ are equal *)

Definition rZSignDec :
  forall a b : rZ, {a = b} + {a = rZComp b} + {~ eqRz a b}.
intros a b; case a; case b; intros a' b'; case (rNatDec a' b'); simpl in |- *;
 auto; intros Eqa'b'.
left; left; rewrite Eqa'b'; auto.
left; right; rewrite Eqa'b'; auto.
left; right; rewrite Eqa'b'; auto.
left; left; rewrite Eqa'b'; auto.
Defined.

(* Lift every function of rNat-> rZ to a function rZ -> rZ
   that is compatible with the complement *)

Definition liftRz (f : rNat -> rZ) (a : rZ) :=
  match a with
  | rZPlus a' => f a'
  | rZMinus a' => rZComp (f a')
  end.

(* Given a:rZ and b:rNat produces an rZ that has the same sign than
   a but the same rNat than b *)

Definition samePol (a : rZ) (b : rNat) := liftRz (fun a : rNat => rZPlus b) a.

(* Comparison between an rZ and an rNat *)

Definition rVlt (a : rZ) (b : rNat) := rlt (valRz a) b.
(* Comparison is compatible with the complement *)

Theorem rVltrZComp :
 forall (a : rZ) (b : rNat), rVlt a b -> rVlt (rZComp a) b.
intros a b; case a; simpl in |- *; auto.
Qed.
Hint Resolve rVltrZComp.

(* Given a:rZ and b:rZ produces an rZ that has the same sign than
   sign(a)*sign(b) but the same rNat than b *)

Definition samePolRz (a b : rZ) := liftRz (fun c : rNat => b) a.
(* Some properties of samePolRz *)

Theorem samePolRzValRz :
 forall (p : rZ) (q : rNat), valRz (samePolRz p (rZPlus q)) = q.
intros p; case p; simpl in |- *; auto.
Qed.

Theorem samePolRzEqRz : forall p q : rZ, eqRz (samePolRz p q) q.
intros p; case p; auto.
Qed.

Theorem samePolRzRvlt :
 forall (p q : rZ) (r : rNat), rVlt p r -> rVlt (samePolRz q p) r.
intros p q r; case q; auto.
Qed.

Theorem samePolRzInvRvlt :
 forall (p q : rZ) (r : rNat), rVlt (samePolRz q p) r -> rVlt p r.
intros p q r; case q; simpl in |- *; auto.
intros H' H'0; replace p with (rZComp (rZComp p)); auto.
Qed.

Theorem samePolRzsamePolRz : forall p q : rZ, samePolRz p (samePolRz p q) = q.
intros p; case p; auto.
Qed.

Theorem samePolSamePolRz :
 forall (p q : rZ) (r : rNat),
 samePol (samePolRz p q) r = samePolRz p (samePol q r).
intros p q; case p; case q; auto.
Qed.

Theorem samePolRzComp :
 forall p q : rZ, rZComp (samePolRz p q) = samePolRz p (rZComp q).
intros p q; case p; case q; simpl in |- *; auto.
Qed.

(*********************************************************************
                                                                    
 Definition of function arrays on an arbitrary Set A, using         
 positive numbers as indexes                                        
                                                                    
*********************************************************************)
Section rA.
Variable A : Set.
Require Import Option.
(* Usual binary tree *)

Inductive rTree : Set :=
  | rEmpty : rTree
  | rSplit : Option A -> rTree -> rTree -> rTree.
(* We use the positive number as a path in the tree to retrieve
   a value *)

Fixpoint rTreeGet (t : rTree) (r : rNat) {struct r} : 
 Option A :=
  match r, t with
  | _, rEmpty => None _
  | xH, rSplit a _ _ => a
  | xO p, rSplit _ t' _ => rTreeGet t' p
  | xI p, rSplit _ _ t' => rTreeGet t' p
  end.
(* To update a Tree we modify the branch designated by the number *)

Fixpoint rTreeSet (t : rTree) (r : rNat) {struct r} : 
 A -> rTree :=
  fun a : A =>
  match r, t with
  | xH, rEmpty => rSplit (Some _ a) rEmpty rEmpty
  | xO p, rEmpty => rSplit (None _) (rTreeSet rEmpty p a) rEmpty
  | xI p, rEmpty => rSplit (None _) rEmpty (rTreeSet rEmpty p a)
  | xH, rSplit _ t'1 t'2 => rSplit (Some _ a) t'1 t'2
  | xO p, rSplit b t'1 t'2 => rSplit b (rTreeSet t'1 p a) t'2
  | xI p, rSplit b t'1 t'2 => rSplit b t'1 (rTreeSet t'2 p a)
  end.
(* Standard properties for the Set and Get function *)

Theorem rTreeDef1 :
 forall (t : rTree) (m : rNat) (v : A),
 rTreeGet (rTreeSet t m v) m = Some _ v.
intros t m; generalize t; Elimc m; simpl in |- *; clear t.
intros p H' t v; case t; auto.
intros p H' t v; case t; auto.
intros t v; case t; auto.
Qed.

Theorem rTreeDef2 :
 forall (t : rTree) (m1 m2 : rNat) (v : A),
 m1 <> m2 -> rTreeGet (rTreeSet t m1 v) m2 = rTreeGet t m2.
intros t m; generalize t; Elimc m; simpl in |- *; clear t.
intros p H' t m2 v; case m2; simpl in |- *; case t; auto.
intros p0 H'0; rewrite H'; auto.
elim p0; simpl in |- *; auto.
Contradict H'0; rewrite H'0; auto.
intros a r1 r2 p0 H'0; rewrite H'; auto.
Contradict H'0; rewrite H'0; auto.
intros p0 H'0; elim p0; simpl in |- *; auto.
intros p H' t m2 v; case m2; simpl in |- *; case t; auto.
intros p0 H'0; elim p0; simpl in |- *; auto.
intros p0 H'0; rewrite H'; auto.
elim p0; simpl in |- *; auto.
Contradict H'0; rewrite H'0; auto.
intros a r1 r2 p0 H'0; rewrite H'; auto.
Contradict H'0; rewrite H'0; auto.
intros t m2 v; case m2; simpl in |- *; auto.
case t; intros p H'; elim p; simpl in |- *; auto.
case t; intros p H'; elim p; simpl in |- *; auto.
intros H'; Contradict H'; auto.
Qed.
(* We turn our rTree into a function array using a default function *)

Inductive rArray : Set :=
    rArrayMake : rTree -> (rNat -> A) -> rArray.

Definition rArrayGet (ar : rArray) (r : rNat) :=
  match ar with
  | rArrayMake t f => match rTreeGet t r with
                      | Some a => a
                      | _ => f r
                      end
  end.

Definition rArraySet (ar : rArray) (r : rNat) (v : A) :=
  match ar with
  | rArrayMake t f => rArrayMake (rTreeSet t r v) f
  end.
(* We get the standard properties *)

Theorem rArrayDef1 :
 forall (Ar : rArray) (m : rNat) (v : A), rArrayGet (rArraySet Ar m v) m = v.
intros Ar m v; case Ar; simpl in |- *.
intros r a; rewrite (rTreeDef1 r m v); auto.
Qed.

Theorem rArrayDef2 :
 forall (Ar : rArray) (m1 m2 : rNat) (v : A),
 m1 <> m2 -> rArrayGet (rArraySet Ar m1 v) m2 = rArrayGet Ar m2.
intros Ar m1 m2 v H'; case Ar; simpl in |- *.
intros r a; rewrite (rTreeDef2 r m1 m2 v); auto.
Qed.

(* Empty array with default value *)

Definition rArrayInit (f : rNat -> A) := rArrayMake rEmpty f.

Theorem rArrayDef :
 forall (m : rNat) (f : rNat -> A), rArrayGet (rArrayInit f) m = f m.
intros m f; simpl in |- *; auto.
elim m; simpl in |- *; auto.
Qed.
End rA.