(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Ring.
Import Ring_polynom Ring_tac Ring_theory InitialRing Setoid List Morphisms.
Require Import ZArith_base.
(*Require Import Omega.*)
Set Implicit Arguments.

Section MakeFieldPol.

(* Field elements *)
 Variable R:Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R->R).
 Variable (rdiv : R -> R ->  R) (rinv : R ->  R).
 Variable req : R -> R -> Prop.

 Notation "0" := rO. Notation "1" := rI.
 Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
 Notation "x - y " := (rsub x y). Notation "x / y" := (rdiv x y).
 Notation "- x" := (ropp x). Notation "/ x" := (rinv x).
 Notation "x == y" := (req x y) (at level 70, no associativity).

 (* Equality properties *)
 Variable Rsth : Equivalence req.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
 Variable SRinv_ext : forall p q, p == q ->  / p == / q.

 (* Field properties *)
  Record almost_field_theory : Prop := mk_afield {
    AF_AR : almost_ring_theory rO rI radd rmul rsub ropp req;
    AF_1_neq_0 : ~ 1 == 0;
    AFdiv_def : forall p q, p / q == p * / q;
    AFinv_l : forall p, ~ p == 0 ->  / p * p == 1
  }.

Section AlmostField.

 Variable AFth : almost_field_theory.
 Let ARth := AFth.(AF_AR).
 Let rI_neq_rO := AFth.(AF_1_neq_0).
 Let rdiv_def := AFth.(AFdiv_def).
 Let rinv_l := AFth.(AFinv_l).

 (* Coefficients *)
 Variable C: Type.
 Variable (cO cI: C) (cadd cmul csub : C->C->C) (copp : C->C).
 Variable ceqb : C->C->bool.
 Variable phi : C -> R.

 Variable CRmorph : ring_morph rO rI radd rmul rsub ropp req
                               cO cI cadd cmul csub copp ceqb phi.

Lemma ceqb_rect : forall c1 c2 (A:Type) (x y:A) (P:A->Type),
  (phi c1 == phi c2 -> P x) -> P y -> P (if ceqb c1 c2 then x else y).
Proof.
intros.
generalize (fun h => X (morph_eq CRmorph c1 c2 h)).
case (ceqb c1 c2); auto.
Qed.


 (* C notations *)
 Notation "x +! y" := (cadd x y) (at level 50).
 Notation "x *! y " := (cmul x y) (at level 40).
 Notation "x -! y " := (csub x y) (at level 50).
 Notation "-! x" := (copp x) (at level 35).
 Notation " x ?=! y" := (ceqb x y) (at level 70, no associativity).
 Notation "[ x ]" := (phi x) (at level 0).


 (* Useful tactics *)
  Add Morphism radd : radd_ext.  exact (Radd_ext Reqe). Qed.
  Add Morphism rmul : rmul_ext.  exact (Rmul_ext Reqe). Qed.
  Add Morphism ropp : ropp_ext.  exact (Ropp_ext Reqe). Qed.
  Add Morphism rsub : rsub_ext. exact (ARsub_ext Rsth Reqe ARth). Qed.
  Add Morphism rinv : rinv_ext. exact SRinv_ext. Qed.

Let eq_trans := Setoid.Seq_trans _ _ Rsth.
Let eq_sym := Setoid.Seq_sym _ _ Rsth.
Let eq_refl := Setoid.Seq_refl _ _ Rsth.
Let mor1h := CRmorph.(morph1).

Hint Resolve eq_refl rdiv_def rinv_l rI_neq_rO .

Let lem1 := Rmul_ext Reqe.
Let lem2 := Rmul_ext Reqe.
Let lem3 := (Radd_ext Reqe).
Let lem4 := ARsub_ext Rsth Reqe ARth.
Let lem5 := Ropp_ext Reqe.
Let lem6 := ARadd_0_l  ARth.
Let lem7 := ARadd_comm  ARth.
Let lem8 := (ARadd_assoc ARth).
Let lem9 := ARmul_1_l  ARth.
Let lem10 := (ARmul_0_l  ARth).
Let lem11 := ARmul_comm  ARth.
Let lem12 := ARmul_assoc ARth.
Let lem13 := (ARdistr_l  ARth).
Let lem14 := ARopp_mul_l ARth.
Let lem15 := (ARopp_add  ARth).
Let lem16 := ARsub_def  ARth.

Hint Resolve lem1 lem2 lem3 lem4 lem5 lem6 lem7 lem8 lem9 lem10
     lem11 lem12 lem13 lem14 lem15 lem16 SRinv_ext.

 (* Power coefficients *)
 Variable Cpow : Type.
 Variable Cp_phi : N -> Cpow.
 Variable rpow : R -> Cpow -> R.
 Variable pow_th : power_theory rI rmul req Cp_phi rpow.
 (* sign function *)
 Variable get_sign : C -> option C.
 Variable get_sign_spec : sign_theory copp ceqb get_sign.

 Variable cdiv:C -> C -> C*C.
 Variable cdiv_th : div_theory req cadd cmul phi cdiv.

Notation NPEeval := (PEeval rO radd rmul rsub ropp phi Cp_phi rpow).
Notation Nnorm:= (norm_subst cO cI cadd cmul csub copp ceqb cdiv).

Notation NPphi_dev := (Pphi_dev rO rI radd rmul rsub ropp cO cI ceqb phi get_sign).
Notation NPphi_pow := (Pphi_pow rO rI radd rmul rsub ropp cO cI ceqb phi Cp_phi rpow get_sign).

(* add abstract semi-ring to help with some proofs *)
Add Ring Rring : (ARth_SRth ARth).

Local Hint Extern 2 (_ == _) => f_equiv.

(* additional ring properties *)

Lemma rsub_0_l : forall r, 0 - r == - r.
intros; rewrite (ARsub_def ARth);ring.
Qed.

Lemma rsub_0_r : forall r, r - 0 == r.
intros; rewrite (ARsub_def ARth).
rewrite (ARopp_zero Rsth Reqe ARth);  ring.
Qed.

(***************************************************************************

                       Properties of division

  ***************************************************************************)

Theorem rdiv_simpl: forall p q, ~ q == 0 ->  q * (p / q) == p.
Proof.
intros p q H.
rewrite rdiv_def.
transitivity (/ q * q * p); [  ring | idtac ].
rewrite rinv_l; auto.
Qed.
Hint Resolve rdiv_simpl .

Instance SRdiv_ext: Proper (req ==> req ==> req) rdiv.
Proof.
intros p1 p2 Ep q1 q2 Eq.
transitivity (p1 * / q1); auto.
transitivity (p2 * / q2); auto.
Qed.
Hint Resolve SRdiv_ext.

Lemma rmul_reg_l : forall p q1 q2,
  ~ p == 0 -> p * q1 == p * q2 -> q1 == q2.
Proof.
intros p q1 q2 H EQ.
rewrite <- (@rdiv_simpl q1 p) by trivial.
rewrite <- (@rdiv_simpl q2 p) by trivial.
rewrite !rdiv_def, !(ARmul_assoc ARth).
now rewrite EQ.
Qed.

Theorem field_is_integral_domain : forall r1 r2,
  ~ r1 == 0 -> ~ r2 == 0 -> ~ r1 * r2 == 0.
Proof.
intros r1 r2 H1 H2. contradict H2.
transitivity (1 * r2); auto.
transitivity (/ r1 * r1 * r2); auto.
rewrite <- (ARmul_assoc ARth).
rewrite H2.
apply ARmul_0_r with (1 := Rsth) (2 := ARth).
Qed.

Theorem ropp_neq_0 : forall r,
  ~ -(1) == 0 -> ~ r == 0 -> ~ -r == 0.
intros.
setoid_replace (- r) with (- (1) * r).
 apply field_is_integral_domain; trivial.
 rewrite <- (ARopp_mul_l ARth).
   rewrite (ARmul_1_l ARth).
   reflexivity.
Qed.

Theorem rdiv_r_r : forall r, ~ r == 0 -> r / r == 1.
intros.
rewrite (AFdiv_def AFth).
rewrite (ARmul_comm ARth).
apply (AFinv_l AFth).
trivial.
Qed.

Theorem rdiv1: forall r,  r == r / 1.
intros r; transitivity (1 * (r / 1)); auto.
Qed.

Theorem rdiv2:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r4 == 0 ->
 r1 / r2 + r3 / r4 == (r1 * r4 + r3 * r2) / (r2 * r4).
Proof.
intros r1 r2 r3 r4 H H0.
assert (~ r2 * r4 == 0) by (apply field_is_integral_domain; trivial).
apply rmul_reg_l with (r2 * r4); trivial.
rewrite rdiv_simpl; trivial.
rewrite (ARdistr_r Rsth Reqe ARth).
apply (Radd_ext Reqe).
- transitivity (r2 * (r1 / r2) * r4); [  ring | auto ].
- transitivity (r2 * (r4 * (r3 / r4))); auto.
  transitivity (r2 * r3); auto.
Qed.


Theorem rdiv2b:
 forall r1 r2 r3 r4 r5,
 ~ (r2*r5) == 0 ->
 ~ (r4*r5) == 0 ->
 r1 / (r2*r5) + r3 / (r4*r5) == (r1 * r4 + r3 * r2) / (r2 * (r4 * r5)).
Proof.
intros r1 r2 r3 r4 r5 H H0.
assert (HH1: ~ r2 == 0) by (intros HH; case H; rewrite HH; ring).
assert (HH2: ~ r5 == 0) by (intros HH; case H; rewrite HH; ring).
assert (HH3: ~ r4 == 0) by (intros HH; case H0; rewrite HH; ring).
assert (HH4: ~ r2 * (r4 * r5) == 0)
   by (repeat apply field_is_integral_domain; trivial).
apply rmul_reg_l with (r2 * (r4 * r5)); trivial.
rewrite rdiv_simpl; trivial.
rewrite (ARdistr_r Rsth Reqe ARth).
apply (Radd_ext Reqe).
 transitivity ((r2 * r5) * (r1 / (r2 * r5)) * r4); [  ring | auto ].
 transitivity ((r4 * r5) * (r3 / (r4 * r5)) * r2); [  ring | auto ].
Qed.

Theorem rdiv5: forall r1 r2,  - (r1 / r2) == - r1 / r2.
Proof.
intros r1 r2.
transitivity (- (r1 * / r2)); auto.
transitivity (- r1 * / r2); auto.
Qed.
Hint Resolve rdiv5 .

Theorem rdiv3 r1 r2 r3 r4 :
 ~ r2 == 0 ->
 ~ r4 == 0 ->
 r1 / r2 - r3 / r4 == (r1 * r4 -  r3 * r2) / (r2 * r4).
Proof.
intros H2 H4.
assert (~ r2 * r4 == 0) by (apply field_is_integral_domain; trivial).
transitivity (r1 / r2 + - (r3 / r4)); auto.
transitivity (r1 / r2 + - r3 / r4); auto.
transitivity ((r1 * r4 + - r3 * r2) / (r2 * r4)).
apply rdiv2; auto.
f_equiv.
transitivity (r1 * r4 + - (r3 * r2)); auto.
Qed.


Theorem rdiv3b:
 forall r1 r2 r3 r4 r5,
 ~ (r2 * r5) == 0 ->
 ~ (r4 * r5) == 0 ->
 r1 / (r2*r5) - r3 / (r4*r5) == (r1 * r4 - r3 * r2) / (r2 * (r4 * r5)).
Proof.
intros r1 r2 r3 r4 r5 H H0.
transitivity (r1 / (r2 * r5) + - (r3 / (r4 * r5))); auto.
transitivity (r1 / (r2 * r5) + - r3 / (r4 * r5)); auto.
transitivity ((r1 * r4 + - r3 * r2) / (r2 * (r4 * r5))).
apply rdiv2b; auto; try ring.
apply (SRdiv_ext); auto.
transitivity (r1 * r4 + - (r3 * r2)); symmetry; auto.
Qed.

Theorem rdiv6:
 forall r1 r2,
 ~ r1 == 0 -> ~ r2 == 0 ->  / (r1 / r2) == r2 / r1.
intros r1 r2 H H0.
assert (~ r1 / r2 == 0) as Hk.
 intros H1; case H.
   transitivity (r2 * (r1 / r2)); auto.
   rewrite H1;  ring.
 apply rmul_reg_l with (r1 / r2); auto.
   transitivity (/ (r1 / r2) * (r1 / r2)); auto.
   transitivity 1; auto.
   repeat rewrite rdiv_def.
   transitivity (/ r1 * r1 * (/ r2 * r2)); [ idtac |  ring ].
   repeat rewrite rinv_l; auto.
Qed.
Hint Resolve rdiv6 .

 Theorem rdiv4:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r4 == 0 ->
 (r1 / r2) * (r3 / r4) == (r1 * r3) / (r2 * r4).
Proof.
intros r1 r2 r3 r4 H H0.
assert (~ r2 * r4 == 0) by (apply field_is_integral_domain; trivial).
apply rmul_reg_l with (r2 * r4); trivial.
rewrite rdiv_simpl; trivial.
transitivity (r2 * (r1 / r2) * (r4 * (r3 / r4))); [  ring | idtac ].
repeat rewrite rdiv_simpl; trivial.
Qed.

 Theorem rdiv4b:
 forall r1 r2 r3 r4 r5 r6,
 ~ r2 * r5 == 0 ->
 ~ r4 * r6 == 0 ->
 ((r1 * r6) / (r2 * r5)) * ((r3 * r5) / (r4 * r6)) == (r1 * r3) / (r2 * r4).
Proof.
intros r1 r2 r3 r4 r5 r6 H H0.
rewrite rdiv4; auto.
transitivity ((r5 * r6) * (r1 * r3) / ((r5 * r6) * (r2 * r4))).
apply SRdiv_ext; ring.
assert (HH: ~ r5*r6 == 0).
  apply field_is_integral_domain.
    intros H1; case H; rewrite H1; ring.
    intros H1; case H0; rewrite H1; ring.
rewrite <- rdiv4 ; auto.
  rewrite rdiv_r_r; auto.

  apply field_is_integral_domain.
    intros H1; case H; rewrite H1; ring.
    intros H1; case H0; rewrite H1; ring.
Qed.


Theorem rdiv7:
 forall r1 r2 r3 r4,
 ~ r2 == 0 ->
 ~ r3 == 0 ->
 ~ r4 == 0 ->
 (r1 / r2) / (r3 / r4) == (r1 * r4) / (r2 * r3).
Proof.
intros.
rewrite (rdiv_def (r1 / r2)).
rewrite rdiv6; trivial.
apply rdiv4; trivial.
Qed.

Theorem rdiv7b:
 forall r1 r2 r3 r4 r5 r6,
 ~ r2 * r6 == 0 ->
 ~ r3 * r5 == 0 ->
 ~ r4 * r6 == 0 ->
 ((r1 * r5) / (r2 * r6)) / ((r3 * r5) / (r4 * r6)) == (r1 * r4) / (r2 * r3).
Proof.
intros.
rewrite rdiv7; auto.
transitivity ((r5 * r6) * (r1 * r4) / ((r5 * r6) * (r2 * r3))).
apply SRdiv_ext; ring.
assert (HH: ~ r5*r6 == 0).
  apply field_is_integral_domain.
    intros H2; case H0; rewrite H2; ring.
    intros H2; case H1; rewrite H2; ring.
rewrite <- rdiv4 ; auto.
rewrite rdiv_r_r; auto.
  apply field_is_integral_domain.
    intros H2; case H; rewrite H2; ring.
    intros H2; case H0; rewrite H2; ring.
Qed.


Theorem rdiv8: forall r1 r2, ~ r2 == 0 -> r1 == 0 ->  r1 / r2 == 0.
intros r1 r2 H H0.
transitivity (r1 * / r2); auto.
transitivity (0 * / r2); auto.
Qed.


Theorem cross_product_eq : forall r1 r2 r3 r4,
  ~ r2 == 0 -> ~ r4 == 0 -> r1 * r4 == r3 * r2 -> r1 / r2 == r3 / r4.
intros.
transitivity (r1 / r2 * (r4 / r4)).
 rewrite rdiv_r_r; trivial.
   symmetry .
   apply (ARmul_1_r Rsth ARth).
 rewrite rdiv4; trivial.
   rewrite H1.
   rewrite (ARmul_comm ARth r2 r4).
   rewrite <- rdiv4; trivial.
   rewrite rdiv_r_r by trivial.
  apply (ARmul_1_r Rsth ARth).
Qed.

(***************************************************************************

                       Some equality test

  ***************************************************************************)

(* equality test *)
Fixpoint PExpr_eq (e1 e2 : PExpr C) {struct e1} : bool :=
 match e1, e2 with
   PEc c1, PEc c2 => ceqb c1 c2
  | PEX p1, PEX p2 => Pos.eqb p1 p2
  | PEadd e3 e5, PEadd e4 e6 => if PExpr_eq e3 e4 then PExpr_eq e5 e6 else false
  | PEsub e3 e5, PEsub e4 e6 => if PExpr_eq e3 e4 then PExpr_eq e5 e6 else false
  | PEmul e3 e5, PEmul e4 e6 => if PExpr_eq e3 e4 then PExpr_eq e5 e6 else false
  | PEopp e3, PEopp e4 => PExpr_eq e3 e4
  | PEpow e3 n3, PEpow e4 n4 => if N.eqb n3 n4 then PExpr_eq e3 e4 else false
  | _, _ => false
 end.

Add Morphism (pow_pos rmul) with signature req ==> eq ==> req as pow_morph.
intros x y H p;induction p as [p IH| p IH|];simpl;auto;ring[IH].
Qed.

Add Morphism (pow_N rI rmul) with signature req ==> eq ==> req as pow_N_morph.
intros x y H [|p];simpl;auto. apply pow_morph;trivial.
Qed.

Theorem PExpr_eq_semi_correct:
 forall l e1 e2, PExpr_eq e1 e2 = true ->  NPEeval l e1 == NPEeval l e2.
intros l e1; elim e1.
intros c1; intros e2; elim e2; simpl; (try (intros; discriminate)).
intros c2; apply (morph_eq CRmorph).
intros p1; intros e2; elim e2; simpl; (try (intros; discriminate)).
intros p2; case Pos.eqb_spec; intros; now subst.
intros e3 rec1 e5 rec2 e2; case e2; simpl; (try (intros; discriminate)).
intros e4 e6; generalize (rec1 e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); generalize (rec2 e6); case (PExpr_eq e5 e6);
 (try (intros; discriminate)); auto.
intros e3 rec1 e5 rec2 e2; case e2; simpl; (try (intros; discriminate)).
intros e4 e6; generalize (rec1 e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); generalize (rec2 e6); case (PExpr_eq e5 e6);
 (try (intros; discriminate)); auto.
intros e3 rec1 e5 rec2 e2; case e2; simpl; (try (intros; discriminate)).
intros e4 e6; generalize (rec1 e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); generalize (rec2 e6); case (PExpr_eq e5 e6);
 (try (intros; discriminate)); auto.
intros e3 rec e2; (case e2; simpl; (try (intros; discriminate))).
intros e4; generalize (rec e4); case (PExpr_eq e3 e4);
 (try (intros; discriminate)); auto.
intros e3 rec n3 e2;(case e2;simpl;(try (intros;discriminate))).
intros e4 n4; case N.eqb_spec; try discriminate; intros EQ H; subst.
repeat rewrite  pow_th.(rpow_pow_N). rewrite (rec _ H);auto.
Qed.

(* add *)
Definition NPEadd e1 e2 :=
  match e1, e2 with
    PEc c1, PEc c2 => PEc (cadd c1 c2)
  | PEc c, _ => if ceqb c cO then e2 else PEadd e1 e2
  |  _, PEc c => if ceqb c cO then e1 else PEadd e1 e2
    (* Peut t'on factoriser ici ??? *)
  | _, _ => PEadd e1 e2
  end.

Theorem NPEadd_correct:
 forall l e1 e2, NPEeval l (NPEadd e1 e2) == NPEeval l (PEadd e1 e2).
Proof.
intros l e1 e2.
destruct e1; destruct e2; simpl; try reflexivity; try apply ceqb_rect;
 try (intro eq_c; rewrite eq_c); simpl;try apply eq_refl;
 try (ring [(morph0 CRmorph)]).
 apply (morph_add CRmorph).
Qed.

Definition NPEpow x n :=
  match n with
  | N0 => PEc cI
  | Npos p =>
    if Pos.eqb p xH then x else
    match x with
    | PEc c =>
      if ceqb c cI then PEc cI else if ceqb c cO then PEc cO else PEc (pow_pos cmul c p)
    | _ => PEpow x n
    end
  end.

Theorem NPEpow_correct : forall l e n,
  NPEeval l (NPEpow e n) == NPEeval l (PEpow e n).
Proof.
 destruct n;simpl.
 rewrite pow_th.(rpow_pow_N);simpl;auto.
 fold (p =? 1)%positive.
 case Pos.eqb_spec; intros H; (rewrite H || clear H).
 now rewrite  pow_th.(rpow_pow_N).
 destruct e;simpl;auto.
 repeat apply ceqb_rect;simpl;intros;rewrite pow_th.(rpow_pow_N);simpl.
 symmetry;induction p;simpl;trivial; ring [IHp H CRmorph.(morph1)].
 symmetry; induction p;simpl;trivial;ring [IHp CRmorph.(morph0)].
 induction p;simpl;auto;repeat rewrite CRmorph.(morph_mul);ring [IHp].
Qed.

(* mul *)
Fixpoint NPEmul (x y : PExpr C) {struct x} : PExpr C :=
  match x, y with
    PEc c1, PEc c2 => PEc (cmul c1 c2)
  | PEc c, _ =>
      if ceqb c cI then y else if ceqb c cO then PEc cO else PEmul x y
  |  _, PEc c =>
      if ceqb c cI then x else if ceqb c cO then PEc cO else PEmul x y
  | PEpow e1 n1, PEpow e2 n2 =>
      if N.eqb n1 n2 then NPEpow (NPEmul e1 e2) n1 else PEmul x y
  | _, _ => PEmul x y
  end.

Lemma pow_pos_mul : forall x y p, pow_pos rmul (x * y) p == pow_pos rmul x p * pow_pos rmul y p.
induction p;simpl;auto;try ring [IHp].
Qed.

Theorem NPEmul_correct : forall l e1 e2,
  NPEeval l (NPEmul e1 e2) == NPEeval l (PEmul e1 e2).
induction e1;destruct e2; simpl;try reflexivity;
 repeat apply ceqb_rect;
 try (intro eq_c; rewrite eq_c); simpl; try reflexivity;
 try ring [(morph0 CRmorph) (morph1 CRmorph)].
 apply (morph_mul CRmorph).
case N.eqb_spec; intros H; try rewrite <- H; clear H.
rewrite NPEpow_correct. simpl.
repeat rewrite pow_th.(rpow_pow_N).
rewrite IHe1; destruct n;simpl;try ring.
apply pow_pos_mul.
simpl;auto.
Qed.

(* sub *)
Definition NPEsub e1 e2 :=
  match e1, e2 with
    PEc c1, PEc c2 => PEc (csub c1 c2)
  | PEc c, _ => if ceqb c cO then PEopp e2 else PEsub e1 e2
  |  _, PEc c => if ceqb c cO then e1 else PEsub e1 e2
     (* Peut-on factoriser ici *)
  | _, _ => PEsub e1 e2
  end.

Theorem NPEsub_correct:
 forall l e1 e2,  NPEeval l (NPEsub e1 e2) == NPEeval l (PEsub e1 e2).
intros l e1 e2.
destruct e1; destruct e2; simpl; try reflexivity; try apply ceqb_rect;
 try (intro eq_c; rewrite eq_c); simpl;
 try rewrite (morph0 CRmorph); try reflexivity;
 try (symmetry; apply rsub_0_l); try (symmetry; apply rsub_0_r).
apply (morph_sub CRmorph).
Qed.

(* opp *)
Definition NPEopp e1 :=
  match e1 with PEc c1 => PEc (copp c1) | _ => PEopp e1 end.

Theorem NPEopp_correct:
 forall l e1,  NPEeval l (NPEopp e1) == NPEeval l (PEopp e1).
intros l e1; case e1; simpl; auto.
intros; apply (morph_opp CRmorph).
Qed.

(* simplification *)
Fixpoint PExpr_simp (e : PExpr C) : PExpr C :=
 match e with
   PEadd e1 e2 => NPEadd (PExpr_simp e1) (PExpr_simp e2)
  | PEmul e1 e2 => NPEmul (PExpr_simp e1) (PExpr_simp e2)
  | PEsub e1 e2 => NPEsub (PExpr_simp e1) (PExpr_simp e2)
  | PEopp e1 => NPEopp (PExpr_simp e1)
  | PEpow e1 n1 => NPEpow (PExpr_simp e1) n1
  | _ => e
 end.

Theorem PExpr_simp_correct:
 forall l e,  NPEeval l (PExpr_simp e) == NPEeval l e.
intros l e; elim e; simpl; auto.
intros e1 He1 e2 He2.
transitivity (NPEeval l (PEadd (PExpr_simp e1) (PExpr_simp e2))); auto.
apply NPEadd_correct.
simpl; auto.
intros e1 He1 e2 He2.
transitivity (NPEeval l (PEsub (PExpr_simp e1) (PExpr_simp e2))); auto.
apply NPEsub_correct.
simpl; auto.
intros e1 He1 e2 He2.
transitivity (NPEeval l (PEmul (PExpr_simp e1) (PExpr_simp e2))); auto.
apply NPEmul_correct.
simpl; auto.
intros e1 He1.
transitivity (NPEeval l (PEopp (PExpr_simp e1))); auto.
apply NPEopp_correct.
simpl; auto.
intros e1 He1 n;simpl.
rewrite NPEpow_correct;simpl.
repeat rewrite pow_th.(rpow_pow_N).
rewrite He1;auto.
Qed.


(****************************************************************************

                               Datastructure

  ***************************************************************************)

(* The input: syntax of a field expression *)

Inductive FExpr : Type :=
   FEc: C ->  FExpr
 | FEX: positive ->  FExpr
 | FEadd: FExpr -> FExpr ->  FExpr
 | FEsub: FExpr -> FExpr ->  FExpr
 | FEmul: FExpr -> FExpr ->  FExpr
 | FEopp: FExpr ->  FExpr
 | FEinv: FExpr ->  FExpr
 | FEdiv: FExpr -> FExpr ->  FExpr
 | FEpow: FExpr -> N -> FExpr .

Fixpoint FEeval (l : list R) (pe : FExpr) {struct pe} : R :=
  match pe with
  | FEc c     => phi c
  | FEX x     => BinList.nth 0 x l
  | FEadd x y => FEeval l x + FEeval l y
  | FEsub x y => FEeval l x - FEeval l y
  | FEmul x y => FEeval l x * FEeval l y
  | FEopp x   => - FEeval l x
  | FEinv x   => / FEeval l x
  | FEdiv x y => FEeval l x / FEeval l y
  | FEpow x n => rpow (FEeval l x) (Cp_phi n)
  end.

Strategy expand [FEeval].

(* The result of the normalisation *)

Record linear : Type := mk_linear {
   num : PExpr C;
   denum : PExpr C;
   condition : list (PExpr C) }.

(***************************************************************************

                Semantics and properties of side condition

  ***************************************************************************)

Fixpoint PCond (l : list R) (le : list (PExpr C)) {struct le} : Prop :=
  match le with
  | nil => True
  | e1 :: nil => ~ req (NPEeval l e1) rO
  | e1 :: l1 => ~ req (NPEeval l e1) rO /\ PCond l l1
  end.

Theorem PCond_cons_inv_l :
   forall l a l1, PCond l (a::l1) ->  ~ NPEeval l a == 0.
intros l a l1 H.
destruct l1; simpl in H |- *; trivial.
destruct H; trivial.
Qed.

Theorem PCond_cons_inv_r : forall l a l1, PCond l (a :: l1) ->  PCond l l1.
intros l a l1 H.
destruct l1; simpl in H |- *; trivial.
destruct H; trivial.
Qed.

Theorem PCond_app_inv_l: forall l l1 l2, PCond l (l1 ++ l2) ->  PCond l l1.
intros l l1 l2; elim l1; simpl app.
 simpl; auto.
 destruct l0; simpl in *.
  destruct l2; firstorder.
  firstorder.
Qed.

Theorem PCond_app_inv_r: forall l l1 l2, PCond l (l1 ++ l2) ->  PCond l l2.
intros l l1 l2; elim l1; simpl app; auto.
intros a l0 H H0; apply H; apply PCond_cons_inv_r with ( 1 := H0 ).
Qed.

(* An unsatisfiable condition: issued when a division by zero is detected *)
Definition absurd_PCond := cons (PEc cO) nil.

Lemma absurd_PCond_bottom : forall l, ~ PCond l absurd_PCond.
unfold absurd_PCond; simpl.
red; intros.
apply H.
apply (morph0 CRmorph).
Qed.

(***************************************************************************

                               Normalisation

  ***************************************************************************)

Fixpoint isIn (e1:PExpr C)  (p1:positive)
                      (e2:PExpr C)  (p2:positive) {struct e2}: option (N * PExpr C) :=
  match e2 with
  | PEmul e3 e4 =>
       match isIn e1 p1 e3 p2 with
       | Some (N0, e5) => Some (N0, NPEmul e5 (NPEpow e4 (Npos p2)))
       | Some (Npos p, e5) =>
          match isIn e1 p e4 p2 with
          | Some (n, e6) => Some (n, NPEmul e5 e6)
          | None => Some (Npos p, NPEmul e5 (NPEpow e4 (Npos p2)))
          end
       | None =>
         match isIn e1 p1 e4 p2 with
         | Some (n, e5) => Some (n,NPEmul (NPEpow e3 (Npos p2)) e5)
         | None => None
         end
       end
  | PEpow e3 N0 => None
  | PEpow e3 (Npos p3) => isIn e1 p1 e3 (Pos.mul p3 p2)
  | _ =>
     if  PExpr_eq e1 e2 then
         match Z.pos_sub p1 p2 with
          | Zpos p => Some (Npos p, PEc cI)
          | Z0 => Some (N0, PEc cI)
          | Zneg p => Some (N0, NPEpow e2 (Npos p))
          end
     else None
   end.

 Definition ZtoN z := match z with Zpos p => Npos p | _ => N0 end.
 Definition NtoZ n := match n with Npos p => Zpos p | _ => Z0 end.

 Notation pow_pos_add :=
   (Ring_theory.pow_pos_add Rsth Reqe.(Rmul_ext) ARth.(ARmul_assoc)).

 Lemma Z_pos_sub_gt p q : (p > q)%positive ->
  Z.pos_sub p q = Zpos (p - q).
 Proof. intros; now apply Z.pos_sub_gt, Pos.gt_lt. Qed.

 Ltac simpl_pos_sub := rewrite ?Z_pos_sub_gt in * by assumption.

 Lemma isIn_correct_aux : forall l e1 e2 p1 p2,
  match
      (if  PExpr_eq e1 e2 then
         match Z.sub (Zpos p1) (Zpos p2) with
          | Zpos p => Some (Npos p, PEc cI)
          | Z0 => Some (N0, PEc cI)
          | Zneg p => Some (N0, NPEpow e2 (Npos p))
          end
     else None)
   with
   | Some(n, e3) =>
       NPEeval l (PEpow e2 (Npos p2)) ==
       NPEeval l (PEmul (PEpow e1 (ZtoN (Zpos p1 - NtoZ n))) e3) /\
       (Zpos p1 > NtoZ n)%Z
   |  _ => True
  end.
Proof.
  intros l e1 e2 p1 p2; generalize (PExpr_eq_semi_correct l e1 e2);
   case (PExpr_eq e1 e2); simpl; auto; intros H.
  rewrite Z.pos_sub_spec.
  case Pos.compare_spec;intros;simpl.
  - repeat rewrite pow_th.(rpow_pow_N);simpl. split. 2:reflexivity.
    subst. rewrite H by trivial. ring [ (morph1 CRmorph)].
  - fold (p2 - p1 =? 1)%positive.
    fold (NPEpow e2 (Npos (p2 - p1))).
    rewrite NPEpow_correct;simpl.
    repeat rewrite pow_th.(rpow_pow_N);simpl.
    rewrite H;trivial. split. 2:reflexivity.
    rewrite <- pow_pos_add. now rewrite Pos.add_comm, Pos.sub_add.
  - repeat rewrite pow_th.(rpow_pow_N);simpl.
    rewrite H;trivial.
    rewrite Z.pos_sub_gt by now apply Pos.sub_decr.
    replace (p1 - (p1 - p2))%positive with p2;
    [| rewrite Pos.sub_sub_distr, Pos.add_comm;
       auto using Pos.add_sub, Pos.sub_decr ].
    split.
    simpl. ring [ (morph1 CRmorph)].
    now apply Z.lt_gt, Pos.sub_decr.
Qed.

Lemma pow_pos_pow_pos : forall x p1 p2, pow_pos rmul (pow_pos rmul x p1) p2 == pow_pos rmul x (p1*p2).
induction p1;simpl;intros;repeat rewrite pow_pos_mul;repeat rewrite pow_pos_add;simpl.
ring [(IHp1 p2)]. ring [(IHp1 p2)]. auto.
Qed.


Theorem isIn_correct: forall l e1 p1 e2 p2,
  match isIn e1 p1 e2 p2 with
   | Some(n, e3) =>
       NPEeval l (PEpow e2 (Npos p2)) ==
       NPEeval l (PEmul (PEpow e1 (ZtoN (Zpos p1 - NtoZ n))) e3) /\
        (Zpos p1 > NtoZ n)%Z
   |  _ => True
  end.
Proof.
Opaque NPEpow.
intros l e1 p1 e2; generalize p1;clear p1;elim e2; intros;
  try (refine (isIn_correct_aux l e1 _ p1 p2);fail);simpl isIn.
generalize (H p1 p2);clear H;destruct (isIn e1 p1 p p2). destruct p3.
destruct n.
  simpl. rewrite NPEmul_correct. simpl; rewrite NPEpow_correct;simpl.
  repeat rewrite pow_th.(rpow_pow_N);simpl.
  rewrite pow_pos_mul;intros (H,H1);split;[ring[H]|trivial].
  generalize (H0 p4 p2);clear H0;destruct (isIn e1 p4 p0 p2). destruct p5.
  destruct n;simpl.
    rewrite NPEmul_correct;repeat rewrite pow_th.(rpow_pow_N);simpl.
    intros (H1,H2) (H3,H4).
    simpl_pos_sub. simpl in H3.
    rewrite pow_pos_mul. rewrite H1;rewrite H3.
    assert (pow_pos rmul (NPEeval l e1) (p1 - p4) * NPEeval l p3 *
        (pow_pos rmul (NPEeval l e1) p4 * NPEeval l p5) ==
        pow_pos rmul (NPEeval l e1) p4 * pow_pos rmul (NPEeval l e1) (p1 - p4) *
        NPEeval l p3 *NPEeval l p5) by ring. rewrite H;clear H.
   rewrite <- pow_pos_add.
   rewrite Pos.add_comm, Pos.sub_add by (now apply Z.gt_lt in H4).
   split. symmetry;apply ARth.(ARmul_assoc). reflexivity.
   repeat rewrite pow_th.(rpow_pow_N);simpl.
   intros (H1,H2) (H3,H4).
   simpl_pos_sub. simpl in H1, H3.
   assert (Zpos p1 > Zpos p6)%Z.
     apply Zgt_trans with (Zpos p4). exact H4. exact H2.
  simpl_pos_sub.
  split. 2:exact H.
  rewrite pow_pos_mul. simpl;rewrite H1;rewrite H3.
  assert (pow_pos rmul (NPEeval l e1) (p1 - p4) * NPEeval l p3 *
                (pow_pos rmul (NPEeval l e1) (p4 - p6) * NPEeval l p5) ==
             pow_pos rmul (NPEeval l e1) (p1 - p4) * pow_pos rmul (NPEeval l e1) (p4 - p6) *
                NPEeval l p3 * NPEeval l p5) by ring. rewrite H0;clear H0.
  rewrite <- pow_pos_add.
  replace (p1 - p4 + (p4 - p6))%positive with (p1 - p6)%positive.
 rewrite NPEmul_correct. simpl;ring.
  assert
     (Zpos p1 - Zpos p6 = Zpos p1 - Zpos p4 + (Zpos p4 - Zpos p6))%Z.
 change  ((Zpos p1 - Zpos p6)%Z = (Zpos p1 + (- Zpos p4) + (Zpos p4 +(- Zpos p6)))%Z).
 rewrite <- Z.add_assoc. rewrite (Z.add_assoc  (- Zpos p4)).
 simpl. rewrite Z.pos_sub_diag. simpl. reflexivity.
 unfold Z.sub, Z.opp in H0. simpl in H0.
  simpl_pos_sub. inversion H0; trivial.
 simpl. repeat rewrite pow_th.(rpow_pow_N).
 intros H1 (H2,H3). simpl_pos_sub.
 rewrite NPEmul_correct;simpl;rewrite NPEpow_correct;simpl.
 simpl in H2. rewrite pow_th.(rpow_pow_N);simpl.
 rewrite pow_pos_mul. split. ring [H2]. exact H3.
 generalize (H0 p1 p2);clear H0;destruct (isIn e1 p1 p0 p2). destruct p3.
 destruct n;simpl. rewrite NPEmul_correct;simpl;rewrite NPEpow_correct;simpl.
 repeat rewrite pow_th.(rpow_pow_N);simpl.
 intros (H1,H2);split;trivial. rewrite pow_pos_mul;ring [H1].
 rewrite NPEmul_correct;simpl;rewrite NPEpow_correct;simpl.
 repeat rewrite pow_th.(rpow_pow_N);simpl. rewrite pow_pos_mul.
 intros (H1, H2);rewrite H1;split.
   simpl_pos_sub. simpl in H1;ring [H1]. trivial.
 trivial.
 destruct n. trivial.
 generalize (H p1 (p0*p2)%positive);clear H;destruct (isIn e1 p1 p (p0*p2)). destruct p3.
 destruct n;simpl. repeat rewrite pow_th.(rpow_pow_N). simpl.
 intros (H1,H2);split. rewrite pow_pos_pow_pos. trivial. trivial.
 repeat rewrite pow_th.(rpow_pow_N). simpl.
 intros (H1,H2);split;trivial.
 rewrite pow_pos_pow_pos;trivial.
 trivial.
Qed.

Record rsplit : Type := mk_rsplit {
   rsplit_left : PExpr C;
   rsplit_common : PExpr C;
   rsplit_right : PExpr C}.

(* Stupid name clash *)
Notation left := rsplit_left.
Notation right := rsplit_right.
Notation common := rsplit_common.

Fixpoint split_aux (e1: PExpr C) (p:positive) (e2:PExpr C) {struct e1}: rsplit :=
  match e1 with
  | PEmul e3 e4 =>
      let r1 := split_aux e3 p e2 in
      let r2 := split_aux e4 p (right r1) in
          mk_rsplit (NPEmul (left r1) (left r2))
                    (NPEmul (common r1) (common r2))
                    (right r2)
  | PEpow e3 N0 => mk_rsplit (PEc cI) (PEc cI) e2
  | PEpow e3 (Npos p3) => split_aux e3 (Pos.mul p3 p) e2
  | _ =>
       match isIn e1 p e2 xH with
       | Some (N0,e3) => mk_rsplit (PEc cI) (NPEpow e1 (Npos p)) e3
       | Some (Npos q, e3) => mk_rsplit (NPEpow e1 (Npos q)) (NPEpow e1 (Npos (p - q))) e3
       | None => mk_rsplit (NPEpow e1 (Npos p)) (PEc cI) e2
       end
  end.

Lemma split_aux_correct_1 : forall l e1 p e2,
  let res :=  match isIn e1 p e2 xH with
       | Some (N0,e3) => mk_rsplit (PEc cI) (NPEpow e1 (Npos p)) e3
       | Some (Npos q, e3) => mk_rsplit (NPEpow e1 (Npos q)) (NPEpow e1 (Npos (p - q))) e3
       | None => mk_rsplit (NPEpow e1  (Npos p)) (PEc cI) e2
       end in
       NPEeval l (PEpow e1 (Npos p)) == NPEeval l (NPEmul (left res) (common res))
   /\
       NPEeval l e2 == NPEeval l (NPEmul (right res) (common res)).
Proof.
 intros. unfold res;clear res; generalize (isIn_correct l e1 p e2 xH).
 destruct (isIn e1 p e2 1). destruct p0.
 Opaque NPEpow NPEmul.
  destruct n;simpl;
    (repeat rewrite NPEmul_correct;simpl;
     repeat rewrite NPEpow_correct;simpl;
     repeat rewrite pow_th.(rpow_pow_N);simpl).
  intros (H, Hgt);split;try ring [H CRmorph.(morph1)].
  intros (H, Hgt). simpl_pos_sub. simpl in H;split;try ring [H].
  apply Z.gt_lt in Hgt.
  now rewrite <- pow_pos_add, Pos.add_comm, Pos.sub_add.
  simpl;intros. repeat rewrite NPEmul_correct;simpl.
  rewrite NPEpow_correct;simpl. split;ring [CRmorph.(morph1)].
Qed.

Theorem split_aux_correct: forall l e1 p e2,
  NPEeval l (PEpow e1 (Npos p)) ==
       NPEeval l (NPEmul (left (split_aux e1 p e2)) (common (split_aux e1 p e2)))
/\
  NPEeval l  e2 == NPEeval l (NPEmul (right (split_aux e1 p e2))
                                   (common (split_aux e1 p e2))).
Proof.
intros l; induction e1;intros k e2; try refine (split_aux_correct_1 l _ k e2);simpl.
generalize (IHe1_1 k e2); clear IHe1_1.
generalize (IHe1_2 k (rsplit_right (split_aux e1_1 k e2))); clear IHe1_2.
simpl. repeat (rewrite NPEmul_correct;simpl).
repeat rewrite pow_th.(rpow_pow_N);simpl.
intros (H1,H2) (H3,H4);split.
rewrite pow_pos_mul. rewrite H1;rewrite H3. ring.
rewrite H4;rewrite H2;ring.
destruct n;simpl.
split. repeat rewrite pow_th.(rpow_pow_N);simpl.
rewrite NPEmul_correct. simpl.
 induction k;simpl;try ring [CRmorph.(morph1)]; ring [IHk CRmorph.(morph1)].
 rewrite NPEmul_correct;simpl. ring [CRmorph.(morph1)].
generalize (IHe1 (p*k)%positive e2);clear IHe1;simpl.
repeat rewrite NPEmul_correct;simpl.
repeat rewrite pow_th.(rpow_pow_N);simpl.
rewrite pow_pos_pow_pos. intros [H1 H2];split;ring [H1 H2].
Qed.

Definition split e1 e2 := split_aux e1 xH e2.

Theorem split_correct_l: forall l e1 e2,
  NPEeval l e1 == NPEeval l (NPEmul (left (split e1 e2))
                                   (common (split e1 e2))).
Proof.
intros l e1 e2; case (split_aux_correct l e1 xH e2);simpl.
rewrite pow_th.(rpow_pow_N);simpl;auto.
Qed.

Theorem split_correct_r: forall l e1 e2,
  NPEeval l e2 == NPEeval l (NPEmul (right (split e1 e2))
                                   (common (split e1 e2))).
Proof.
intros l e1 e2; case (split_aux_correct l e1 xH e2);simpl;auto.
Qed.

Fixpoint Fnorm (e : FExpr) : linear :=
  match e with
  | FEc c => mk_linear (PEc c) (PEc cI) nil
  | FEX x => mk_linear (PEX C x) (PEc cI) nil
  | FEadd e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        (NPEadd (NPEmul (num x) (right s)) (NPEmul (num y) (left s)))
        (NPEmul (left s) (NPEmul (right s) (common s)))
        (condition x ++ condition y)

  | FEsub e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s := split (denum x) (denum y) in
      mk_linear
        (NPEsub (NPEmul (num x) (right s)) (NPEmul (num y) (left s)))
        (NPEmul (left s) (NPEmul (right s) (common s)))
        (condition x ++ condition y)
  | FEmul e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s1 := split (num x) (denum y) in
      let s2 := split (num y) (denum x) in
      mk_linear (NPEmul (left s1) (left s2))
        (NPEmul (right s2) (right s1))
        (condition x ++ condition y)
  | FEopp e1 =>
      let x := Fnorm e1 in
      mk_linear (NPEopp (num x)) (denum x) (condition x)
  | FEinv e1 =>
      let x := Fnorm e1 in
      mk_linear (denum x) (num x) (num x :: condition x)
  | FEdiv e1 e2 =>
      let x := Fnorm e1 in
      let y := Fnorm e2 in
      let s1 := split (num x) (num y) in
      let s2 := split (denum x) (denum y) in
      mk_linear (NPEmul (left s1) (right s2))
        (NPEmul (left s2) (right s1))
        (num y :: condition x ++ condition y)
  | FEpow e1 n =>
      let x := Fnorm e1 in
      mk_linear (NPEpow (num x) n) (NPEpow (denum x) n) (condition x)
  end.


(* Example *)
(*
Eval compute
   in (Fnorm
        (FEdiv
          (FEc cI)
          (FEadd (FEinv (FEX xH%positive)) (FEinv (FEX (xO xH)%positive))))).
*)

 Lemma pow_pos_not_0 : forall x, ~x==0 -> forall p, ~pow_pos rmul x p == 0.
Proof.
 induction p;simpl.
  intro Hp;assert (H1 := @rmul_reg_l _ (pow_pos rmul x p * pow_pos rmul x p) 0 H).
  apply IHp.
  rewrite (@rmul_reg_l _ (pow_pos rmul x p)  0 IHp).
  reflexivity.
  rewrite H1. ring. rewrite Hp;ring.
  intro Hp;apply IHp. rewrite (@rmul_reg_l _ (pow_pos rmul x p)  0 IHp).
  reflexivity. rewrite Hp;ring. trivial.
Qed.

Theorem Pcond_Fnorm:
 forall l e,
 PCond l (condition (Fnorm e)) ->  ~ NPEeval l (denum (Fnorm e)) == 0.
intros l e; elim e.
 simpl; intros _ _; rewrite (morph1 CRmorph); exact rI_neq_rO.
 simpl; intros _ _; rewrite (morph1 CRmorph); exact rI_neq_rO.
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum.
   rewrite NPEmul_correct.
   simpl.
   apply field_is_integral_domain.
   intros HH; case Hrec1; auto.
     apply PCond_app_inv_l with (1 := Hcond).
   rewrite (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2))).
   rewrite NPEmul_correct; simpl; rewrite HH; ring.
   intros HH; case Hrec2; auto.
     apply PCond_app_inv_r with (1 := Hcond).
   rewrite (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))); auto.
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum.
   rewrite NPEmul_correct.
   simpl.
   apply field_is_integral_domain.
   intros HH; case Hrec1; auto.
     apply PCond_app_inv_l with (1 := Hcond).
   rewrite (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2))).
   rewrite NPEmul_correct; simpl; rewrite HH; ring.
   intros HH; case Hrec2; auto.
     apply PCond_app_inv_r with (1 := Hcond).
   rewrite (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))); auto.
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum.
   rewrite NPEmul_correct.
   simpl.
   apply field_is_integral_domain.
  intros HH; apply Hrec1.
    apply PCond_app_inv_l with (1 := Hcond).
    rewrite (split_correct_r l (num (Fnorm e2)) (denum (Fnorm e1))).
    rewrite NPEmul_correct; simpl; rewrite HH; ring.
  intros HH; apply Hrec2.
    apply PCond_app_inv_r with (1 := Hcond).
    rewrite (split_correct_r l (num (Fnorm e1)) (denum (Fnorm e2))).
    rewrite NPEmul_correct; simpl; rewrite HH; ring.
 intros e1 Hrec1 Hcond.
   simpl condition in Hcond.
   simpl denum.
   auto.
 intros e1 Hrec1 Hcond.
   simpl condition in Hcond.
   simpl denum.
   apply PCond_cons_inv_l with (1:=Hcond).
 intros e1 Hrec1 e2 Hrec2 Hcond.
   simpl condition in Hcond.
   simpl denum.
   rewrite NPEmul_correct.
   simpl.
   apply field_is_integral_domain.
    intros HH; apply Hrec1.
    specialize PCond_cons_inv_r with (1:=Hcond); intro Hcond1.
    apply PCond_app_inv_l with (1 := Hcond1).
    rewrite (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2))).
    rewrite NPEmul_correct; simpl; rewrite HH; ring.
    intros HH; apply PCond_cons_inv_l with (1:=Hcond).
    rewrite (split_correct_r l (num (Fnorm e1)) (num (Fnorm e2))).
    rewrite NPEmul_correct; simpl; rewrite HH; ring.
 simpl;intros e1 Hrec1 n Hcond.
  rewrite NPEpow_correct.
  simpl;rewrite pow_th.(rpow_pow_N).
  destruct n;simpl;intros.
  apply AFth.(AF_1_neq_0). apply pow_pos_not_0;auto.
Qed.
Hint Resolve Pcond_Fnorm.


(***************************************************************************

                       Main theorem

  ***************************************************************************)

Theorem Fnorm_FEeval_PEeval:
 forall l fe,
 PCond l (condition (Fnorm fe)) ->
 FEeval l fe == NPEeval l (num (Fnorm fe)) / NPEeval l (denum (Fnorm fe)).
Proof.
intros l fe; elim fe; simpl.
intros c H; rewrite CRmorph.(morph1); apply rdiv1.
intros p H; rewrite CRmorph.(morph1); apply rdiv1.
intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
rewrite NPEadd_correct; simpl.
repeat rewrite NPEmul_correct; simpl.
generalize (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))).
repeat rewrite NPEmul_correct; simpl.
intros U1 U2; rewrite U1; rewrite U2.
apply rdiv2b; auto.
  rewrite <- U1; auto.
  rewrite <- U2; auto.

intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
rewrite NPEsub_correct; simpl.
repeat rewrite NPEmul_correct; simpl.
generalize (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))).
repeat rewrite NPEmul_correct; simpl.
intros U1 U2; rewrite U1; rewrite U2.
apply rdiv3b; auto.
  rewrite <- U1; auto.
  rewrite <- U2; auto.

intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
repeat rewrite NPEmul_correct; simpl.
generalize (split_correct_l l (num (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_r l (num (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_l l (num (Fnorm e2)) (denum (Fnorm e1)))
   (split_correct_r l (num (Fnorm e2)) (denum (Fnorm e1))).
repeat rewrite NPEmul_correct; simpl.
intros U1 U2 U3 U4; rewrite U1; rewrite U2; rewrite U3;
  rewrite U4; simpl.
apply rdiv4b; auto.
  rewrite <- U4; auto.
  rewrite <- U2; auto.

intros e1 He1 HH.
rewrite NPEopp_correct; simpl; rewrite (He1 HH); apply rdiv5; auto.

intros e1 He1 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_cons_inv_r with ( 1 := HH ).
rewrite (He1 HH1); apply rdiv6; auto.
apply PCond_cons_inv_l with ( 1 := HH ).

intros e1 He1 e2 He2 HH.
assert (HH1: PCond l (condition (Fnorm e1))).
apply PCond_app_inv_l with (condition (Fnorm e2)).
apply PCond_cons_inv_r with ( 1 := HH ).
assert (HH2: PCond l (condition (Fnorm e2))).
apply PCond_app_inv_r with (condition (Fnorm e1)).
apply PCond_cons_inv_r with ( 1 := HH ).
rewrite (He1 HH1); rewrite (He2 HH2).
repeat rewrite NPEmul_correct;simpl.
generalize (split_correct_l l (num (Fnorm e1)) (num (Fnorm e2)))
   (split_correct_r l (num (Fnorm e1)) (num (Fnorm e2)))
   (split_correct_l l (denum (Fnorm e1)) (denum (Fnorm e2)))
   (split_correct_r l (denum (Fnorm e1)) (denum (Fnorm e2))).
repeat rewrite NPEmul_correct; simpl.
intros U1 U2 U3 U4; rewrite U1; rewrite U2; rewrite U3;
  rewrite U4; simpl.
apply rdiv7b; auto.
  rewrite <- U3; auto.
  rewrite <- U2; auto.
apply PCond_cons_inv_l with ( 1 := HH ).
  rewrite <- U4; auto.

intros e1 He1 n Hcond;assert (He1' := He1 Hcond);clear He1.
repeat rewrite NPEpow_correct;simpl;repeat rewrite pow_th.(rpow_pow_N).
rewrite He1';clear He1'.
destruct n;simpl. apply rdiv1.
generalize (NPEeval l (num (Fnorm e1))) (NPEeval l (denum (Fnorm e1)))
  (Pcond_Fnorm _ _ Hcond).
intros r r0 Hdiff;induction p;simpl.
repeat (rewrite <- rdiv4;trivial).
rewrite IHp. reflexivity.
apply pow_pos_not_0;trivial.
apply pow_pos_not_0;trivial.
intro Hp. apply (pow_pos_not_0 Hdiff  p).
rewrite  (@rmul_reg_l (pow_pos rmul r0 p) (pow_pos rmul r0 p)  0).
 reflexivity. apply pow_pos_not_0;trivial. ring [Hp].
rewrite <- rdiv4;trivial.
rewrite IHp;reflexivity.
apply pow_pos_not_0;trivial. apply pow_pos_not_0;trivial.
reflexivity.
Qed.

Theorem Fnorm_crossproduct:
 forall l fe1 fe2,
 let nfe1 := Fnorm fe1 in
 let nfe2 := Fnorm fe2 in
 NPEeval l (PEmul (num nfe1) (denum nfe2)) ==
 NPEeval l (PEmul (num nfe2) (denum nfe1)) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
intros l fe1 fe2 nfe1 nfe2 Hcrossprod Hcond; subst nfe1 nfe2.
rewrite Fnorm_FEeval_PEeval by
 apply PCond_app_inv_l with (1 := Hcond).
 rewrite Fnorm_FEeval_PEeval by
  apply PCond_app_inv_r with (1 := Hcond).
  apply cross_product_eq; trivial.
   apply Pcond_Fnorm.
     apply PCond_app_inv_l with (1 := Hcond).
   apply Pcond_Fnorm.
     apply PCond_app_inv_r with (1 := Hcond).
Qed.

(* Correctness lemmas of reflexive tactics *)
Notation Ninterp_PElist := (interp_PElist rO radd rmul rsub ropp req phi Cp_phi rpow).
Notation Nmk_monpol_list := (mk_monpol_list cO cI cadd cmul csub copp ceqb cdiv).

Theorem Fnorm_correct:
 forall n l lpe fe,
  Ninterp_PElist l lpe ->
  Peq ceqb (Nnorm n (Nmk_monpol_list lpe) (num (Fnorm fe))) (Pc cO) = true ->
  PCond l (condition (Fnorm fe)) ->  FEeval l fe == 0.
intros n l lpe fe Hlpe H H1;
 apply eq_trans with (1 := Fnorm_FEeval_PEeval l fe H1).
apply rdiv8; auto.
transitivity (NPEeval l (PEc cO)); auto.
rewrite (norm_subst_ok Rsth Reqe ARth CRmorph pow_th cdiv_th n l lpe);auto.
change (NPEeval l (PEc cO)) with (Pphi 0 radd rmul phi l (Pc cO)).
apply (Peq_ok Rsth Reqe CRmorph);auto.
simpl. apply (morph0 CRmorph); auto.
Qed.

(* simplify a field expression into a fraction *)
(* TODO: simplify when den is constant... *)
Definition display_linear l num den :=
  NPphi_dev l num / NPphi_dev l den.

Definition display_pow_linear l num den :=
  NPphi_pow l num / NPphi_pow l den.

Theorem Field_rw_correct :
 forall n lpe l,
   Ninterp_PElist l lpe ->
   forall lmp, Nmk_monpol_list lpe = lmp ->
   forall fe nfe, Fnorm fe = nfe ->
   PCond l (condition nfe) ->
   FEeval l fe == display_linear l (Nnorm n lmp (num nfe)) (Nnorm n lmp (denum nfe)).
Proof.
  intros n lpe l Hlpe lmp lmp_eq fe nfe eq_nfe H; subst nfe lmp.
  apply eq_trans with (1 := Fnorm_FEeval_PEeval _ _ H).
  unfold display_linear; apply SRdiv_ext;
  eapply (ring_rw_correct Rsth Reqe ARth CRmorph);eauto.
Qed.

Theorem Field_rw_pow_correct :
 forall n lpe l,
   Ninterp_PElist l lpe ->
   forall lmp, Nmk_monpol_list lpe = lmp ->
   forall fe nfe, Fnorm fe = nfe ->
   PCond l (condition nfe) ->
   FEeval l fe == display_pow_linear l (Nnorm n lmp (num nfe)) (Nnorm n lmp (denum nfe)).
Proof.
  intros n lpe l Hlpe lmp lmp_eq fe nfe eq_nfe H; subst nfe lmp.
  apply eq_trans with (1 := Fnorm_FEeval_PEeval _ _ H).
  unfold display_pow_linear; apply SRdiv_ext;
  eapply (ring_rw_pow_correct Rsth Reqe ARth CRmorph);eauto.
Qed.

Theorem Field_correct :
 forall n l lpe fe1 fe2, Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 Peq ceqb (Nnorm n lmp (PEmul (num nfe1) (denum nfe2)))
          (Nnorm n lmp (PEmul (num nfe2) (denum nfe1))) = true ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros n l lpe fe1 fe2 Hlpe lmp eq_lmp nfe1 eq1 nfe2 eq2 Hnorm Hcond; subst nfe1 nfe2 lmp.
apply Fnorm_crossproduct; trivial.
eapply (ring_correct Rsth Reqe ARth CRmorph); eauto.
Qed.

(* simplify a field equation : generate the crossproduct and simplify
   polynomials *)
Theorem Field_simplify_eq_old_correct :
 forall l fe1 fe2 nfe1 nfe2,
 Fnorm fe1 = nfe1 ->
 Fnorm fe2 = nfe2 ->
 NPphi_dev l (Nnorm O nil (PEmul (num nfe1) (denum nfe2))) ==
 NPphi_dev l (Nnorm O nil (PEmul (num nfe2) (denum nfe1))) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros l fe1 fe2 nfe1 nfe2 eq1 eq2 Hcrossprod Hcond;  subst nfe1 nfe2.
apply Fnorm_crossproduct; trivial.
match goal with
 [ |- NPEeval l ?x == NPEeval l ?y] =>
    rewrite (ring_rw_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec
       O nil l I Logic.eq_refl x Logic.eq_refl);
    rewrite (ring_rw_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec
       O nil l I Logic.eq_refl y Logic.eq_refl)
 end.
trivial.
Qed.

Theorem Field_simplify_eq_correct :
 forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 NPphi_dev l (Nnorm n lmp (PEmul (num nfe1) (right den))) ==
 NPphi_dev l (Nnorm n lmp (PEmul (num nfe2) (left den))) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros n l lpe fe1 fe2 Hlpe lmp Hlmp nfe1 eq1 nfe2 eq2 den eq3 Hcrossprod Hcond;
  subst nfe1 nfe2 den lmp.
apply Fnorm_crossproduct; trivial.
simpl.
rewrite (split_correct_l l (denum (Fnorm fe1)) (denum (Fnorm fe2))).
rewrite (split_correct_r l (denum (Fnorm fe1)) (denum (Fnorm fe2))).
rewrite NPEmul_correct.
rewrite NPEmul_correct.
simpl.
repeat rewrite (ARmul_assoc ARth).
rewrite <-(
  let x := PEmul (num (Fnorm fe1))
                     (rsplit_right (split (denum (Fnorm fe1)) (denum (Fnorm fe2)))) in
ring_rw_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec n lpe l
        Hlpe Logic.eq_refl
        x Logic.eq_refl) in Hcrossprod.
rewrite <-(
  let x := (PEmul (num (Fnorm fe2))
                     (rsplit_left
                        (split (denum (Fnorm fe1)) (denum (Fnorm fe2))))) in
    ring_rw_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec n lpe l
        Hlpe Logic.eq_refl
        x Logic.eq_refl) in Hcrossprod.
simpl in Hcrossprod.
rewrite Hcrossprod.
reflexivity.
Qed.

Theorem Field_simplify_eq_pow_correct :
 forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 NPphi_pow l (Nnorm n lmp (PEmul (num nfe1) (right den))) ==
 NPphi_pow l (Nnorm n lmp (PEmul (num nfe2) (left den))) ->
 PCond l (condition nfe1 ++ condition nfe2) ->
 FEeval l fe1 == FEeval l fe2.
Proof.
intros n l lpe fe1 fe2 Hlpe lmp Hlmp nfe1 eq1 nfe2 eq2 den eq3 Hcrossprod Hcond;
  subst nfe1 nfe2 den lmp.
apply Fnorm_crossproduct; trivial.
simpl.
rewrite (split_correct_l l (denum (Fnorm fe1)) (denum (Fnorm fe2))).
rewrite (split_correct_r l (denum (Fnorm fe1)) (denum (Fnorm fe2))).
rewrite NPEmul_correct.
rewrite NPEmul_correct.
simpl.
repeat rewrite (ARmul_assoc ARth).
rewrite <-(
  let x := PEmul (num (Fnorm fe1))
                     (rsplit_right (split (denum (Fnorm fe1)) (denum (Fnorm fe2)))) in
ring_rw_pow_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec n lpe l
        Hlpe Logic.eq_refl
        x Logic.eq_refl) in Hcrossprod.
rewrite <-(
  let x := (PEmul (num (Fnorm fe2))
                     (rsplit_left
                        (split (denum (Fnorm fe1)) (denum (Fnorm fe2))))) in
    ring_rw_pow_correct Rsth Reqe ARth CRmorph pow_th cdiv_th get_sign_spec n lpe l
        Hlpe Logic.eq_refl
        x Logic.eq_refl) in Hcrossprod.
simpl in Hcrossprod.
rewrite Hcrossprod.
reflexivity.
Qed.

Theorem Field_simplify_eq_pow_in_correct :
 forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 forall np1, Nnorm n lmp (PEmul (num nfe1) (right den)) = np1 ->
 forall np2, Nnorm n lmp (PEmul (num nfe2) (left den)) = np2 ->
 FEeval l fe1 == FEeval l fe2 ->
  PCond l (condition nfe1 ++ condition nfe2) ->
 NPphi_pow l np1 ==
 NPphi_pow l np2.
Proof.
 intros. subst nfe1 nfe2 lmp np1 np2.
 repeat rewrite (Pphi_pow_ok Rsth Reqe ARth CRmorph pow_th get_sign_spec).
 repeat (rewrite <- (norm_subst_ok Rsth Reqe ARth CRmorph pow_th);trivial). simpl.
 assert (N1 := Pcond_Fnorm _ _ (PCond_app_inv_l _ _ _ H7)).
 assert (N2 := Pcond_Fnorm _ _ (PCond_app_inv_r _ _ _ H7)).
 apply (@rmul_reg_l (NPEeval l (rsplit_common den))).
 intro Heq;apply N1.
 rewrite (split_correct_l l (denum (Fnorm fe1)) (denum (Fnorm fe2))).
 rewrite H3. rewrite NPEmul_correct. simpl. ring [Heq].
 repeat rewrite (ARth.(ARmul_comm) (NPEeval l (rsplit_common den))).
 repeat rewrite <- ARth.(ARmul_assoc).
 change (NPEeval l (rsplit_right den) * NPEeval l (rsplit_common den)) with
      (NPEeval l (PEmul (rsplit_right den) (rsplit_common den))).
 change (NPEeval l (rsplit_left den) * NPEeval l (rsplit_common den)) with
      (NPEeval l (PEmul (rsplit_left den) (rsplit_common den))).
 repeat rewrite <- NPEmul_correct. rewrite <- H3. rewrite <- split_correct_l.
 rewrite <- split_correct_r.
 apply (@rmul_reg_l (/NPEeval l (denum (Fnorm fe2)))).
 intro Heq; apply AFth.(AF_1_neq_0).
 rewrite <- (@AFinv_l AFth (NPEeval l (denum (Fnorm fe2))));trivial.
 ring [Heq]. rewrite (ARth.(ARmul_comm)  (/ NPEeval l (denum (Fnorm fe2)))).
 repeat rewrite <- (ARth.(ARmul_assoc)).
 rewrite <- (AFth.(AFdiv_def)). rewrite rdiv_r_r by trivial.
 apply (@rmul_reg_l (/NPEeval l (denum (Fnorm fe1)))).
 intro Heq; apply AFth.(AF_1_neq_0).
 rewrite <- (@AFinv_l AFth (NPEeval l (denum (Fnorm fe1))));trivial.
 ring [Heq]. repeat rewrite (ARth.(ARmul_comm)  (/ NPEeval l (denum (Fnorm fe1)))).
 repeat rewrite <- (ARth.(ARmul_assoc)).
 repeat rewrite <- (AFth.(AFdiv_def)). rewrite rdiv_r_r by trivial.
 rewrite (AFth.(AFdiv_def)). ring_simplify. unfold SRopp.
 rewrite  (ARth.(ARmul_comm) (/ NPEeval l (denum (Fnorm fe2)))).
 repeat rewrite <- (AFth.(AFdiv_def)).
 repeat rewrite <- Fnorm_FEeval_PEeval ; trivial.
 apply (PCond_app_inv_r _ _ _ H7). apply (PCond_app_inv_l _ _ _ H7).
Qed.

Theorem Field_simplify_eq_in_correct :
forall n l lpe fe1 fe2,
    Ninterp_PElist l lpe ->
 forall lmp, Nmk_monpol_list lpe = lmp ->
 forall nfe1, Fnorm fe1 = nfe1 ->
 forall nfe2, Fnorm fe2 = nfe2 ->
 forall den, split (denum nfe1) (denum nfe2) = den ->
 forall np1, Nnorm n lmp (PEmul (num nfe1) (right den)) = np1 ->
 forall np2, Nnorm n lmp (PEmul (num nfe2) (left den)) = np2 ->
 FEeval l fe1 == FEeval l fe2 ->
  PCond l (condition nfe1 ++ condition nfe2) ->
 NPphi_dev l np1 ==
 NPphi_dev l np2.
Proof.
 intros. subst nfe1 nfe2 lmp np1 np2.
 repeat rewrite (Pphi_dev_ok Rsth Reqe ARth CRmorph  get_sign_spec).
 repeat (rewrite <- (norm_subst_ok Rsth Reqe ARth CRmorph pow_th);trivial). simpl.
 assert (N1 := Pcond_Fnorm _ _ (PCond_app_inv_l _ _ _ H7)).
 assert (N2 := Pcond_Fnorm _ _ (PCond_app_inv_r _ _ _ H7)).
 apply (@rmul_reg_l (NPEeval l (rsplit_common den))).
 intro Heq;apply N1.
 rewrite (split_correct_l l (denum (Fnorm fe1)) (denum (Fnorm fe2))).
 rewrite H3. rewrite NPEmul_correct. simpl. ring [Heq].
 repeat rewrite (ARth.(ARmul_comm) (NPEeval l (rsplit_common den))).
 repeat rewrite <- ARth.(ARmul_assoc).
 change (NPEeval l (rsplit_right den) * NPEeval l (rsplit_common den)) with
      (NPEeval l (PEmul (rsplit_right den) (rsplit_common den))).
 change (NPEeval l (rsplit_left den) * NPEeval l (rsplit_common den)) with
      (NPEeval l (PEmul (rsplit_left den) (rsplit_common den))).
 repeat rewrite <- NPEmul_correct;rewrite <- H3. rewrite <- split_correct_l.
 rewrite <- split_correct_r.
 apply (@rmul_reg_l (/NPEeval l (denum (Fnorm fe2)))).
 intro Heq; apply AFth.(AF_1_neq_0).
 rewrite <- (@AFinv_l AFth (NPEeval l (denum (Fnorm fe2))));trivial.
 ring [Heq]. rewrite (ARth.(ARmul_comm)  (/ NPEeval l (denum (Fnorm fe2)))).
 repeat rewrite <- (ARth.(ARmul_assoc)).
 rewrite <- (AFth.(AFdiv_def)). rewrite rdiv_r_r by trivial.
 apply (@rmul_reg_l (/NPEeval l (denum (Fnorm fe1)))).
 intro Heq; apply AFth.(AF_1_neq_0).
 rewrite <- (@AFinv_l AFth (NPEeval l (denum (Fnorm fe1))));trivial.
 ring [Heq]. repeat rewrite (ARth.(ARmul_comm)  (/ NPEeval l (denum (Fnorm fe1)))).
 repeat rewrite <- (ARth.(ARmul_assoc)).
 repeat rewrite <- (AFth.(AFdiv_def)). rewrite rdiv_r_r by trivial.
 rewrite (AFth.(AFdiv_def)). ring_simplify. unfold SRopp.
 rewrite  (ARth.(ARmul_comm) (/ NPEeval l (denum (Fnorm fe2)))).
 repeat rewrite <- (AFth.(AFdiv_def)).
 repeat rewrite <- Fnorm_FEeval_PEeval;trivial.
 apply (PCond_app_inv_r _ _ _ H7). apply (PCond_app_inv_l _ _ _ H7).
Qed.


Section Fcons_impl.

Variable Fcons : PExpr C -> list (PExpr C) -> list (PExpr C).

Hypothesis PCond_fcons_inv : forall l a l1,
  PCond l (Fcons a l1) ->  ~ NPEeval l a == 0 /\ PCond l l1.

Fixpoint Fapp (l m:list (PExpr C)) {struct l} : list (PExpr C) :=
  match l with
  | nil => m
  | cons a l1 => Fcons a (Fapp l1 m)
  end.

Lemma fcons_correct : forall l l1,
  PCond l (Fapp l1 nil) -> PCond l l1.
induction l1; simpl; intros.
 trivial.
 elim PCond_fcons_inv with (1 := H); intros.
   destruct l1; auto.
Qed.

End Fcons_impl.

Section Fcons_simpl.

(* Some general simpifications of the condition: eliminate duplicates,
   split multiplications *)

Fixpoint Fcons (e:PExpr C) (l:list (PExpr C)) {struct l} : list (PExpr C) :=
 match l with
   nil       => cons e nil
 | cons a l1 => if PExpr_eq e a then l else cons a (Fcons e l1)
 end.

Theorem PFcons_fcons_inv:
 forall l a l1, PCond l (Fcons a l1) ->  ~ NPEeval l a == 0 /\ PCond l l1.
intros l a l1; elim l1; simpl Fcons; auto.
simpl; auto.
intros a0 l0.
generalize (PExpr_eq_semi_correct l a a0); case (PExpr_eq a a0).
intros H H0 H1; split; auto.
rewrite H; auto.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
intros H H0 H1;
 assert (Hp: ~ NPEeval l a0 == 0 /\ (~ NPEeval l a == 0 /\ PCond l l0)).
split.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
apply H0.
generalize (PCond_cons_inv_r _ _ _ H1); simpl; auto.
generalize Hp; case l0; simpl; intuition.
Qed.

(* equality of normal forms rather than syntactic equality *)
Fixpoint Fcons0 (e:PExpr C) (l:list (PExpr C)) {struct l} : list (PExpr C) :=
 match l with
   nil       => cons e nil
 | cons a l1 =>
     if Peq ceqb (Nnorm O nil e) (Nnorm O nil a) then l
     else cons a (Fcons0 e l1)
 end.

Theorem PFcons0_fcons_inv:
 forall l a l1, PCond l (Fcons0 a l1) ->  ~ NPEeval l a == 0 /\ PCond l l1.
intros l a l1; elim l1; simpl Fcons0; auto.
simpl; auto.
intros a0 l0.
generalize (ring_correct Rsth Reqe ARth CRmorph pow_th cdiv_th O l nil a a0). simpl.
  case (Peq ceqb (Nnorm O nil a) (Nnorm O nil a0)).
intros H H0 H1; split; auto.
rewrite H; auto.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
intros H H0 H1;
 assert (Hp: ~ NPEeval l a0 == 0 /\ (~ NPEeval l a == 0 /\ PCond l l0)).
split.
generalize (PCond_cons_inv_l _ _ _ H1); simpl; auto.
apply H0.
generalize (PCond_cons_inv_r _ _ _ H1); simpl; auto.
clear get_sign get_sign_spec.
generalize Hp; case l0; simpl; intuition.
Qed.

(* split factorized denominators *)
Fixpoint Fcons00 (e:PExpr C) (l:list (PExpr C)) {struct e} : list (PExpr C) :=
 match e with
   PEmul e1 e2 => Fcons00 e1 (Fcons00 e2 l)
 | PEpow e1 _ => Fcons00 e1 l
 | _ => Fcons0 e l
 end.

Theorem PFcons00_fcons_inv:
  forall l a l1, PCond l (Fcons00 a l1) -> ~ NPEeval l a == 0 /\ PCond l l1.
intros l a; elim a; try (intros; apply PFcons0_fcons_inv; auto; fail).
 intros p H p0 H0 l1 H1.
   simpl in H1.
   case (H _ H1); intros H2 H3.
   case (H0 _ H3); intros H4 H5; split; auto.
   simpl.
   apply field_is_integral_domain; trivial.
   simpl;intros. rewrite pow_th.(rpow_pow_N).
   destruct (H _ H0);split;auto.
   destruct n;simpl. apply AFth.(AF_1_neq_0).
   apply pow_pos_not_0;trivial.
Qed.

Definition Pcond_simpl_gen :=
  fcons_correct _ PFcons00_fcons_inv.


(* Specific case when the equality test of coefs is complete w.r.t. the
   field equality: non-zero coefs can be eliminated, and opposite can
   be simplified (if -1 <> 0) *)

Hypothesis ceqb_complete : forall c1 c2, phi c1 == phi c2 -> ceqb c1 c2 = true.

Lemma ceqb_rect_complete : forall c1 c2 (A:Type) (x y:A) (P:A->Type),
  (phi c1 == phi c2 -> P x) ->
  (~ phi c1 == phi c2 -> P y) ->
  P (if ceqb c1 c2 then x else y).
Proof.
intros.
generalize (fun h => X (morph_eq CRmorph c1 c2 h)).
generalize (@ceqb_complete c1 c2).
case (c1 ?=! c2); auto; intros.
apply X0.
red; intro.
absurd (false = true); auto;  discriminate.
Qed.

Fixpoint Fcons1 (e:PExpr C) (l:list (PExpr C)) {struct e} : list (PExpr C) :=
 match e with
   PEmul e1 e2 => Fcons1 e1 (Fcons1 e2 l)
 | PEpow e _ => Fcons1 e l
 | PEopp e => if ceqb (copp cI) cO then absurd_PCond else Fcons1 e l
 | PEc c => if ceqb c cO then absurd_PCond else l
 | _ => Fcons0 e l
 end.

Theorem PFcons1_fcons_inv:
  forall l a l1, PCond l (Fcons1 a l1) -> ~ NPEeval l a == 0 /\ PCond l l1.
intros l a; elim a; try (intros; apply PFcons0_fcons_inv; auto; fail).
 simpl; intros c l1.
   apply ceqb_rect_complete; intros.
  elim (@absurd_PCond_bottom l H0).
  split; trivial.
    rewrite <- (morph0 CRmorph); trivial.
 intros p H p0 H0 l1 H1.
   simpl in H1.
   case (H _ H1); intros H2 H3.
   case (H0 _ H3); intros H4 H5; split; auto.
   simpl.
   apply field_is_integral_domain; trivial.
 simpl; intros p H l1.
   apply ceqb_rect_complete; intros.
  elim (@absurd_PCond_bottom l H1).
  destruct (H _ H1).
    split; trivial.
    apply ropp_neq_0; trivial.
    rewrite (morph_opp CRmorph) in H0.
    rewrite (morph1 CRmorph) in H0.
    rewrite (morph0 CRmorph) in H0.
    trivial.
 intros;simpl. destruct (H _ H0);split;trivial.
 rewrite pow_th.(rpow_pow_N). destruct n;simpl.
 apply AFth.(AF_1_neq_0). apply pow_pos_not_0;trivial.
Qed.

Definition Fcons2 e l := Fcons1 (PExpr_simp e) l.

Theorem PFcons2_fcons_inv:
 forall l a l1, PCond l (Fcons2 a l1) -> ~ NPEeval l a == 0 /\ PCond l l1.
unfold Fcons2; intros l a l1 H; split;
 case (PFcons1_fcons_inv l (PExpr_simp a) l1); auto.
intros H1 H2 H3; case H1.
transitivity (NPEeval l a); trivial.
apply PExpr_simp_correct.
Qed.

Definition Pcond_simpl_complete :=
  fcons_correct _ PFcons2_fcons_inv.

End Fcons_simpl.

End AlmostField.

Section FieldAndSemiField.

  Record field_theory : Prop := mk_field {
    F_R : ring_theory rO rI radd rmul rsub ropp req;
    F_1_neq_0 : ~ 1 == 0;
    Fdiv_def : forall p q, p / q == p * / q;
    Finv_l : forall p, ~ p == 0 ->  / p * p == 1
  }.

  Definition F2AF f :=
    mk_afield
      (Rth_ARth Rsth Reqe f.(F_R)) f.(F_1_neq_0) f.(Fdiv_def) f.(Finv_l).

  Record semi_field_theory : Prop := mk_sfield {
    SF_SR : semi_ring_theory rO rI radd rmul req;
    SF_1_neq_0 : ~ 1 == 0;
    SFdiv_def : forall p q, p / q == p * / q;
    SFinv_l : forall p, ~ p == 0 ->  / p * p == 1
  }.

End FieldAndSemiField.

End MakeFieldPol.

  Definition SF2AF R (rO rI:R) radd rmul rdiv rinv req Rsth
    (sf:semi_field_theory rO rI radd rmul rdiv rinv req)  :=
    mk_afield _ _
      (SRth_ARth Rsth sf.(SF_SR))
      sf.(SF_1_neq_0)
      sf.(SFdiv_def)
      sf.(SFinv_l).


Section Complete.
 Variable R : Type.
 Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
 Variable (rdiv : R -> R ->  R) (rinv : R ->  R).
 Variable req : R -> R -> Prop.
  Notation "0" := rO.  Notation "1" := rI.
  Notation "x + y" := (radd x y).  Notation "x * y " := (rmul x y).
  Notation "x - y " := (rsub x y).  Notation "- x" := (ropp x).
  Notation "x / y " := (rdiv x y).  Notation "/ x" := (rinv x).
  Notation "x == y" := (req x y) (at level 70, no associativity).
 Variable Rsth : Setoid_Theory R req.
   Add Setoid R req Rsth as R_setoid3.
 Variable Reqe : ring_eq_ext radd rmul ropp req.
   Add Morphism radd : radd_ext3.  exact (Radd_ext Reqe). Qed.
   Add Morphism rmul : rmul_ext3.  exact (Rmul_ext Reqe). Qed.
   Add Morphism ropp : ropp_ext3.  exact (Ropp_ext Reqe). Qed.

Section AlmostField.

 Variable AFth : almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req.
 Let ARth := AFth.(AF_AR).
 Let rI_neq_rO := AFth.(AF_1_neq_0).
 Let rdiv_def := AFth.(AFdiv_def).
 Let rinv_l := AFth.(AFinv_l).

Hypothesis S_inj : forall x y, 1+x==1+y -> x==y.

Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Lemma add_inj_r : forall p x y,
   gen_phiPOS1 rI radd rmul p + x == gen_phiPOS1 rI radd rmul p + y -> x==y.
intros p x y.
elim p using Pos.peano_ind; simpl; intros.
 apply S_inj; trivial.
 apply H.
   apply S_inj.
   repeat rewrite (ARadd_assoc ARth).
   rewrite <- (ARgen_phiPOS_Psucc Rsth Reqe ARth); trivial.
Qed.

Lemma gen_phiPOS_inj : forall x y,
  gen_phiPOS rI radd rmul x == gen_phiPOS rI radd rmul y ->
  x = y.
intros x y.
repeat rewrite <- (same_gen Rsth Reqe ARth).
case (Pos.compare_spec x y).
 intros.
   trivial.
 intros.
   elim gen_phiPOS_not_0 with (y - x)%positive.
   apply add_inj_r with x.
   symmetry.
   rewrite (ARadd_0_r Rsth ARth).
   rewrite <- (ARgen_phiPOS_add Rsth Reqe ARth).
   now rewrite Pos.add_comm, Pos.sub_add.
 intros.
   elim gen_phiPOS_not_0 with (x - y)%positive.
   apply add_inj_r with y.
   rewrite (ARadd_0_r Rsth ARth).
   rewrite <- (ARgen_phiPOS_add Rsth Reqe ARth).
   now rewrite Pos.add_comm, Pos.sub_add.
Qed.


Lemma gen_phiN_inj : forall x y,
  gen_phiN rO rI radd rmul x == gen_phiN rO rI radd rmul y ->
  x = y.
destruct x; destruct y; simpl; intros; trivial.
 elim gen_phiPOS_not_0 with p.
   symmetry .
   rewrite (same_gen Rsth Reqe ARth); trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth); trivial.
 rewrite gen_phiPOS_inj with (1 := H); trivial.
Qed.

Lemma gen_phiN_complete : forall x y,
  gen_phiN rO rI radd rmul x == gen_phiN rO rI radd rmul y ->
  N.eqb x y = true.
Proof.
intros. now apply N.eqb_eq, gen_phiN_inj.
Qed.

End AlmostField.

Section Field.

 Variable Fth : field_theory rO rI radd rmul rsub ropp rdiv rinv req.
 Let Rth := Fth.(F_R).
 Let rI_neq_rO := Fth.(F_1_neq_0).
 Let rdiv_def := Fth.(Fdiv_def).
 Let rinv_l := Fth.(Finv_l).
 Let AFth := F2AF Rsth Reqe Fth.
 Let ARth := Rth_ARth Rsth Reqe Rth.

Lemma ring_S_inj : forall x y, 1+x==1+y -> x==y.
intros.
transitivity (x + (1 + - (1))).
 rewrite (Ropp_def Rth).
   symmetry .
   apply (ARadd_0_r Rsth ARth).
 transitivity (y + (1 + - (1))).
  repeat rewrite <- (ARplus_assoc ARth).
    repeat rewrite (ARadd_assoc ARth).
    apply (Radd_ext Reqe).
   repeat rewrite <- (ARadd_comm ARth 1).
     trivial.
   reflexivity.
  rewrite (Ropp_def Rth).
    apply (ARadd_0_r Rsth ARth).
Qed.


 Hypothesis gen_phiPOS_not_0 : forall p, ~ gen_phiPOS1 rI radd rmul p == 0.

Let gen_phiPOS_inject :=
   gen_phiPOS_inj AFth ring_S_inj gen_phiPOS_not_0.

Lemma gen_phiPOS_discr_sgn : forall x y,
  ~ gen_phiPOS rI radd rmul x == - gen_phiPOS rI radd rmul y.
red; intros.
apply gen_phiPOS_not_0 with (y + x)%positive.
rewrite (ARgen_phiPOS_add Rsth Reqe ARth).
transitivity (gen_phiPOS1 1 radd rmul y + - gen_phiPOS1 1 radd rmul y).
 apply (Radd_ext Reqe); trivial.
  reflexivity.
  rewrite (same_gen Rsth Reqe ARth).
    rewrite (same_gen Rsth Reqe ARth).
    trivial.
 apply (Ropp_def Rth).
Qed.

Lemma gen_phiZ_inj : forall x y,
  gen_phiZ rO rI radd rmul ropp x == gen_phiZ rO rI radd rmul ropp y ->
  x = y.
destruct x; destruct y; simpl; intros.
 trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   symmetry ; trivial.
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)).
   rewrite <- H.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   trivial.
 rewrite gen_phiPOS_inject  with (1 := H); trivial.
 elim gen_phiPOS_discr_sgn with (1 := H).
 elim gen_phiPOS_not_0 with p.
   rewrite (same_gen Rsth Reqe ARth).
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)).
   rewrite H.
   apply (ARopp_zero Rsth Reqe ARth).
 elim gen_phiPOS_discr_sgn with p0 p.
   symmetry ; trivial.
 replace p0 with p; trivial.
   apply gen_phiPOS_inject.
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p)).
   rewrite <- (Ropp_opp Rsth Reqe Rth (gen_phiPOS 1 radd rmul p0)).
   rewrite H; trivial.
   reflexivity.
Qed.

Lemma gen_phiZ_complete : forall x y,
  gen_phiZ rO rI radd rmul ropp x == gen_phiZ rO rI radd rmul ropp y ->
  Zeq_bool x y = true.
intros.
 replace y with x.
 unfold Zeq_bool.
   rewrite Z.compare_refl; trivial.
 apply gen_phiZ_inj; trivial.
Qed.

End Field.

End Complete.
