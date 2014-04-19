Require Import Arith.

(* Exercise 6 *)

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
intros x y H.
apply (plus_lt_compat_r x y 10). assumption.
Qed.

(* Exercise 7 *)

Goal forall P Q : nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
intros P Q H1 H2.
apply (H2 0). assumption.
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
intros P H.
exists 1. simpl. assumption.
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
intros P H1 H2 q.
destruct H2 as [p H3]. apply (H1 p q).
assumption.
Qed.

(* Exercise 8 *)

Goal forall m n : nat, (n * 10) + m = (10 * n) + m.
Proof.
intros m n.  
eapply NPeano.Nat.add_cancel_r.
eapply mult_comm.
Qed.

(* Exercise 9 *)

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
intros n m p q.
apply plus_permute_2_in_4.
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
intros n m.
erewrite mult_plus_distr_l.
repeat erewrite mult_plus_distr_r.
rewrite (plus_comm (n * m) (m * m)).
erewrite <- plus_permute_2_in_4.
eapply NPeano.Nat.add_cancel_l.
rewrite (mult_comm m n).
simpl. erewrite <- plus_n_O.
erewrite mult_plus_distr_r.
reflexivity.
Qed.

(* Exercise 10 *)

Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* \u4f7f\u3063\u3066\u3082\u3088\u3044 *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
intro x.
assert(H: (/(/x) * (/x)) * x * (/x) = 1).
 rewrite <- (mult_assoc (/(/x) * (/x)) x (/x)).
 rewrite <- (mult_assoc (/(/x)) (/x) (x * /x)).
 rewrite (mult_assoc (/x) x (/x)).
 rewrite (inv_l x). rewrite one_unit_l.
 apply (inv_l (/x)).
rewrite (inv_l (/x)) in H. rewrite one_unit_l in H.
assumption.
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
intros x.
rewrite <- (one_unit_l (x * 1)).
assert(H: (/(/x) * (/x)) * (x * (/x * x)) = x).
 rewrite <- (mult_assoc (/(/x)) (/x) (x* (/x * x))).
 rewrite (mult_assoc (/(/x)) (/x) (x*(/x * x))).
 rewrite <- mult_assoc.
 rewrite (mult_assoc (/x) x (/x * x)).
 replace (/x * x * (/x * x)) with (1 * (/x * x)).
  rewrite one_unit_l. rewrite mult_assoc.
  rewrite inv_l. rewrite one_unit_l. reflexivity.
 rewrite (inv_l x). reflexivity. 
rewrite (inv_l x) in H. rewrite (inv_l (/x)) in H.
assumption.
Qed.

