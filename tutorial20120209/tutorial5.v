Require Import Arith.
Require Import Omega.

(* Inductive predicate *)
Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS : forall n, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
| odd_1 : odd 1
| odd_SS : forall n, odd n -> odd (S (S n)).

Theorem even_double : forall n, even (n + n).
Proof.
induction n.
(* Proof *)
Qed.

Theorem even_plus : forall m n, even m -> even n -> even (m + n).
Proof.
intros m n Hm Hn.
induction Hm.
(* Proof *)
Qed.

Theorem not_even_1 : ~even 1.
Proof.
intro. inversion H.
Qed.

Theorem even_SS_inv : forall n, even (S (S n)) -> even n.
Proof.
intros n H.
(* Proof *)
Qed.

Theorem even_odd : forall n, even n -> odd (S n).
Proof.
intros n H.
induction H.
(* Proof *)
Qed.

Theorem odd_even : forall n, odd n -> even (S n).
Proof.
(* Proof *)
Qed.

Theorem even_not_odd : forall n, even n -> ~odd n.
Proof.
(* Proof *)
Qed.

Theorem even_or_odd : forall n, even n \/ odd n.
Proof.
intro n.
induction n.
 left. apply even_0.
induction n. 
(* Proof. even_odd and odd_even are useful. *)
Qed.

Theorem odd_odd_even : forall m n, odd m -> odd n -> even (m + n).
Proof.
intros m n Hm Hn.
induction Hm.
 induction Hn.
(* Proof. *)
Qed.

Section List_inversion.

Require Import List.

Variable A:Type.

Theorem app_inv_l : forall l l1 l2:list A,
  l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
(* Proof. *)
Qed.

Check app_nil_r.
Check app_cons_not_nil.

Lemma app_cons_assoc : forall (a:A)(l1 l2:list A),
  l1 ++ a::l2 = (l1 ++ a::nil) ++ l2.
Proof.
(* Proof. *)
Qed.

Lemma app_snoc_inv : forall (a:A)(l1 l2:list A),
  l1 ++ a::nil = l2 ++ a::nil -> l1 = l2.
Proof.
(* Proof. *)
Qed.

Theorem app_inv_r : forall l l1 l2:list A,
  l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
(* Proof. *)
Qed.

Check app_inv_l.
End List_inversion.
Check app_inv_l.
