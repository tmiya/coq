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
 simpl. apply even_0.
replace (S n + S n) with (S (S (n + n))) by omega.
eapply even_SS. assumption.
Qed.

Theorem even_plus : forall m n, even m -> even n -> even (m + n).
Proof.
intros m n Hm Hn.
induction Hm.
 simpl. assumption.
simpl. apply even_SS. auto.
Qed.

Theorem not_even_1 : ~even 1.
Proof.
intro. inversion H.
Qed.

Theorem even_SS_inv : forall n, even (S (S n)) -> even n.
Proof.
intros n H. inversion H. assumption.
Qed.

Theorem even_odd : forall n, even n -> odd (S n).
Proof.
intros n H.
induction H.
 apply odd_1.
eapply odd_SS. auto.
Qed.

Theorem odd_even : forall n, odd n -> even (S n).
Proof.
intros n H.
induction H.
 apply even_SS. apply even_0.
eapply even_SS. assumption.
Qed.

Theorem even_not_odd : forall n, even n -> ~odd n.
Proof.
intros n H. 
induction H.
 intro. inversion H.
intro. elim IHeven.
inversion H0. assumption.
Qed.

Theorem even_or_odd : forall n, even n \/ odd n.
Proof.
intro n.
induction n.
 left. apply even_0.
induction n. 
 right. apply odd_1.
destruct IHn.
 right. eapply even_odd. assumption.
left. eapply odd_even. assumption.
Qed.

Theorem odd_odd_even : forall m n, odd m -> odd n -> even (m + n).
Proof.
intros m n Hm Hn.
induction Hm.
 induction Hn.
  simpl. apply even_SS. apply even_0.
 replace (1 + S (S n)) with (S (S (1+n))) by omega.
 apply even_SS. assumption.
replace (S (S n0) + n) with (S (S (n0 + n))) by omega.
apply even_SS. assumption.
Qed.


Section List_inversion.
Require Import List.

Variable A:Type.

Theorem app_inv_l : forall l l1 l2:list A,
  l ++ l1 = l ++ l2 -> l1 = l2.
Proof.
induction l.
 simpl. intros. auto.
simpl. intros. inversion H. eapply IHl. auto.
Qed.

Check app_nil_r.
Check app_cons_not_nil.

Lemma app_cons_assoc : forall (a:A)(l1 l2:list A),
  l1 ++ a::l2 = (l1 ++ a::nil) ++ l2.
Proof.
induction l1. 
 intros. simpl. auto.
intros. simpl. erewrite IHl1. auto. 
Qed.

Lemma app_snoc_inv : forall (a:A)(l1 l2:list A),
  l1 ++ a::nil = l2 ++ a::nil -> l1 = l2.
Proof.
induction l1.
 intros. induction l2.
  auto.
 simpl in H. inversion H.
 specialize(app_cons_not_nil l2 nil a0). intro.
 elim H0. auto.
induction l2.
 intro. simpl in H. inversion H.
 specialize(app_cons_not_nil l1 nil a). intro.
 elim H0. auto.
intro. simpl in H. inversion H.
rewrite H1 in *. specialize(IHl1 _ H2). rewrite IHl1 in *.
auto.
Qed.

Theorem app_inv_r : forall l l1 l2:list A,
  l1 ++ l = l2 ++ l -> l1 = l2.
Proof.
induction l.
 intros. repeat erewrite app_nil_r in H. auto.
intros.
rewrite (app_cons_assoc a l1 l) in H. 
rewrite (app_cons_assoc a l2 l) in H.
specialize (IHl _ _ H).
eapply app_snoc_inv. apply IHl.
Qed.

Check app_inv_l.
End List_inversion.
Check app_inv_l.
