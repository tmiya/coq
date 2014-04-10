Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
intros x y H.
apply (plus_lt_compat_r x y 10). assumption.
Qed.

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
