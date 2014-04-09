(* Coq Exercise 1 / http://qnighy.github.io/coqex2014/ex1.html *)

Theorem tautology : forall P : Prop, P -> P.
Proof.
  intros P H.
  assumption.
Qed.

(*
Theorem wrong : forall P : Prop, P.
Proof.
  intros P.
Qed.
*)

Theorem Modus_ponens : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
intros P Q p pq.
apply pq. assumption.
Qed.

Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
Proof.
intros P Q H p.
destruct H as [nq pq].
apply nq. apply pq. assumption.
Qed.

Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
intros P Q pq np.
destruct pq as [p|q].
 elim np. assumption.
assumption.
Qed.

Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
intros P Q H pq. destruct pq as [p q].
destruct H as [np|nq].
 apply np. assumption.
apply nq. assumption.
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
intros P Q H pq. destruct H as [np nq].
destruct pq as [p|q].
 apply np. assumption.
apply nq. assumption.
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
intros P Q H. split.
 intro p. apply H. left. assumption.
intro q. apply H. right. assumption.
Qed.

Theorem NotNot_LEM : forall P : Prop, ~ ~(P \/ ~P).
Proof.
intros P H. apply H.
right. intro p. apply H. left. assumption.
Qed.
