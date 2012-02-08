Section ExProp.
Variable A B C D P Q R S:Prop.
Goal (P -> Q) -> (Q -> R) -> P -> R.
Proof.
intros pq qr p.
apply qr. apply pq. exact p.
Qed.
Goal ~False.
Proof.
intro H. exact H.
Qed.

Goal P -> ~~P.
Proof.
intro p. intro np. elim np. exact p.
Qed.

Goal (P -> Q) -> ~Q -> ~P.
Proof.
intros pq nq. intro p.
elim nq. apply pq. exact p.
Qed.

Goal P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
intro pqr. destruct pqr as [p [q r]].
split.
 split.
  exact p.
  exact q.
 exact r.
Qed.

Goal P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
intro pqr.
destruct pqr as [p [q|r]].
 left. split.
  exact p.
  exact q.
 right. split.
  exact p.
  exact r.
Qed.

Goal P -> ~P -> Q.
Proof.
intros p np. elim np. exact p.
Qed.

Goal (A \/ B -> C) -> (A -> C)/\(B -> C).
Proof.
intro abc.
split.
 intro a. apply abc. left. exact a.
 intro b. apply abc. right. exact b.
Qed.

Goal (A \/ B -> C) -> (A -> C) \/ (B -> C).
Proof.
intro abc.
 left. intro a. apply abc. left. exact a.
Qed.

Goal (A -> (B -> C)) /\ (A -> B) -> (A -> C).
Proof.
intros H a. destruct H as [abc ab].
apply abc.
 exact a.
 apply ab. exact a.
Qed.

Goal (~A /\ ~B) -> ~(A \/ (~A /\ B)).
Proof.
intro nanb. intro anab.
destruct nanb as [na nb].
destruct anab as [a|[na' b]].
 elim na. exact a.
 elim nb. exact b.
Qed.

Goal (A -> ~A) -> ~A.
Proof.
intro ana. intro a. elim ana.
 exact a.
 exact a.
Qed.

Goal (~(A /\ A) -> (~A \/ ~A)).
Proof.
intro naa. left. intro a. elim naa.
split.
 exact a.
 exact a.
Qed.

Goal (A -> B) -> (A -> ~B) -> A -> C.
Proof.
intros ab anb a. elim anb.
 exact a.
 apply ab. exact a.
Qed.

End ExProp.