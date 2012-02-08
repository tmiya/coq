Section ExProp.


Proof.
Qed.

Proof.
Qed.

Goal P -> ~~P.
Proof.
Qed.

Goal (P -> Q) -> ~Q -> ~P.
Proof.
Qed.

Goal P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
Qed.

Goal P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
Qed.

Goal P -> ~P -> Q.
Proof.
Qed.

Goal (A \/ B -> C) -> (A -> C)/\(B -> C).
Proof.
Qed.

Goal (A \/ B -> C) -> (A -> C) \/ (B -> C).
Proof.
Qed.

Goal (A -> (B -> C)) /\ (A -> B) -> (A -> C).
Proof.
Qed.

Goal (~A /\ ~B) -> ~(A \/ (~A /\ B)).
Proof.
Qed.

Goal (A -> ~A) -> ~A.
Proof.
Qed.

Goal (~(A /\ A) -> (~A \/ ~A)).
Proof.
Qed.

Goal (A -> B) -> (A -> ~B) -> A -> C.
Proof.
Qed.

End ExProp.