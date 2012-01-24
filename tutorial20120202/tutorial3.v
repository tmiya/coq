(** -> を含む証明 *)
Module Section4.

Section imp_sample.
Variables P Q R:Prop.
Theorem imp_sample : (P -> (Q -> R)) -> (P -> Q) -> P -> R.
Proof.
  (* 最初は intro(s) してゴールの -> を無くす *)
  intros pqr pq p.
  (* ゴールの R を得られそうなのは pqr *)
  apply pqr.
    (* ゴール = P. そのままの仮定があれば assumption *)
    assumption.
    (* ゴール = Q. pq を使えば Q が得られそう *)
    apply pq.  assumption.
Qed.

(** 4.2 /\ を含む証明 *)
Theorem and_assoc : (P/\Q)/\R -> P/\(Q/\R).
Proof.
  intro pqr.
  (* (P/\Q)/\R を分解する *)
  destruct pqr as [[p q] r].
  (* ゴールの P/\(Q/\R) を P と Q/\R に分解 *)
  split.
    (* ゴール P *)
    assumption.
    (* ゴール Q /\ R。 split. assumption. assumption. でも OK *)
    split; assumption.
Qed.

(** 4.3 \/ を含む証明 *)
Theorem or_assoc : (P\/Q)\/R -> P\/(Q\/R).
Proof.
  intro pqr.
  (* (P\/Q)\/R を分解する *)
  destruct pqr as [[p|q]|r].
    (* 仮定 p:P *)
    left. assumption.
    (* 仮定 q:Q *)
    right. left. assumption.
    (* 仮定 r:R *)
    right; right.  assumption.
Qed.

(** 4.4 ~を含む証明 *)
Print False.

Theorem neg_sample : ~(P /\ ~P).
Proof.
  (* ~で始まるゴールは intro *)
  intro.
  destruct H as [p np].
  (* ゴールが False なら ~で始まる仮定を elim *)
  elim np.
  assumption.
Qed.

End imp_sample.
(** 課題４：命題論理の証明 *)
(* 証明せよ *)
Section Ex4.
Variable A B C D:Prop. 
Theorem ex4_1 : (A -> C) /\ (B -> D) /\ A /\ B -> C /\ D. 
Proof.
(* Proof *)
Qed.

Theorem ex4_2 : ~~~A -> ~A. 
Proof.
(* Proof *)
Qed.

Theorem ex4_3 : (A -> B) -> ~B -> ~A. 
Proof.
(* Proof *)
Qed.

Theorem ex4_4 : ((((A -> B) -> A) -> A) -> B) -> B. 
Proof.
(* Proof *)
Qed.

Theorem ex4_5 : ~~(A\/~A).
Proof.
(* Proof *)
Qed.

End Ex4.
End Section4.
