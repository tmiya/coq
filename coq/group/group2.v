(** Group defined by one operation *)
(* Operator 'x/y' means xy^{-1}.
  Probe that '/' and four axioms obout it defines a group. *)

Section Group2.
Parameter G:Set.
(* G is not an empty set. At least one element exists. *)
Parameter g0:G. 
Parameter op:G->G->G.
Notation "a / b" := (op a b).
(* Axioms for / *)
Parameter G1: forall a b, a/a = b/b.
Parameter G2: forall a b, a/(b/b) = a.
Parameter G3: forall a b c, (a/a)/(b/c) = c/b.
Parameter G4: forall a b c, (a/c)/(b/c) = a/b.

Definition e:G := g0/g0.
Notation "1" := e.
Definition mult(a b:G) := (a/(1/b)).
Notation "a * b" := (mult a b).

Lemma op_refl_1 : forall a, a/a = 1.
Proof.
intro a. unfold "1". eapply G1.
Qed.

Lemma op_1 : forall a, a/1 = a.
Proof.
intro. unfold "1". rewrite G2. auto.
Qed.

Theorem left_id : forall a, 1*a = a.
Proof.
intro. unfold "1". unfold "*".
erewrite G3. eapply op_1.
Qed.

Theorem right_id : forall a, a*1 = a.
Proof.
intro. unfold "*". erewrite op_1.
erewrite op_1. auto.
Qed.

Definition inv(a:G) := (1/a).
Notation "! a" := (inv a) (at level 91).

Theorem left_inv : forall a, (!a)*a=1.
Proof.
intros. unfold "!". unfold "*".
rewrite G4. erewrite op_1. auto.
Qed.

Lemma inv_inv : forall a, 1/(1/a) = a.
Proof.
intros.
replace (1/(1/a)) with (1/1/(1/a)).
 rewrite G3. eapply op_1.
erewrite op_1. auto.
Qed.

Theorem right_inv : forall a, a*(!a)=1.
Proof.
intros. unfold "!". unfold "*".
erewrite inv_inv. eapply op_refl_1.
Qed.

Lemma inv_op : forall a b, inv (a/b) = b/a.
Proof.
intros. unfold "!". unfold "1".
erewrite G3. auto.
Qed.

Lemma inv_idem : forall a, inv (inv a) = a.
Proof.
intros. unfold "!". eapply inv_inv.
Qed.

Lemma op_eq : forall a b c d,
 a/b = c/d -> b/a = d/c.
Proof.
intros.
replace (b/a) with (1/1/(a/b)).
 replace (d/c) with (1/1/(c/d)).
  rewrite H. auto.
 erewrite G3. auto.
erewrite G3. auto.
Qed.

Lemma op_mult : forall a b, (a/b)*b = a.
Proof.
intros. unfold "*". erewrite G4.
eapply op_1.
Qed.

Lemma rm_op_2 : forall a b c, a/c=b/c -> a=b.
Proof.
intros. assert(a/c*c = b/c*c).
 rewrite H. auto.
erewrite op_mult in H0.
erewrite op_mult in H0. auto.
Qed.

Lemma rm_op_1 : forall a b c, a/b=a/c -> b=c.
Proof.
intros. specialize(op_eq a b a c H). intro.
eapply (rm_op_2 b c a H0).
Qed.

Lemma mult_op : forall a b, (a*b)/b = a.
Proof.
intros. unfold "*".
replace (a/(1/b)/b) with (a/(1/b)/(1/(1/b))).
rewrite G4. rewrite op_1. auto.
replace (1/(1/b)) with b. auto.
erewrite inv_inv. auto.
Qed.

Lemma assoc_2 : forall a b c, a/(b/c) = a*c/b.
intros.
replace (a/(b/c)) with ((a*c)/c/(b/c)).
rewrite G4. auto.
rewrite mult_op. auto.
Qed.

Lemma assoc_3 : forall a b c, a*(c/b) = a*c/b.
intros. 
replace (a*(c/b)) with (a/(inv (c/b))).
unfold "!". replace (1/(c/b)) with (b/c).
rewrite assoc_2. auto.
replace (1/(c/b)) with (1/1/(c/b)).
rewrite G3. auto. rewrite op_1. auto.
unfold inv. unfold "*". auto.
Qed.

Lemma assoc_4 : forall a b c, a*(c*(inv b)) = a*c*(inv b).
intros. unfold inv.
replace (c*(1/b)) with (c/b).
replace (a*c*(1/b)) with (a*c/b).
eapply assoc_3.
unfold "*". rewrite inv_inv. auto.
unfold "*". rewrite inv_inv. auto.
Qed.

Theorem assoc : forall a b c, a*(b*c) = a*b*c.
intros.
replace c with (inv (inv c)).
eapply assoc_4.
eapply inv_idem.
Qed.
End Group2.