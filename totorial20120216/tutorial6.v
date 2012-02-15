Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import List.

Section QuickSort.
Variable A:Set.
Variable cmp: A -> A -> comparison.

Lemma length_of_filter : forall (l:list A)(p:A->bool),
 length (filter p l) <= length l.
Proof.
induction l.
 intro p. simpl. omega.
intro p. simpl. destruct (p a).
 simpl. specialize (IHl p). omega.
simpl. specialize (IHl p). omega.
Qed.

Definition gt_A(a b:A):bool :=
match (cmp a b) with
| Gt => true
| _ => false
end.

Definition le_A(a b:A):bool := negb (gt_A a b).

Function qsort(l:list A){measure length l}:list A :=
match l with
| nil => nil
| x::xs => qsort (filter (gt_A x) xs) ++ (x::nil) ++ qsort (filter (le_A x) xs)
end.
Proof.
 intros. specialize (length_of_filter xs (le_A x)). intro.
 simpl. omega.
intros. specialize (length_of_filter xs (gt_A x)). intro.
simpl. omega.
Defined.

Check qsort_ind.
Check qsort_equation.

Lemma qsort_In1 : forall (l:list A)(x:A), In x l -> In x (qsort l).
Proof.
intros l a. eapply qsort_ind.
(* Proof. in_or_app and filter_In are useful. *)
Qed.

Lemma qsort_In2 : forall (l:list A)(x:A), In x (qsort l) -> In x l. 
Proof.
(* Proof. in_app_or and filter_In are useful. *)
Qed.

Lemma length_filter_sum : forall (a:A)(l:list A), 
  length (filter (gt_A a) l) + length (filter (le_A a) l) = length l.
Proof.
(* Proof *)
Qed.

Theorem length_of_qsort : forall l:list A, length l = length (qsort l).
Proof.
intro l. eapply qsort_ind.
(* Proof. app_length isuseful. *)
Qed.

End QuickSort.