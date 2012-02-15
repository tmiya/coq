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
 intros. assumption.
intros. simpl in H1. destruct H1.
 rewrite H1. eapply in_or_app. right. 
 eapply in_or_app. left. simpl. left. reflexivity.
remember (gt_A x a). destruct b.
 eapply in_or_app. left. eapply H. eapply filter_In. split; auto.
eapply in_or_app. right. eapply in_or_app. right.
eapply H0. eapply filter_In. split.
 assumption.
unfold le_A. rewrite <- Heqb. simpl. reflexivity.
Qed.

Lemma qsort_In2 : forall (l:list A)(x:A), In x (qsort l) -> In x l. 
intros l a. eapply qsort_ind.
 intros. assumption.
intros.
specialize (in_app_or (qsort (filter (gt_A x) xs))  ((x :: nil) ++ qsort (filter (le_A x) xs)) a H1).
intro. destruct H2.
 specialize (H H2). specialize filter_In. intro.
 specialize (H3 A (gt_A x) a xs). destruct H3. specialize (H3 H).
 destruct H3. simpl. right. assumption.
specialize (in_app_or (x::nil) (qsort (filter (le_A x) xs)) a H2). intro.
destruct H3.
 simpl. left. simpl in H3. destruct H3.
  assumption.
 elim H3.
specialize (H0 H3). specialize (filter_In (le_A x) a xs). intro.
destruct H4. specialize (H4 H0). destruct H4.
simpl. right. assumption.
Qed.

Lemma length_filter_sum : forall (a:A)(l:list A), 
  length (filter (gt_A a) l) + length (filter (le_A a) l) = length l.
Proof.
induction l.
 simpl. reflexivity.
simpl. unfold le_A in *. destruct (gt_A a a0); simpl; omega.
Qed.

Theorem length_of_qsort : forall l:list A, length l = length (qsort l).
Proof.
intro l. eapply qsort_ind.
 intros. simpl. auto.
intros. repeat rewrite app_length.
rewrite <- H. rewrite <- H0.
specialize (length_filter_sum x xs). intro.
simpl. omega.
Qed.

End QuickSort.