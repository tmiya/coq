(* Hand is defined inductively. *)
Inductive Hand : Set := Gu | Tyoki | Pa.

(* Check type of Hand. *)
Check Hand.

(* Show definitions. *)
Print Hand.
Print Hand_ind.

(* Function definition *)
Inductive win : Hand -> Hand -> Prop :=
| gu_win_tyoki : win Gu Tyoki
| tyoki_win_pa : win Tyoki Pa
| pa_win_gu : win Pa Gu.

Hint Constructors win.
(* Winning hand *)
Definition winning_hand(s:Hand) : { a | win a s }.
Proof.
induction s.
 exists Pa. apply pa_win_gu.
 exists Gu. auto.
 exists Tyoki; auto.
Defined.

(* Result = hand & proof *)
Eval compute in (winning_hand Gu).
(* Hand *)
Eval compute in (proj1_sig (winning_hand Gu)).
(* Proof *)
Eval compute in (proj2_sig (winning_hand Gu)).
(* Extract as OCaml program *)
Extraction winning_hand.

(* Winning hand is unique. *)
Theorem winning_hand_unique : forall a b c, 
  win a c -> win b c -> a = b.
Proof.
intros a b c Hac Hbc. induction c.
 inversion Hac. inversion Hbc. reflexivity.
 inversion Hac. inversion Hbc. auto.
 inversion Hac; inversion Hbc; auto.
Qed.

(* Import List module *)
Require Import List.

(* Show definition of list type *)
Print list.

(* Sample of list *)
Check (1::2::nil).

Check list_ind.

(* Define append function *)
Fixpoint append{A:Type}(xs ys:list A):=
match xs with
| nil => ys
| x::xs' => x::(append xs' ys)
end.

(* Evaluation *)
Eval compute in (append (1::2::nil) (3::4::nil)).

(* Definition of nat *)
Print nat.
Print plus.

(* Write your length function *)
Fixpoint len{A:Type}(xs:list A):nat :=
match xs with
| nil => ??????
| x::xs' => ???????
end.

(* Should be 3 *)
Eval compute in (len (1::2::3::nil)).

Theorem len_append: forall (A:Type)(xs ys:list A),
  len (append xs ys) = plus (len xs) (len ys).  
Proof.
intro A.
induction xs.
 simpl.
 intro ys. auto.

 intro ys. simpl.
 erewrite IHxs.
 auto.
Qed.

Fixpoint reverse{A:Type}(xs:list A):list A :=
match xs with
| nil => nil
| x::xs' => append (reverse xs') (x::nil)
end.

(* Evaluate *)
Eval compute in (reverse (1::2::3::nil)).
(* reverse twice *)
Eval compute in (reverse (reverse (1::2::3::nil))).

Lemma append_right_nil: forall (A:Type)(xs:list A),
  append xs nil = xs.
Proof.
????
Qed.

Lemma append_append : forall (A:Type)(xs ys zs:list A),
  append (append xs ys) zs = append xs (append ys zs).
Proof.
????
Qed. 

Lemma reverse_append : forall (A:Type)(xs ys:list A),
  reverse (append xs ys) = append (reverse ys) (reverse xs).
Proof.
????
Qed.

Theorem reverse_reverse: forall (A:Type)(xs:list A),
  reverse (reverse xs) = xs.
Proof.
????
Qed.

