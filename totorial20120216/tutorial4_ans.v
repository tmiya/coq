(** 6. 述語論理 *)
Module Section6.

(** 述語論理 *)
(* 述語 iszero:nat -> Prop *)
Definition iszero(n:nat):Prop :=
match n with
| O => True
| _ => False
end.

(* 動作確認 *)
Eval compute in (iszero 0).
Eval compute in (iszero 3).

(** forall がある場合 *)
Theorem sample_forall : forall (X:Type)(P Q:X->Prop)(x:X),
  P x -> (forall y:X, Q y) -> (P x /\ Q x).
Proof.
  (* 最初は intro(s) する。名前は判りやすく付けると良い *)
  intros X P Q x px Hqy.
  (* ゴールが /\ の形ならば split. する *)
  split.
    (* goal = P x *)
    assumption.
    (* goal = Q x. Hqy の forall y の y に x を代入 *)
    apply (Hqy x).
Qed.

Theorem sample_exists : forall (P Q:nat->Prop),
  (forall n, P n) -> (exists n, Q n) ->
  (exists n, P n /\ Q n).
Proof.
  intros P Q Hpn Hqn.
  (* exists の式は /\ と同様に destruct する *)
  destruct Hqn as [n' qn'].
  (* ゴールの exists n に具体的な n' という値を示す *)
  exists n'.
  split.
    (* 仮定 Hpn から P n' を得る *)
    apply (Hpn n').
    (* goal = Q n' *)
    assumption.
Qed.

(** 課題５：述語論理の証明 *)
Theorem ex5_1 : forall (A:Set)(P:A->Prop),
  (~exists a, P a) -> (forall a, ~P a).
Proof.
  intros A P nep a. intro pa.
  elim nep. exists a. assumption.
Qed.

Theorem ex5_2 : forall (A:Set)(P Q:A->Prop),
  (exists a, P a \/ Q a) ->
  (exists a, P a) \/ (exists a, Q a).
Proof.
  intros A P Q epqa.
  destruct epqa as [a [pa|qa]].
    left. exists a. assumption.
    right. exists a. assumption.
Qed.

Theorem ex5_3 : forall (A:Set)(P Q:A->Prop),
  (exists a, P a) \/ (exists a, Q a) ->
  (exists a, P a \/ Q a).
Proof.
  intros A P Q Hpq.
  destruct Hpq as [Hp|Hq].
    destruct Hp as [a pa]. exists a. left. assumption.
    destruct Hq as [a qa]. exists a. right. assumption.
Qed.

Theorem ex5_4 : forall (A:Set)(R:A->A->Prop),
  (exists x, forall y, R x y) -> (forall y, exists x, R x y).
Proof.
  intros A R H y.
  destruct H as [x Hy].
  exists x.  apply (Hy y).
Qed.

Theorem ex5_5 : forall (A:Set)(R:A->A->Prop),
  (forall x y, R x y -> R y x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  (forall x, exists y, R x y) ->
  (forall x, R x x).
Proof.
  intros A R Hsym Htrans Hex x.
  destruct (Hex x) as [y Rxy].
  apply (Htrans x y x).
    assumption.
    apply Hsym.  assumption.
Qed.

(** 6.3 =を含む証明 *)
(* =　は eq という名前で定義されている *)
Print eq.

Theorem plus_0_l : forall n, 0 + n = n.
Proof.
  intro n.
  (* 0 + n をplusの定義に従い簡単にする *)
  simpl.
  (* = の左辺と右辺が同じ形ならば reflexivity. *)
  reflexivity.
Qed.

(* simpl では簡単にならない例 *)
Theorem plus_0_r : forall n, n + 0 = n.
Proof.
  intro n.
  simpl.
Abort. (* 中断して破棄 *)

(* natに関する帰納法 *)
Check nat_ind.

(* 証明課題を無名関数にして渡した例 *)
Check (nat_ind (fun n => n + 0 = n)). 

(* boolに関する帰納法は、単なる場合分け *)
Check bool_ind.

Theorem plus_0_r : forall n, n + 0 = n.
Proof.
  (* n を O と S n' とに場合分けする *)
  induction n as [|n'].
    (* n=0 の場合 *)
    reflexivity.
    (* n=S n' の場合. 簡単にする *)
    simpl.
    (* ゴールに対して、IHn'の左辺->右辺と書き換え *)  
    rewrite IHn'.
    reflexivity.
Qed.

(** 課題６：n+m=m+nの証明 *)
SearchAbout plus.

(*
plus_n_O: forall n : nat, n = n + 0
plus_O_n: forall n : nat, 0 + n = n
plus_n_Sm: forall n m : nat, S (n + m) = n + S m
plus_Sn_m: forall n m : nat, S n + m = S (n + m)
mult_n_Sm: forall n m : nat, n * m + n = n * S m
plus_0_r: forall n : nat, n + 0 = n
plus_0_l: forall n : nat, 0 + n = n
*)

Theorem plus_comm : forall m n, m + n = n + m.
Proof.
  induction m as [|m'].
    (* m=0 *)
    intro n. simpl. rewrite <- plus_n_O. reflexivity.
    (* m=S m' *)
    intro n. simpl. rewrite <- plus_n_Sm. 
    rewrite IHm'. reflexivity.
Qed.

(* リストライブラリをインポート *)
Require Import List.
Theorem length_app : forall (A:Type)(l1 l2:list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
(* (1) 最初に全て intros する場合 *)
  intros A l1 l2.
  induction l1 as [|a l1'].
    simpl. reflexivity.
    (* ここでの IHl1'は、
IHl1' : length (l1' ++ l2) = length l1' + length l2 *)
    simpl. rewrite IHl1'. reflexivity.
Qed.
(* (2) 最初に全て l1 のみ intros する場合
  intros A l1.
  induction l1 as [|a l1'].
    intro l2. simpl. reflexivity.
    (* ここでの IHl1'は、任意の l2 に対する仮定
IHl1' : forall l2 : list A, 
  length (l1' ++ l2) = length l1' + length l2 *)
    intro l2. simpl. rewrite IHl1'. reflexivity.
Qed.
*)
(** 課題７：リストに関する証明 *)
Fixpoint append{A:Type}(l1 l2:list A) :=
match l1 with
| nil => l2
| a::l1' => a::(append l1' l2)
end.
(* 動作確認 *)
Eval compute in (append (1::2::3::nil) (4::5::nil)).

Fixpoint reverse{A:Type}(l:list A):=
match l with
| nil => nil
| a::l' => append (reverse l') (a::nil)
end.
(* 動作確認 *)
Eval compute in (reverse (1::2::3::4::nil)).

(* Lemma は補題の意味だが、Coq の処理としては Theorem と同じ *)
Lemma append_nil : forall (A:Type)(l:list A),
  append l nil = l.
Proof.
  intro A.
  induction l as [|a l'].
    simpl. reflexivity.
    simpl. rewrite IHl'. reflexivity.
Qed.

Lemma append_assoc : forall (A:Type)(l1 l2 l3:list A),
  append (append l1 l2) l3 = append l1 (append l2 l3).
Proof.
  intro A.
  induction l1 as [|a l1'].
    intros l2 l3. simpl. reflexivity.
    intros l2 l3. simpl. rewrite IHl1'. reflexivity.
Qed.

Lemma reverse_append : forall (A:Type)(l1 l2:list A),
  reverse (append l1 l2) = append (reverse l2) (reverse l1).
Proof.
  intro A.
  induction l1 as [|a l1'].
    intro l2. simpl. rewrite append_nil. reflexivity.
    intro l2. simpl. rewrite IHl1'.
    rewrite append_assoc. reflexivity.
Qed.

Theorem reverse_reverse : forall (A:Type)(l:list A),
  reverse (reverse l) = l.
Proof.
  intro A.
  induction l as [|a l'].
    simpl. reflexivity. 
    simpl. rewrite reverse_append. rewrite IHl'.
    simpl. reflexivity. 
Qed.
End Section6.

