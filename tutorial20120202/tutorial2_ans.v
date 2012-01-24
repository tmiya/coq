(** * 3. Coq でのプログラミング *)
(** 3.2 再帰的な型と関数 *)
Module Section3_2.

(** 自然数 nat について *)
Print nat.
(* Inductive nat : Set :=  
   O : nat 
 | S : nat -> nat 
*)

Eval compute in (S (S (S O))).

(** 自然数の加法 *)
Fixpoint add(n m:nat):nat :=
match n with
| O => m
| S n' => S (add n' m)
end.

Eval compute in (add (S (S O)) (S (S (S O)))).

(** 自然数の比較 *)
Fixpoint eq_nat(n m:nat):bool :=
match n,m with
| O,O => true
| S n', S m' => eq_nat n' m'
| _,_ => false
end.

Eval compute in (eq_nat 3 3).
Eval compute in (eq_nat 3 2).

Fixpoint le_nat(n m:nat):bool :=
match n,m with
| O,_ => true
| S n,O => false
| S n',S m' => le_nat n' m'
end.

Eval compute in (le_nat 2 3).  (* = true *) 
Eval compute in (le_nat 3 3).  (* = true *)
Eval compute in (le_nat 4 3).  (* = false *)

(** 再帰関数の停止性 *)
Fixpoint add'(n m:nat){struct n}:nat :=
match n with
| O => m
| S n' => S (add n' m)
end.

(** 課題２：自然数の関数 *)
(* 1. 掛け算を行う関数 mul を add を参考に定義せよ。 *)
Fixpoint mul(n m:nat) :=
match n with
| O => O
| S n' => add m (mult n' m)
end.

Eval compute in (mul 2 3). (* = 6 *)

(* 2. mul を用いて階乗を計算する関数 fact を定義せよ。*)
Fixpoint fact(n:nat) :=
match n with
| O => 1
| S n' => mult n (fact n')
end.

Eval compute in (fact 4). (* = 24 *)

(* 3. 引き算を行う関数 sub を定義してみよ。但し n = 0 の場合は sub 0 m = 0と定義する。*)
Fixpoint sub(n m:nat):nat :=
match n,m with
| O,_ => O
| _,O => n
| S n',S m' => sub n' m'
end.

Eval compute in (sub 5 2). (* = 3 *)
Eval compute in (sub 4 4). (* = 0 *)
Eval compute in (sub 2 5). (* = 0 *)

(* 4. 次の関数 div3 は何を計算する関数か考えよ。また Eval を用いて 動作を確認してみよ。*)
Fixpoint div3(n:nat) :=
match n with
| S (S (S n')) => S (div3 n')
| _ => O
end.

Eval compute in (div3 2).
Eval compute in (div3 6).
Eval compute in (div3 7).

End Section3_2.

(** 3.3 多相型 *)
Module Section3_3. 

(** 多相型とは *)
Definition cond{A:Set}(c:bool)(vt vf:A) : A :=
match c with
| true => vt
| false => vf
end.

Eval compute in (cond true 2 3).
Eval compute in (cond false false true).
Eval compute in (@cond nat false 2 3).

(** option型 *)
Print option.
(* Inductive option (A : Type) : Type :=  Some : A -> option A | None : option A *)

Definition option_map {A B:Type}(f:A->B)(o:option A) :=
match o with
| Some a => Some (f a)
| None => None
end.

Eval compute in (option_map (fun x => x+1) (Some 1)).
Eval compute in (option_map (fun x => x+1) None).

(** prod型とsum型 *)

Print prod.
(* Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B *)

Print sum.
(* Inductive sum (A B : Type) : Type :=  inl : A -> A + B | inr : B -> A + B *)

Check (2,true,3).

Definition test_sum(s:sum nat bool) :=
match s with
| inl n => n
| inr true => 1
| inr false => 0
end.

(** List型 *)
Require Import List.
Print list.
(* Inductive list (A : Type) : Type :=
    nil : list A 
  | cons : A -> list A -> list A
*)

Check (1::2::nil).

(** List に対する再帰関数 *)
(* Listの連結 *)
Fixpoint append{A:Type}(xs ys:list A):=
match xs with
| nil => ys
| x::xs' => x::(append xs' ys)
end.
Eval compute in (append (1::2::nil) (3::4::nil)).

(* Listの最後の要素 *)
Fixpoint olast{A:Type}(xs:list A):option A :=
match xs with
| nil => None
| a::nil => Some a
| _::xs' => olast xs'
end.
Eval compute in (olast (1::2::3::nil)).
Eval compute in (olast (1::nil)).
Eval compute in (olast (@nil nat)).

(** 課題３：Listへの関数 *)
(* 1. リストの長さを与える関数 len{A:Type}(xs:list A):nat を定義 せよ。*)
Fixpoint len{A:Type}(xs:list A):nat :=
match xs with
| nil => O
| _::xs' => S (len xs')
end.

Eval compute in (len (1::2::3::nil)). (* = 3 *)

(* 2. list bool の入力を受け取り、全要素が true の時 true を返す関数
 all_true(xs:list bool):bool を定義せよ。
但し nil に対し ては true を返すとせよ。*)
Fixpoint all_true(xs:list bool):bool :=
match xs with
| nil => true
| x::xs' => andb x (all_true xs')
end.
Eval compute in (all_true (@nil bool)).  (* = true *)
Eval compute in (all_true (true::true::nil)).  (* = true *)
Eval compute in (all_true (true::true::false::nil)).  (* = false *)

(* 3. リストの先頭要素 x があれば Some x を、空リストに対しては 
None を返す、関数 ohead{A:Type}(xs:list A):option A を
定義せよ。*)
Definition ohead{A:Type}(xs:list A):option A :=
match xs with
| nil => None
| a::_ => Some a
end.

Eval compute in (ohead (@nil nat)).  (* = None *)
Eval compute in (ohead (1::nil)).  (* = Some 1 *)
Eval compute in (ohead (1::2::nil)).  (* = Some 1 *)

(* 4. 自然数s,nに対してs :: s+1 :: ... :: (s+n-1) :: nilを
 返す関数 nat_list(s n:nat):list nat を定義せよ。*)
Fixpoint nat_list(s n:nat):list nat :=
match n with
| O => nil
| S n' => s::(nat_list (S s) n')
end.

Eval compute in (nat_list 3 5).  (* = 3::4::5::6::7::nil *)

(* 5. リストを反転する関数 reverse{A:Type}(xs:list A):list A を
 定義せよ。必要なら append を使え。*)
Fixpoint reverse{A:Type}(xs:list A):list A :=
match xs with
| nil => nil
| x::xs' => append (reverse xs') (x::nil)
end.

Eval compute in (reverse (1::2::3::nil)). (* =  3::2::1::nil *)

End Section3_3.
