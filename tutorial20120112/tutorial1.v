(* If you cannot read Kanji characters in CoqIDE,
  Edit -> Preferences -> Fonts -> fonts includes Kanji-code *)

(** * 3. Coq でのプログラミング *)
(* コメントは (* ... *) の形式で書く. ネストも可能 *)

(** 定義の方法と定義の確認方法　*)
(* Module は定義のスコープを作る仕組み. Coq入門コースでは説明しない。*)
Module Section3_0.

(* x を 1 と定義する。Definition コマンドと := を使う. *)
Definition x := 1.

(* 定義されたものの型を確認するコマンドは Check. *)
Check x.

(* 定義の内容を確認するときは Print. *)
Print x.

(* x を再定義は出来ないのでエラーになるはず.
エラーを確認したら、行を削除するかコメント化して先に進め. *)
Definition x := 2.

(* 定義のスコープを閉じる *)
End Section3_0.

(* もう x は見つからないことを、確認せよ. 
エラーを確認したら、行を削除するかコメント化して先に進め. *)
Check x.

(** 関数の定義の方法 *)
(* 関数 f を定義。引数宣言に括弧は不要。 *) 
Definition f x y := x - y.

(* f の型を確認せよ. *)
Check f.

(* f' y = f 3 y と部分適用 *)
Definition f' := f 3.

(* f' の型を確認せよ. *)
Check f'.

(* 値を評価するときは Eval compute in ... を使う. *)
Eval compute in (f' 1).

(** 無名関数の定義方法 *)
Check (fun x => 2*x).

(* 無名関数を使って計算. *)
Eval compute in ((fun x => 2*x) 3).

(* 無名関数を使って定義も出来る. *)
Definition double := (fun x => 2*x).
Check double.

(** 高階関数の定義方法 *)
(* twice は f を２回適用する関数を返す. *)
Definition twice(f:nat->nat):nat->nat :=
  fun x => f (f x).

(* 5 を足す関数. *)
Definition add5(x:nat) := x + 5.

(* 5 を２回足す関数 *)
(* 関数名とかは C と同じく snake-case が普通 *)
Definition twice_add5 := twice add5.

(* 評価 *)
Eval compute in (twice_add5 2).

(* 下の様に書いてもOK. *)
Eval compute in (twice add5 2).

(** 3.1 ユーザ定義の型 *)
Module Section3_1.
(* ユーザ定義の型を作るときは Inductive を使う. *)
(* 改行やインデントには意味はないので見やすく整形すれば良い *)
Inductive Weekday : Set :=
  Sun | Mon | Tue | Wed | Thr | Fri | Sat.

(* Sun の型は? *)
Check Sun.

(* Weekdayという型の型は? *)
Check Weekday.

(** ユーザ定義の型への関数. 型推論してくれている。*)
Definition nextday d :=
match d with
| Sun => Mon
| Mon => Tue
| Tue => Wed
| Wed => Thr
| Thr => Fri
| Fri => Sat
| Sat => Sun
end.

(* nextday という関数の型は? *)
Check nextday.

(* 値を計算 *)
Eval compute in (nextday Mon).

(* 課題：nextday を参考にして prevday を同様に定義せよ. *)

(* 動作確認は下記の様に実施せよ *)
Eval compute in (prevday Wed).

(* Boolを定義してみる. *)
Inductive Bool : Set :=
| tru : Bool
| fls : Bool.

(* _ は wildcard で、全てにマッチ *)
Definition And(b1 b2:Bool):Bool :=
match b1,b2 with
| tru,tru => tru
| _,_ => fls
end.

(* 課題：Or, Not を同様に定義せよ.
結果は下記で目視確認せよ. *)

Eval compute in (Or tru tru). (* = tru *)
Eval compute in (Or tru fls). (* = tru *)
Eval compute in (Or fls tru). (* = tru *)
Eval compute in (Or fls fls). (* = fls *)
Eval compute in (Not tru). (* = fls *)
Eval compute in (Not fls). (* = tru *)

(** ライブラリのbool型 *)
Print bool.
Print andb.
Print orb.
Print negb.

Eval compute in (andb true false).

(**　unit型にはttという値がただ一つある *)
Print unit.

(** De Morgan 則を証明してみる *)
Theorem De_Morgan_1 : forall b1 b2,
  Not (And b1 b2) = Or (Not b1) (Not b2).
intros.
destruct b1; destruct b2.
simpl.  reflexivity.
auto.
auto.
auto.
Qed.

(* Admitted. を消して、同様に試してみよ *)
Theorem De_Morgan_2 : forall b1 b2,
  Not (Or b1 b2) = And (Not b1) (Not b2).
Admitted.

(** 課題１：３値論理 *)
(* 1. Yes, Maybe, No の３つの値を持つ型 Bool3 を定義せよ *)

(* 2. Bool3 に対する And3, Or3, Not3 を適切に定義せよ *)

(* 定義が適切か下記を用いて確認せよ *)

Eval compute in (And3 Yes Yes).  (* = Yes *)
Eval compute in (And3 Maybe Yes).  (* = Maybe *)
Eval compute in (And3 Yes No).  (* = No *)
Eval compute in (And3 No Maybe).  (* = No *)
Eval compute in (Or3 No No).  (* = No *)
Eval compute in (Or3 Maybe No).  (* = Maybe *)
Eval compute in (Or3 Yes No).  (* = Yes *)
Eval compute in (Or3 Yes Maybe).  (* = Yes *)
Eval compute in (Not3 Yes). (* = No *)
Eval compute in (Not3 Maybe). (* = Maybe *)
Eval compute in (Not3 No). (* = Yes *)

(* 3. Bool3 に対する De Morgan 則を証明せよ *) 
Theorem De_Morgan_1' : forall b1 b2,
  Not3 (And3 b1 b2) = Or3 (Not3 b1) (Not3 b2).
Proof.
(* ここに証明を書く *)
Qed.

Theorem De_Morgan_2' : forall b1 b2,
  Not3 (Or3 b1 b2) = And3 (Not3 b1) (Not3 b2).
Proof.
(* ここに証明を書く *)
Qed.

End Section3_1.
