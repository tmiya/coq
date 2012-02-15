(****************************************************************
 
   ACGT.v
 
   ...mathink
 
 ****************************************************************)
 
Require Import Arith.
Require Import List.
 
Set Implicit Arguments.
 
Notation "[ A ]" := (A::nil).
Notation "[ X , .. , Y ]" := (X:: .. (Y::nil) ..).
 
 
(*
   all_cons...
   
   a, (l1, l2, ... , ln) ~~> (a::l1, a::l2, ... , a::ln) 
*)
Fixpoint all_cons (A: Set)(a: A)(ll: list (list A)) :=
  match ll with
    | h::t => (a::h)::(all_cons a t)
    | nil => nil
  end.
 
Lemma all_cons_length:
  forall (A: Set)(a: A) l ll,
    In l (all_cons a ll) -> 1 <= length l.
Proof.
  intros A a l ll.
  generalize a l; clear a l.
  elim ll; clear ll.
  simpl; intros; contradiction.
  simpl.
  intros l ll IH a l' [Heq | HIn].
  subst; simpl; auto with arith.
  apply IH with a; assumption.
Qed.
 
Lemma all_cons_In_gen:
  forall (A: Set)(a b: A) l ll,
    In (a::l) (all_cons b ll) -> a=b/\In l ll.
Proof.
  intros A a b l ll.
  elim ll; clear ll.
  simpl; intros; contradiction.
  simpl.
  intros hl ll IH [Heq | HIn].
  injection Heq; intros; subst; split;
    [reflexivity | simpl; left; reflexivity].
  split.
  destruct (IH HIn) as [Heq _]; assumption.
  right; destruct (IH HIn) as [_ H]; assumption.
Qed.
 
(* 出番がない *)
Lemma all_cons_In:
  forall (A: Set)(a: A) l ll,
    In (a::l) (all_cons a ll) -> In l ll.
Proof.
  intros.
  destruct (all_cons_In_gen _ _ _ _ H) as [_ HIn].
  assumption.
Qed.
(* *)
 
Lemma all_cons_In_inv:
  forall (A: Set)(a: A) l ll,
    In l ll -> In (a::l) (all_cons a ll).
Proof.
  intros A a l ll; elim ll; clear ll.
  simpl; intros; contradiction.
  simpl; intros hl ll IH [Heq | HIn].
  subst; left; reflexivity.
  right; apply IH; assumption.
Qed.
 
 
(*
   DNA_base...
 
   Adenine Cytosine Guanine Thymine
*)
Inductive base :=
| A | C | G | T.
 
Definition ACGT := [A,C,G,T].
 
Definition base_all_cons (ll: list (list base)) :=
  (all_cons A ll)++(all_cons C ll)++(all_cons G ll)++(all_cons T ll).
 
Lemma bac_length:
  forall l ll,
    In l (base_all_cons ll) -> 1 <= length l.
Proof.
  unfold base_all_cons.
  intros l ll HIn.
  repeat rewrite in_app_iff in HIn.
  destruct HIn as [HIn | [HIn | [HIn | HIn]]];
    generalize HIn; clear HIn; apply all_cons_length.
Qed.
 
 
(*
   generate...
   
   list of (list base) including all n-length list
   ...generate_correct
*)
Fixpoint generate (n: nat): list (list base) :=
  match n with
    | O => [nil]
    | 1 => [[A],[C],[G],[T]]
    | S p => base_all_cons (generate p)
  end.
 
Eval compute in (generate 2).
Eval compute in (length (generate 2)).
 
Lemma generate_length:
  forall n l,
    In l (generate n) -> length l = n.
Proof.
  intro n; elim n; clear n.
  simpl.
  intros l [Heq | F]; [subst; simpl; reflexivity | contradiction].
  intro n; case n; clear n.
  intros IH l [Heq | [Heq | [Heq | [Heq | F]]]]; subst; try contradiction;
    simpl; reflexivity.
  intros n IH l; case l; clear l.
  simpl.
  intro HIn.
  apply bac_length in HIn.
  elim (le_Sn_0 _ HIn).
  intros b l HIn.
  simpl.
  apply eq_S; apply IH.
  simpl in HIn; unfold base_all_cons in HIn.
  repeat rewrite in_app_iff in HIn.
  destruct HIn as [HIn | [HIn | [HIn | HIn]]];
    generalize HIn; clear HIn; case b; clear b;
      simpl; intro HIn;
        apply all_cons_In_gen in HIn;
          destruct HIn as [Heq HIn]; try discriminate;
            unfold base_all_cons; assumption.
Qed.
 
 
Lemma length_0_nil:
  forall (A: Set)(l: list A), length l = 0 -> l = nil.
Proof.
  intros A l; case l; clear l;
    [reflexivity | intros; discriminate].
Qed.
 
 
Lemma generate_all:
  forall n l,
    length l = n -> In l (generate n).
Proof.
  intro n; elim n; clear n.
  simpl.
  intros l Heq; apply length_0_nil in Heq; subst; 
    left; reflexivity.
  intro n; case n; clear n.
  intros IH l; case l; clear l.
  simpl; intros; discriminate.
  simpl; intro b; case b; clear b;
    intros l Heq; apply eq_add_S in Heq; apply length_0_nil in Heq; subst;
      [left | right; left | right; right; left | right; right; right; left]; reflexivity.
  intros n IH l; case l; clear l.
  intros; discriminate.
  intros b l Heq; simpl in Heq.
  apply eq_add_S in Heq.
  apply IH in Heq.
  case b; clear b; simpl; unfold base_all_cons;
    repeat rewrite in_app_iff;
      [left | right; left | right; right; left | right; right; right];
      apply all_cons_In_inv; apply IH; apply generate_length; assumption.
Qed.
 
 
Theorem generate_correct:
  forall n l,
    In l (generate n) <-> length l = n.
Proof.
  intros n l; split;
    [apply generate_length | apply generate_all].
Qed.
  
 
(*
   nat_part...
 
   all partitions of n
   ..."nat_part_correct"
*)
Fixpoint nat_part_aux (n m: nat) :=
  match n with
    | O => [(n, m)]
    | S p => (n, m)::(nat_part_aux p (S m))
  end.
 
Eval compute in (nat_part_aux 2 5).
 
Definition nat_part (n: nat) := nat_part_aux n 0.
 
Eval compute in (nat_part 5).
 
 
Lemma nat_part_aux_trivial_In:
  forall n m,
    In (n, m) (nat_part_aux n m).
Proof.
  intro n; case n; clear n;
    simpl; left; reflexivity.
Qed.
 
Lemma nat_part_correct_aux:
  forall n m p q,
    n <= p ->
    n + m = p+q ->
    In (n, m) (nat_part_aux p q).
Proof.
  intros n m p q Hle;
    generalize m q; clear m q.
  elim Hle; clear Hle p.
  intros m q Heq.
  apply plus_reg_l in Heq; subst q.
  apply nat_part_aux_trivial_In.
  intros p Hle IH m q Heq.
  rewrite plus_Snm_nSm in Heq.
  simpl; right.
  apply (IH _ _ Heq).
Qed.
 
Lemma plus_le:
  forall n m p,
    n + m = p -> n <= p.
Proof.
  intros n m; generalize n; clear n.
  case m; clear m;
    simpl; intros; subst; auto with arith.
Qed.
 
 
Theorem nat_part_correct:
  forall n m p,
    n + m = p -> In (n, m) (nat_part p).
Proof.
  intros n m p Heq.
  apply nat_part_correct_aux.
  apply (plus_le _ _ Heq).
  rewrite plus_0_r; assumption.
Qed.
 
 
(*
   all_tupling...
 
   (a1, a2, ... , an), (b1, b2, ... bm) ~~>
   ((a1, b1), (a1, b2), ... , (a1, bm), (a2, b1), ... , (an, bm))
*)
Fixpoint tupling (A B: Set)(a: A)(l: list B) :=
  match l with
    | nil => nil
    | h::t => (a, h)::(tupling a t)
  end.
 
Fixpoint all_tupling (A B: Set)(al: list A)(bl: list B) :=
  match al with
    | nil => nil
    | h::t => (tupling h bl)++(all_tupling t bl)
  end.
 
Eval compute in (all_tupling (1::3::5::7::nil) (2::4::6::nil)).
 
Lemma tupling_In:
  forall (A B: Set)(a: A)(b: B) l,
    In b l ->
    In (a, b) (tupling a l).
Proof.
  intros A B a b l.
  generalize A a b;
    clear A a b.
  elim l; clear l; simpl.
  intros; contradiction.
  intros h l IH A a b [Heq | HIn].
  subst h; left; reflexivity.
  right; apply IH; assumption.
Qed.
 
Lemma all_tupling_In:
  forall (A B: Set)(a: A)(b: B) l1 l2,
    In a l1 ->
    In b l2 ->
    In (a, b) (all_tupling l1 l2).
Proof.
  intros A B a b l1.
  generalize B a b; clear B a b.
  elim l1; clear l1.
  simpl; intros; contradiction.
  simpl; intros h1 l1 IH B a b l2 [Heq | HIn1] HIn2.
  subst h1.
  apply in_app_iff; left.
  apply tupling_In; assumption.
  apply in_app_iff; right; apply IH; assumption.
Qed.
 
 
(*
   tuplist_generator_aux...
 
   all combinations of n-length list and m-length list
*)
Definition tuplist_generator_aux (n m: nat) :=
  all_tupling (generate n) (generate m).
 
Eval compute in (tuplist_generator_aux 2 2).
 
Lemma tuplist_generator_aux_all:
  forall n m l1 l2,
    length l1 = n ->
    length l2 = m ->
    In (l1, l2) (tuplist_generator_aux n m).
Proof.
  intros n m l1 l2 Heq1 Heq2.
  apply all_tupling_In;
    apply generate_correct; assumption.
Qed.
 
Check pair.
 
(*
   tuplist_generator_with_l...
 
   list of all combinations of ....
*)
Fixpoint tuplist_generator_with_l (l: list (prod nat nat)) :=
  match l with
    | nil => nil
    | (p, q)::t =>
      (tuplist_generator_aux p q)++(tuplist_generator_with_l t)
  end.
 
Lemma tuplist_generator_with_l_correct:
  forall n m l pl,
    In (n, m) pl->
    In l (tuplist_generator_aux n m) ->
    In l (tuplist_generator_with_l pl).
Proof.
  intros n m l pl;
    generalize n m l;
      clear n m l.
  elim pl; clear pl.
  simpl; intros; contradiction.
  simpl.
  intros [p q] pl IH n m [l1 l2] [Heq | HIn].
  injection Heq; intros; subst; clear Heq.
  apply in_app_iff; left; assumption.
  intros HIn'; apply in_app_iff;
    right; eapply IH; eassumption.
Qed.
 
 
Lemma tuplist_generator_correct_aux:
  forall n m p l l1 l2,
    length l1 = n ->
    length l2 = m ->
    n + m = p ->
    l = nat_part p ->
    In (l1, l2) (tuplist_generator_with_l l).
Proof.
  intros n m p l l1 l2 Heq1 Heq2 Heqp Heql.
  generalize (tuplist_generator_aux_all _ _ Heq1 Heq2).
  generalize (nat_part_correct _ _ Heqp).
  rewrite <- Heql.
  apply tuplist_generator_with_l_correct.
Qed.
 
(*
   tuplist_generator...
 
   all combinations of p-length list and q-length list, with p + q = n
*)
Definition tuplist_generator (n: nat) := tuplist_generator_with_l (nat_part n).
 
Eval compute in (tuplist_generator 3).
 
 
(*
   insert...
 
   l ___ l1 l2 ~~> l1 \\ l // l2
*)
Definition insert (A: Set)(l l1 l2: list A) := l1++l++l2.
 
Fixpoint insert_all (A: Set)(l: list A)(pll: list (list A*list A)) :=
  match pll with
    | nil => nil
    | (p,q)::t => (insert l p q)::(insert_all l t)
  end.
 
Eval compute in (insert_all ACGT (tuplist_generator 1)).
 
Lemma insert_all_app:
  forall (A: Set)(l: list A) l1 l2,
    insert_all l (l1++l2) = (insert_all l l1)++(insert_all l l2).
Proof.
  intros A l l1; elim l1; clear l1.
  simpl; reflexivity.
  intros [p1 p2] l1 IH l2.
  simpl.
  rewrite (IH l2); reflexivity.
Qed.
 
Lemma insert_In:
  forall (A: Set)(l1 l2: list A) pl,
    In (l1, l2) pl ->
    forall l,
      In (l1++l++l2) (insert_all l pl).
Proof.
  intros A l1 l2 pl;
    generalize l1 l2;
      clear l1 l2.
  elim pl; clear pl.
  simpl; intros; contradiction.
  intros [p q] pl IH l1 l2.
  simpl; intros [Heq | HIn].
  injection Heq; intros; subst p q.
  left; trivial.
  intros; right; apply IH.
  assumption.
Qed.
 
Lemma insert_tuplist_generator_correct:
  forall l l1 l2 pl,
    In (l1, l2) (tuplist_generator_with_l pl) ->
    In (l1++l++l2) (insert_all l (tuplist_generator_with_l pl)).
Proof.
  intros l l1 l2 pl;
    generalize l l1 l2;
      clear l l1 l2.
  elim pl; clear pl.
  simpl; intros; contradiction.
  intros [p q] pl IH l l1 l2.
  simpl (In (_,_) _); rewrite in_app_iff.
  intros [HIn | HIn].
  simpl.
  generalize (insert_In _ _ _ HIn l).
  rewrite insert_all_app.
  rewrite in_app_iff.
  left; assumption.
  simpl.
  rewrite insert_all_app.
  rewrite in_app_iff; right.
  apply IH; assumption.
Qed.
 
 
(*
   insert_generator...
 
   all lists of m-length lists including l (m = n + length l)
   ..."insert_generator_correct"
*)
Definition insert_generator (l: list base)(n: nat) := 
  insert_all l (tuplist_generator n).
 
Eval compute in (insert_generator ACGT 1).
 
Lemma insert_generator_correct_aux:
  forall n m l l1 l2,
    length l1 = n ->
    length l2 = m ->
    In (l1++l++l2) (insert_generator l (n+m)).
Proof.
  intros n m l l1 l2 Heq1 Heq2.
  unfold insert_generator.
  unfold tuplist_generator.
  apply insert_tuplist_generator_correct.
  apply (tuplist_generator_correct_aux _ _ Heq1 Heq2 (eq_refl _) (eq_refl _)).
Qed.
 
 
(*
   include...
*)
Definition include (A: Set)(l l': list A) :=
  exists l1, exists l2, l' = l1++l++l2.
 
Lemma include_length:
  forall (A: Set)(l l': list A),
    include l l' ->
    length l <= length l'.
Proof.
  intros A l l' [l1 [l2 Heq]]; subst.
  repeat rewrite app_length.
  rewrite plus_comm; simpl.
  auto with arith.
Qed.
 
 
Lemma le_plus:
  forall n p,
    n <= p -> exists m, n+m=p.
Proof.
  intros n p Hle.
  elim Hle; clear Hle p.
  exists 0; rewrite plus_0_r; reflexivity.
  intros p Hle [m Heq]; subst; exists (S m).
  rewrite <- (plus_Snm_nSm n m); simpl; reflexivity.
Qed.
 
Theorem insert_generator_correct:
  forall n l l',
    include l l' ->
    length l + n = length l' ->
    In l' (insert_generator l n).
Proof.
  intros n l l' Hinc.
  generalize Hinc;
    intros [l1 [l2 Heq]];
      apply include_length in Hinc.
  apply le_plus in Hinc.
  subst l'.
  destruct Hinc as [m Heq].
  intro Heq'.
  generalize (eq_trans Heq (eq_sym Heq')).
  intro Heq''.
  apply plus_reg_l in Heq''; subst n.
  clear Heq'.
  repeat rewrite app_length in Heq.
  rewrite (plus_comm (length l1) _) in Heq.
  rewrite <- plus_assoc in Heq.
  apply plus_reg_l in Heq.
  rewrite plus_comm in Heq.
  subst m.
  eapply insert_generator_correct_aux;
    reflexivity.
Qed.
 
 
(*
   AAG_generator
*)
Definition AAG := [A,A,G].
Definition AAG_generator (n: nat) := insert_generator AAG n.
 
Theorem AAG_generator_correct:
  forall n l,
    include AAG l ->
    3 + n = length l ->
    In l (AAG_generator n).
Proof.
  intros.
  apply insert_generator_correct;
    simpl; assumption.
Qed.
 
Eval compute in (AAG_generator 2).