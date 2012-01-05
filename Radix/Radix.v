(** * Encoder/Decoder by Radix *)
Require Import Recdef.
Require Import List.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Omega.
Require Import Ring.

Section fold_unfold_N.
(** Variable *)
Variable radix : Z.
Variable Hradix : (radix >= 2)%Z.

Definition Nradix := N_of_Z radix.

(** Preparations *)

Ltac intro_discri :=
 let H' := fresh "H" in 
 intro H'; discriminate H'.

Ltac simpl_discri H :=
 simpl in H; discriminate H.

Ltac add_H' P H' := specialize P; intro H'.

Ltac add_H P := specialize P; intro.

(* It solves only trivial ones. *)
Ltac elim_ineq H' :=
match type of H' with
| (_ < _)%Z => unfold Zlt in H'; simpl_discri H'
| (_ > _)%Z => unfold Zgt in H'; simpl_discri H'
| (_ <= _)%Z => unfold Zle in H'; simpl in H'; elim H'; auto
| (_ >= _)%Z => unfold Zge in H'; simpl in H'; elim H'; auto
| (_ < _)%N => unfold Nlt in H'; simpl_discri H'
| (_ > _)%N => unfold Ngt in H'; simpl_discri H'
| (_ <= _)%N => unfold Nle in H'; simpl in H'; elim H'; auto
| (_ >= _)%N => unfold Nge in H'; simpl in H'; elim H'; auto
end.

(* Simple lemmas *)
Lemma radix_pos : (radix > 0)%Z.
Proof with auto.
omega.
Qed.

Lemma Z0_le_radix : (0 <= radix)%Z.
Proof with auto.
omega.
Qed.

Lemma Zabs_radix : (Zabs radix = radix)%Z.
Proof with auto.
destruct radix...
elim Hradix. simpl...
Qed.

Hint Extern 5 ((radix > 0)%Z) => eapply radix_pos : mydb.
Hint Extern 5 ((0 <= radix)%Z) => eapply Z0_le_radix : mydb.
Hint Extern 5 ((Zabs radix = radix)%Z) => eapply Zabs_radix : mydb.

Lemma Z0_le_Zpos : forall p, (0<=Zpos p)%Z.
Proof.
intros; destruct p; unfold Zle; 
simpl; intro_discri. 
Qed.

Lemma Z0_lt_Zpos : forall p, (0<Zpos p)%Z.
Proof.
intros; destruct p; unfold Zlt; auto.
Qed.

Lemma Zpos_ge_Z0 : forall p, (Zpos p>=0)%Z.
Proof.
intros; destruct p; unfold Zle; 
simpl; intro_discri.
Qed.

Lemma Zpos_gt_Z0 : forall p, (Zpos p>0)%Z.
Proof.
intros; add_H (Z0_lt_Zpos p); omega.
Qed.

Hint Extern 5 ((0 < Zpos ?X)%Z) => eapply Z0_lt_Zpos : mydb.
Hint Extern 5 ((0 <= Zpos ?X)%Z) => eapply Z0_le_Zpos : mydb.
Hint Extern 5 ((Zpos ?X > 0)%Z) => eapply Zpos_gt_Z0 : mydb.
Hint Extern 5 ((Zpos ?X >= 0)%Z) => eapply Zpos_ge_Z0 : mydb.

Lemma N0_le_N : forall n:N, (0<=n)%N.
Proof.
intro; destruct n; unfold Nle; intro_discri.
Qed.

Lemma N_ge_N0 : forall n:N, (n>=0)%N.
Proof.
intro; destruct n; unfold Nge; intro_discri.
Qed.

Lemma N0_lt_Npos : forall p, (0<Npos p)%N.
Proof with auto.
intro; unfold Nlt; simpl...
Qed.

Lemma Npos_gt_N0 : forall p, (Npos p>0)%N.
Proof with auto.
intro; unfold Ngt; simpl...
Qed.

Hint Extern 5 ((0 < Npos ?X)%N) => eapply N0_lt_Npos : mydb.
Hint Extern 5 ((Npos ?X > 0)%N) => eapply Npos_gt_N0 : mydb.
Hint Extern 5 ((0 <= ?X)%N) => eapply N0_le_N : mydb.
Hint Extern 5 ((?X >= 0)%N) => eapply N_ge_N0 : mydb.

Lemma Zcompare_Lt : forall a b:Z,
 (a<b)%Z -> (a ?= b)%Z=Lt.
Proof with auto.
intros...
Qed.
Lemma Zcompare_Gt : forall a b:Z,
 (a>b)%Z -> (a ?= b)%Z=Gt.
Proof with auto.
intros...
Qed.
Lemma Zcompare_Le : forall a b:Z,
 (a<=b)%Z -> (a ?= b)%Z<>Gt.
Proof with auto.
intros...
Qed.
Lemma Zcompare_Ge : forall a b:Z,
 (a>=b)%Z -> (a ?= b)%Z<>Lt.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Lt : forall a b:N,
 (a<b)%N -> (a ?= b)%N=Lt.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Gt : forall a b:N,
 (a>b)%N -> (a ?= b)%N=Gt.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Le : forall a b:N,
 (a<=b)%N -> (a ?= b)%N<>Gt.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Ge : forall a b:N,
 (a>=b)%N -> (a ?= b)%N<>Lt.
Proof with auto.
intros...
Qed.

Ltac fold_compare :=
match goal with
| [ |- (?a ?= ?b)%Z = Lt ] => eapply Zcompare_Lt; try omega; try auto
| [ |- (?a ?= ?b)%Z = Gt ] => eapply Zcompare_Gt; try omega; try auto
| [ |- (?a ?= ?b)%Z <> Gt ] => eapply Zcompare_Le; try omega; try auto
| [ |- (?a ?= ?b)%Z <> Lt ] => eapply Zcompare_Ge; try omega; try auto
| [ |- (?a ?= ?b)%N = Lt ] => eapply Ncompare_Lt; try omega; try auto
| [ |- (?a ?= ?b)%N = Gt ] => eapply Ncompare_Gt; try omega; try auto
| [ |- (?a ?= ?b)%N <> Gt ] => eapply Ncompare_Le; try omega; try auto
| [ |- (?a ?= ?b)%N <> Lt ] => eapply Ncompare_Ge; try omega; try auto
end.

Lemma Zcompare_Lt_H : forall a b:Z,
 (a ?= b)%Z=Lt -> (a<b)%Z.
Proof with auto.
intros...
Qed.
Lemma Zcompare_Gt_H : forall a b:Z,
 (a ?= b)%Z=Gt -> (a>b)%Z.
Proof with auto.
intros...
Qed.
Lemma Zcompare_Le_H : forall a b:Z,
 (a ?= b)%Z<>Gt -> (a<=b)%Z.
Proof with auto.
intros...
Qed.
Lemma Zcompare_Ge_H : forall a b:Z,
 (a ?= b)%Z<>Lt -> (a>=b)%Z.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Lt_H : forall a b:N,
 (a ?= b)%N=Lt -> (a<b)%N.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Gt_H : forall a b:N,
 (a ?= b)%N=Gt -> (a>b)%N.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Le_H : forall a b:N,
 (a ?= b)%N<>Gt -> (a<=b)%N.
Proof with auto.
intros...
Qed.
Lemma Ncompare_Ge_H : forall a b:N,
 (a ?= b)%N<>Lt -> (a>=b)%N.
Proof with auto.
intros...
Qed.

Ltac fold_compare_H H' :=
match type of H' with
| ((?a ?= ?b)%Z = Lt) => add_H (Zcompare_Lt_H a b H')
| ((?a ?= ?b)%Z = Gt) => add_H (Zcompare_Gt_H a b H')
| ((?a ?= ?b)%Z <> Gt) => add_H (Zcompare_Le_H a b H')
| ((?a ?= ?b)%Z <> Lt) => add_H (Zcompare_Ge_H a b H')
| ((?a ?= ?b)%N = Lt) => add_H (Ncompare_Lt_H a b H')
| ((?a ?= ?b)%N = Gt) => add_H (Ncompare_Gt_H a b H')
| ((?a ?= ?b)%N <> Gt) => add_H (Ncompare_Le_H a b H')
| ((?a ?= ?b)%N <> Lt) => add_H (Ncompare_Ge_H a b H')
end; clear H'; try omega.

Lemma nat_compare_Lt : forall n m:nat, 
 nat_compare n m = Lt -> n < m.
Proof with auto.
induction n.
 intros m H. unfold nat_compare in H.
 induction m.
  discriminate H.
 omega.
induction m.
 intros H. unfold nat_compare in H. 
 discriminate H.
intros H. simpl in H. specialize (IHn m H). 
omega.
Qed.

Lemma Nplus_eq_N0 : forall n m:N, 
 (n+m=0)%N -> (n=0)%N /\ (m=0)%N.
Proof with auto.
destruct n; destruct m...
simpl. intro_discri.
Qed.

Lemma Nmult_eq_N0 : forall n m:N, 
 (n*m=0)%N -> (n=0)%N \/ (m=0)%N.
Proof with auto.
destruct n; destruct m...
simpl. intro_discri.
Qed.

Lemma Zneg_le_M1 : forall p, (Zneg p <= -1)%Z.
Proof with auto.
destruct p; unfold Zle; simpl; intro_discri.
Qed.

Hint Extern 5 ((Zneg ?p <= -1)%Z) => eapply Zneg_le_M1 : mydb.

(** Z and N *)

Lemma Z_of_N_of_Z : forall z,
 (0 <= z)%Z ->
 Z_of_N (N_of_Z z) = z.
Proof with auto.
intros z H. destruct z...
elim_ineq H.
Qed.

Lemma N_of_Z_of_N : forall n,
 N_of_Z (Z_of_N n) = n.
Proof with auto.
intros n. destruct n...
Qed.

Lemma N_of_Z_preserve_plus : forall z1 z2,
 (0 <= z1)%Z -> (0 <= z2)%Z ->
 (N_of_Z z1 + N_of_Z z2)%N = N_of_Z (z1 + z2)%Z.
Proof with auto.
destruct z1; destruct z2; intros H1 H2...
 elim_ineq H2.
elim_ineq H1.
Qed.

Lemma N_of_Z_preserve_mult : forall z1 z2,
 (0 <= z1)%Z -> (0 <= z2)%Z ->
 (N_of_Z z1 * N_of_Z z2)%N = N_of_Z (z1 * z2)%Z.
Proof with auto.
destruct z1; destruct z2; intros H1 H2...
elim_ineq H1.
Qed.

Lemma N_of_Z_preserve_compare : forall z1 z2,
 (0 <= z1)%Z -> (0 <= z2)%Z ->
 (N_of_Z z1 ?= N_of_Z z2)%N = (z1 ?= z2)%Z.
Proof with auto.
destruct z1; destruct z2; intros H1 H2...
  elim_ineq H2...
 elim_ineq H1... 
elim_ineq H1...
Qed.

Lemma Z_of_N_preserve_plus : forall n1 n2,
 (Z_of_N n1 + Z_of_N n2)%Z = Z_of_N (n1 + n2)%N.
Proof with auto.
destruct n1; destruct n2...
Qed.

Lemma Z_of_N_preserve_mult : forall n1 n2,
 (Z_of_N n1 * Z_of_N n2)%Z = Z_of_N (n1 * n2)%N.
Proof with auto.
destruct n1; destruct n2...
Qed.

Lemma Z_of_N_preserve_compare : forall n1 n2,
 (Z_of_N n1 ?= Z_of_N n2)%Z = (n1 ?= n2)%N.
Proof with auto.
destruct n1; destruct n2...
Qed.

(** Zdiv-related *)

Lemma Zneg_False : forall p p0 r,
 Zpos p = (radix*Zneg p0+r)%Z ->
 (0<=r<radix)%Z -> False.
Proof with auto with mydb.
intros p p0 r H H0.
assert((radix*Zneg p0+r < 0)%Z).
 assert((radix*Zneg p0 <= radix*(-1))%Z).
  assert((Zneg p0 <= -1)%Z)...
  eapply Zmult_le_compat_l... 
 omega.
rewrite <- H in H1. elim_ineq H1.
Qed.

Ltac elim_neg Hx :=
match type of Hx with
| Zpos ?p = (radix * Zneg ?p0 + ?r)%Z =>
  elim (Zneg_False p p0 r Hx); auto
| (radix * Zneg ?p0 + ?r)%Z = Zpos ?p =>
  elim (Zneg_False p p0 r Hx); auto
end.

Ltac div_eucl Hx :=
match type of Hx with
| Zdiv_eucl (Zpos ?p) radix = (_, _)
  => let H' := fresh "H" in
     specialize(Z_div_mod (Zpos p) radix radix_pos);
     intro H'; erewrite Hx in H'; destruct H'
| (_, _) = Zdiv_eucl (Zpos ?p) radix
  => let H' := fresh "H" in
     specialize(Z_div_mod (Zpos p) radix radix_pos);
     intro H'; erewrite <- Hx in H'; destruct H'
end.

Ltac tuple_eucl z q r:=
 let p' := fresh "p" in
 remember(Zdiv_eucl z radix) as p'; destruct p' as [q r].

(** * foldr and unfoldr by radix *)

Fixpoint foldr_by_radix(ns:list N):N :=
let nr := N_of_Z radix in
match ns with
| nil => N0
| n::ns' => (n + nr*(foldr_by_radix ns'))%N
end.

Function unfoldr_by_radix(n:N){measure nat_of_N n}:list Z :=
match n with
| N0 => nil
| Npos p => match (Zdiv_eucl (Zpos p) radix) with
  | (Z0,r) => r::nil
  | (q,r) => r::(unfoldr_by_radix (N_of_Z q))
  end
end.
Proof with auto.
 intros n p Hpn q r p0 Hqp0 Heucl.
 eapply nat_compare_lt.
 erewrite <- nat_of_Ncompare. simpl.
 add_H (Z_div_lt (Zpos p) radix Hradix (Zpos_gt_Z0 p)). 
 unfold Zdiv in H. 
 rewrite Heucl in H...
intros n p Hnp q r p0 Hqp0 Heucl.
div_eucl Heucl. elim_neg H.
Defined.
(* Here we have two supporting lemmas:
unfoldr_by_radix_ind : 
  forall P : N -> list Z -> Prop,
  (some conditions) ->
  forall n : N, P n (unfoldr_by_radix n),
  which is its induction principle.
unfoldr_by_radix_equation :
  forall n : N, unfoldr_by_radix n = ...,
  which is its definition.
*)

Inductive Zproper:list Z -> Prop :=
| Nil_Zproper : Zproper nil
| Single_Zproper : forall z, 
  (0 < z < radix)%Z -> Zproper (z::nil)
| Cons_Zproper : forall z zs, 
  (0 <= z < radix)%Z -> zs<> nil -> Zproper zs -> 
  Zproper (z::zs).

Inductive Nproper:list N -> Prop :=
| Nil_Nproper : Nproper nil
| Single_Nproper : forall n:N, 
  (0 < n)%N -> (n < Nradix)%N -> Nproper (n::nil)
| Cons_Nproper : forall (n:N)(ns:list N), 
  (0 <= n)%N -> (n < Nradix)%N -> ns<> nil -> Nproper ns -> 
  Nproper (n::ns).

Hint Constructors Zproper Nproper: mydb.

Lemma Zproper_is_Nproper : forall zs,
 Zproper zs -> Nproper (map N_of_Z zs).
Proof with auto with mydb.
induction zs.
 intro H. simpl. eapply Nil_Nproper.
intro H. induction zs.
 inversion H. simpl. eapply Single_Nproper.
   replace 0%N with (N_of_Z 0%Z).
    unfold Nlt. 
    erewrite N_of_Z_preserve_compare...
      fold_compare.
     omega.
    omega.
   simpl...
  unfold Nradix. unfold Nlt.
  erewrite N_of_Z_preserve_compare.
    fold_compare.
   omega.
  omega.
 elim H3...
inversion H. rewrite <- H1.
eapply Cons_Nproper.
   replace 0%N with (N_of_Z 0%Z).
    intro. 
    erewrite N_of_Z_preserve_compare in H5.
      fold_compare_H H5.
     omega.
    omega.
   simpl...
  unfold Nradix. unfold Nlt.
  erewrite N_of_Z_preserve_compare.
    fold_compare.
   omega.
  omega.
 rewrite H1. intro_discri.
rewrite <- H1 in *. specialize (IHzs H4).
unfold map in IHzs...
Qed.

Lemma Zproper_cons : forall z zs,
 Zproper (z::zs) ->
 {(0<z<radix)%Z /\ zs=nil} +
 {(0<=z<radix)%Z /\ zs<> nil /\ Zproper zs}.
Proof with auto with mydb.
intros z zs H.
induction zs.
 left. split...
 inversion H...
 elim H3...
right. split.
 inversion H...
split.
 intro_discri. 
inversion H...
Qed.

Lemma unfoldr_by_radix_proper : forall n, 
 Zproper (unfoldr_by_radix n).
Proof with auto with mydb.
intros n.
eapply unfoldr_by_radix_ind.
  intros...
 intros n0 p Hn0 r Heucl.
 div_eucl Heucl.
 replace (radix*0+r)%Z with r in H by ring.
 assert((0<r<radix)%Z).
  assert((r<>0)%Z).
   rewrite <- H. intro_discri. 
  omega.
 eapply Single_Zproper...
intros n0 p Hn0 q r Heucl Hproper IHproper.
div_eucl Heucl.
destruct q.
  elim Hproper.
 eapply Cons_Zproper... 
 erewrite unfoldr_by_radix_equation.
 replace (N_of_Z (Zpos p0)) with (Npos p0) by auto.
 tuple_eucl (Zpos p0) q' r'.
 destruct q'; intro_discri. 
elim_neg H.
Qed.

Lemma foldr_by_radix_nonzero : forall ns:list N,
 Nproper ns -> ns <> nil -> (foldr_by_radix ns <> 0)%N.
Proof with auto with mydb.
induction ns.
 intros. elim H0...
intros. inversion H.
 simpl. intro.
 add_H (Nplus_eq_N0 _ _ H5). destruct H6.
 rewrite H6 in H3.
 elim_ineq H3.
specialize(IHns H6 H5).
simpl. intro. add_H (Nplus_eq_N0 _ _ H7).
destruct H8.
add_H (Nmult_eq_N0 _ _ H9). destruct H10.
 assert((Z_of_N (N_of_Z radix) = 0)%Z).
  rewrite H10...
  erewrite Z_of_N_of_Z in H11.
  rewrite H11 in Hradix. omega.
 omega.
elim IHns...
Qed.
 
Theorem foldr_unfoldr_by_radix : forall n,
  foldr_by_radix (map N_of_Z (unfoldr_by_radix n)) = n.
Proof with auto with mydb.
intro n.
remember (unfoldr_by_radix n) as l.
generalize dependent n.
induction l.
 intros n Heql.
 rewrite unfoldr_by_radix_equation in Heql.
 destruct n...
 tuple_eucl (Zpos p) q r; destruct q;
 discriminate Heql.
intros n0 Hal. simpl.
erewrite unfoldr_by_radix_equation in Hal.
destruct n0; try discriminate Hal.
tuple_eucl (Zpos p) q r; destruct q.
  inversion Hal. simpl.
  assert((r = Zpos p)%Z).
   div_eucl Heqp0. rewrite H. ring.
  replace (N_of_Z r + N_of_Z radix * 0)%N with
  (N_of_Z r) by ring.
  rewrite H...
 inversion Hal. specialize(IHl (Npos p0) H1).
 rewrite <- H1. rewrite IHl.
 div_eucl Heqp0.
 replace (N_of_Z r + N_of_Z radix * Npos p0)%N
 with (N_of_Z (radix*Zpos p0+r)%Z).
  rewrite <- H...
 replace (Npos p0) with (N_of_Z (Zpos p0)) by auto.
 erewrite (N_of_Z_preserve_mult radix (Zpos p0)).
   erewrite (N_of_Z_preserve_plus r (radix*Zpos p0)%Z).
     replace (radix*Zpos p0+r)%Z with (r+radix*Zpos p0)%Z by ring...
    omega.
   eapply Zmult_le_0_compat...
  omega.
 auto with mydb.
div_eucl Heqp0. elim_neg H. 
Qed.

Theorem unfoldr_foldr_by_radix : forall ns:list N,
  Nproper ns ->
  map N_of_Z (unfoldr_by_radix (foldr_by_radix ns)) = ns.
Proof with auto with mydb.
induction ns...
remember (foldr_by_radix ns) as n0. simpl.
rewrite <- Heqn0.
remember (a + N_of_Z radix * n0)%N as n1.
intros Hproper.
erewrite unfoldr_by_radix_equation.
destruct n1.
 symmetry in Heqn1.
 add_H (Nplus_eq_N0 _ _ Heqn1). destruct H.
 add_H (Nmult_eq_N0 _ _ H0). destruct H1.
  assert((Z_of_N (N_of_Z radix) = 0)%Z).
   rewrite H1...
  erewrite Z_of_N_of_Z in H2.
   add_H radix_pos. rewrite H2 in H3. elim_ineq H3. 
  add_H radix_pos. omega.
 inversion Hproper.
  rewrite H in H4. elim_ineq H4. 
 specialize(IHns H7). rewrite H1 in IHns.
 simpl in IHns. rewrite <- IHns in H6.
 elim H6...
tuple_eucl (Zpos p) q r. div_eucl Heqp0.
assert((Zpos p = radix * Z_of_N n0 + Z_of_N a)%Z).
 replace (Zpos p) with (Z_of_N (Npos p)) by auto.
 rewrite Heqn1. erewrite <- Z_of_N_preserve_plus.
 erewrite <- Z_of_N_preserve_mult.
 erewrite Z_of_N_of_Z... ring.
rewrite H in H1.
add_H (Zdiv_mod_unique radix q (Z_of_N n0) r (Z_of_N a)).
rewrite Zabs_radix in H2.
specialize(H2 H0).
assert((0<=Z_of_N a<radix)%Z).
 inversion Hproper.
  split.
   replace 0%Z with (Z_of_N 0%N) by auto...
   unfold Zle. erewrite Z_of_N_preserve_compare.
   fold_compare...
  replace radix with (Z_of_N Nradix).
   unfold Zlt. erewrite Z_of_N_preserve_compare.
   fold_compare...
  unfold Nradix. erewrite Z_of_N_of_Z...
 split.
  replace 0%Z with (Z_of_N 0%N) by auto...
  unfold Zle. erewrite Z_of_N_preserve_compare.
  unfold Nle in H5...
 replace radix with (Z_of_N Nradix).
  unfold Zlt. erewrite Z_of_N_preserve_compare.
  unfold Nlt in H6...
 unfold Nradix. erewrite Z_of_N_of_Z...
specialize(H2 H3 H1). destruct H2.
destruct q.
  assert((n0 = 0)%N).
   destruct n0...
   simpl_discri H2.
  assert(ns=nil).
   destruct ns...
   inversion Hproper. 
   elim (foldr_by_radix_nonzero (n::ns) H11 H10)...
   rewrite <- Heqn0...
  rewrite H6 in *. simpl. rewrite H4.
  rewrite N_of_Z_of_N...
 rewrite H2. erewrite N_of_Z_of_N.
 simpl. rewrite H4. erewrite N_of_Z_of_N.
 inversion Hproper.
  rewrite <- H6 in Heqn0. simpl in Heqn0.
  rewrite Heqn0...
 rewrite (IHns H10)...
elim_neg H.
Qed.

Definition encode_by_radix(n:N):list N :=
  map N_of_Z (unfoldr_by_radix n).
Definition decode_by_radix(ns:list N):N :=
  foldr_by_radix ns.

Theorem decode_encode_radix : forall n,
  decode_by_radix (encode_by_radix n) = n.
Proof.
unfold decode_by_radix.
unfold encode_by_radix.
eapply foldr_unfoldr_by_radix.
Qed.

Theorem encode_Nproper : forall n,
 Nproper (encode_by_radix n).
Proof with auto.
unfold encode_by_radix.
intros. eapply Zproper_is_Nproper.
eapply unfoldr_by_radix_proper.
Qed.

Lemma decode_by_radix_eq_0 : forall ns, 
 Nproper ns -> decode_by_radix ns = 0%N -> 
 ns = nil.
Proof with auto.
induction ns.
 intros...
intros. induction ns.
 simpl in H0.
 replace (a + N_of_Z radix * 0)%N with a in H0 by ring.
 inversion H.
  rewrite H0 in H2. unfold Nlt in H2.
  simpl_discri H2.
 elim H5...
inversion H.
rewrite <- H2 in *. specialize(IHns H6).
assert(a::ns0<>nil) by intro_discri.
elim (foldr_by_radix_nonzero (a::ns0) H H7)...
Qed.

Theorem encode_decode_radix : forall ns,
  Nproper ns -> 
  encode_by_radix (decode_by_radix ns) = ns.
Proof with auto with mydb.
intros.
unfold decode_by_radix.
unfold encode_by_radix.
eapply unfoldr_foldr_by_radix...
Qed.

End fold_unfold_N.

Lemma radix_2 : (2 >= 2)%Z.
Proof. omega. Qed.
Lemma radix_10 : (10 >= 2)%Z.
Proof. omega. Qed.
Lemma radix_128 : (128 >= 2)%Z.
Proof. omega. Qed.
Lemma radix_256 : (256 >= 2)%Z.
Proof. omega. Qed.

(** Sample usage
Eval compute in (encode_by_radix 10%Z radix_10 0%N).
  = nil
Eval compute in (encode_by_radix 10%Z radix_10 123%N).
  = 3%N :: 2%N :: 1%N :: nil
Eval compute in (decode_by_radix 10%Z nil).
  = 0%N
Eval compute in (decode_by_radix 10%Z (3%N::2%N::1%N::nil)).
  = 123%N
*)

(** itoa : Z -> string *)

Require Import Ascii.
Require Import String.

Definition N_to_ascii : forall n:N, (n<10)%N -> ascii.
refine(fun n =>
  match n with
  | 0%N => fun _ => "0"%char
  | 1%N => fun _ => "1"%char
  | 2%N => fun _ => "2"%char
  | 3%N => fun _ => "3"%char
  | 4%N => fun _ => "4"%char
  | 5%N => fun _ => "5"%char
  | 6%N => fun _ => "6"%char
  | 7%N => fun _ => "7"%char
  | 8%N => fun _ => "8"%char
  | 9%N => fun _ => "9"%char
  | _ => fun _ => False_rec _ _
  end).
Proof with auto.
         unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
        unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
       unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
      unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
     unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
    unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
   unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
  unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
 unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
unfold Nlt in _H; simpl in _H; destruct p2; discriminate _H.
Defined.

Definition ns_to_asciis_aux : forall ns:list N,
 Nproper 10%Z ns -> list ascii.
refine(fix f (ns:list N):(Nproper 10%Z ns)->list ascii :=
  match ns as ns0 return (Nproper 10%Z ns0 -> list ascii) with
  | nil => fun _ => nil
  | n::ns' => fun _ => (N_to_ascii n _) :: (f ns' _)
  end).
Proof with auto.
 inversion _H.
  unfold Nradix in H2. simpl in H2...
 unfold Nradix in H2. simpl in H2...
inversion _H...
eapply Nil_Nproper.
Defined.

Definition N_to_asciis(n:N):list ascii.
Proof with auto.
remember(encode_by_radix 10%Z radix_10 n).
assert(Nproper 10%Z l).
 rewrite Heql. eapply encode_Nproper.
exact (ns_to_asciis_aux l H).
Defined.

Fixpoint asciis_to_string(cs:list ascii):string :=
match cs with
| nil => EmptyString
| c::cs' => String c (asciis_to_string cs')
end.

Definition itoa(z:Z):string :=
match z with
| Z0 => "0"%string
| Zpos p => 
  asciis_to_string (rev (N_to_asciis (Npos p)))
| Zneg p => String "-"%char (
  asciis_to_string (rev (N_to_asciis (Npos p))))
end.

(*
Eval compute in (itoa (-1234)%Z).
  = "-1234"%string 
*)


