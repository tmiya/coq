Section Even.

(* Assume the function which gives the reminder by 2 *)
Variable mod2 : nat -> nat.

Definition even1(n:nat):Prop := exists m, 2*m = n.


Inductive even:nat -> Prop :=

End Even.

Require Import List.

Section ACGT.

Inductive Letter:Set := A | C | G | T.

Proof.
destruct l; destruct l';
Qed.

Fixpoint combi(n:nat):list (list Letter) :=
match n with

Lemma combi_complete : forall (n:nat)(s:list Letter),
  length s = n -> In s (combi n).
Proof.
induction n.
 induction s.
  intro. simpl. left. auto.
 intro. simpl in H. discriminate H.
induction s.
 intro. simpl in H. discriminate H.
intro. simpl in H. inversion H.
unfold combi; fold combi. rewrite H1.
destruct a.
   eapply in_or_app. left.
   eapply in_map. eapply IHn; auto.
  eapply in_or_app. right. eapply in_or_app. left.
  eapply in_map. eapply IHn; auto.
 eapply in_or_app. right. eapply in_or_app. right.
 eapply in_or_app. left.
 eapply in_map. eapply IHn; auto.
eapply in_or_app. right. eapply in_or_app. right.
eapply in_or_app. right.
eapply in_map. eapply IHn; auto.
Qed.

Proof.
induction n.
 intros. simpl in H. destruct H.
  rewrite <- H. auto.
 elim H.
intros. unfold combi in H; fold combi in H.
assert(forall c:Letter, 
 In s (map (fun s=>c::s) (combi n)) -> 
 length s = S n).
 intros.
 specialize(in_map_iff (fun s=>c::s) (combi n) s).
 intros. destruct H1 as [H1 _].
 specialize(H1 H0). destruct H1. destruct H1.
 rewrite <- H1. simpl. rewrite (IHn x H2). auto.
specialize(in_app_or _ _ _ H). intro.
destruct H1.
 eapply (H0 A H1).
specialize(in_app_or _ _ _ H1). intro.
destruct H2.
 eapply (H0 C H2).
specialize(in_app_or _ _ _ H2). intro.
destruct H3.
 eapply (H0 G H3).
eapply (H0 T H3).
Qed.

| cons_aag : forall (c:Letter) s,
  hasAAG s -> hasAAG (c::s)
| aag_cons : forall s, hasAAG (A::A::G::s).

Proof.
induction s.
 right. intro. inversion H.
destruct IHs.
 left. eapply cons_aag. auto.
destruct a.
   induction s.
    right. intro. inversion H. inversion H1.
   destruct a.
      induction s.
       right. intro. inversion H. inversion H1. inversion H4.
      destruct a.
         right; intro; elim n; inversion H; auto.
        right; intro; elim n; inversion H; auto.
       left. eapply aag_cons.
      right; intro; elim n; inversion H; auto.
     right; intro; elim n; inversion H; auto.
    right; intro; elim n; inversion H; auto.
   right; intro; elim n; inversion H; auto.
  right; intro; elim n; inversion H; auto.
 right; intro; elim n; inversion H; auto.
right; intro; elim n; inversion H; auto.
Qed.

match s with
| nil => false
| A::A::G::_ => true
| _::s' => hasAAGb s'
end.


Proof.
induction s.
 intros. inversion H.
intros. inversion H.
 unfold hasAAGb; fold hasAAGb.
 destruct a; try eapply (IHs H1).
 induction s.
  inversion H1.
 destruct a; try eapply (IHs H1).
 induction s; try eapply (IHs H1).
 destruct a; try eapply (IHs H1).
 reflexivity.
simpl. reflexivity.
Qed.

Proof.
induction s.
 intros. simpl in H. discriminate H.
intros. unfold hasAAGb in H; fold hasAAGb in H.
destruct a;
try (eapply cons_aag; eapply (IHs H)).
induction s.
 simpl in H. discriminate H.
destruct a;
try (eapply cons_aag; eapply (IHs H)).
induction s.
 simpl in H. discriminate H.
destruct a; 
try (eapply cons_aag; eapply (IHs H)).
eapply aag_cons.
Qed.
  


Require Import Ascii.
Require Import String.


match n with


Proof.
simpl. reflexivity. 
Qed.





  filter hasAAG' (combi' n).

Proof. auto. Qed.




Proof.
assert(forall c s, (fun x => String c x) s = String c s).
 intros. simpl. auto.
induction n.
 intros. simpl. left. inversion H0. auto.
intros. simpl. inversion H0. inversion H2.
   rewrite <- H5 in *; clear H5.
   eapply in_or_app. left.
   eapply in_map. eapply IHn. auto.
  rewrite <- H5 in *; clear H5.
  eapply in_or_app. right. eapply in_or_app. left.
  eapply in_map. eapply IHn. auto.
 rewrite <- H5 in *; clear H5.
 eapply in_or_app. right. eapply in_or_app. right. 
 eapply in_or_app. left.
 eapply in_map. eapply IHn. auto.
rewrite <- H5 in *; clear H5.
eapply in_or_app. right. eapply in_or_app. right. 
eapply in_or_app. right.
eapply in_map. eapply IHn. auto.
Qed.

Proof.
induction n.
 intros. simpl in *. destruct H.
  rewrite <- H. apply empty_word.
 elim H.
induction s.
 intro. unfold combi in H; fold combi in H.
 assert(forall c s, (fun x => String c x) s <> EmptyString).
  intros. intro. discriminate H0.
 assert(forall c ss, 
  induction ss.
   intro. simpl in H1. elim H1.
  intro. simpl in H1. destruct H1.
   discriminate H1.
  elim IHss; auto.
 specialize(in_app_or _ _ ""%string H). intro. destruct H2.
  elim (H1 "A"%char (combi' n)); auto.
 specialize(in_app_or _ _ ""%string H2). intro. destruct H3.
  elim (H1 "C"%char (combi' n)); auto.
 specialize(in_app_or _ _ ""%string H3). intro. destruct H4.
  elim (H1 "G"%char (combi' n)); auto.
 elim (H1 "T"%char (combi' n)); auto.
intro. eapply string_word.
 unfold combi' in H; fold combi' in H.
 assert(forall a c s ss, 
  induction ss.
   intro. simpl in H0. elim H0.
  intro. simpl in H0. destruct H0.
   inversion H0. auto.
  apply IHss; auto.
 specialize(in_app_or _ _ (String a s) H). intro. destruct H1.
  specialize(H0 a "A"%char s (combi' n) H1). rewrite H0. apply A_letter.
 specialize(in_app_or _ _ (String a s) H1). intro. destruct H2.
  rewrite (H0 a "C"%char s (combi' n) H2). apply C_letter.
 specialize(in_app_or _ _ (String a s) H2). intro. destruct H3.
  rewrite (H0 a "G"%char s (combi' n) H3). apply G_letter.
 rewrite (H0 a "T"%char s (combi' n) H3). apply T_letter.
eapply IHn.
unfold combi' in H; fold combi' in H.
assert(forall a c s ss, 
 induction ss.
  intro. simpl in H0. elim H0.
 intro. simpl in H0. destruct H0.
  inversion H0. simpl. left; auto.
 simpl. right; apply IHss; auto.
specialize(in_app_or _ _ (String a s) H). intro. destruct H1.
 eapply (H0 a "A"%char); auto.
specialize(in_app_or _ _ (String a s) H1). intro. destruct H2.
 eapply (H0 a "C"%char); auto.
specialize(in_app_or _ _ (String a s) H2). intro. destruct H3.
 eapply (H0 a "G"%char); auto.
eapply (H0 a "T"%char); auto.
Qed.

  hasAAG' s = true -> Aag s.
Proof.
induction s.
 simpl. intro. discriminate H.
unfold hasAAG'; fold hasAAG'. destruct (hasAAG' s).
 intro. eapply c_aag. eapply IHs. auto.
destruct (ascii_dec a "A").
 rewrite e in *; clear e. destruct s.
  intro. discriminate H.
 destruct (ascii_dec a0 "A").
  rewrite e in *; clear e. destruct s.
   intro. discriminate H.
  destruct (ascii_dec a1 "G").
   rewrite e in *; clear e. intro. eapply aag_s.
  intro. discriminate H.
 intro. discriminate H.
intro. discriminate H.
Qed.

Proof.
induction s.
 intro. inversion H.
intro. inversion H.
 simpl. rewrite (IHs H1). auto.
simpl. destruct (hasAAG' s0); auto.
Qed.





Eval compute in (ans_aux 4 0).


