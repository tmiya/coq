Section Even.

(* Assume the function which gives the reminder by 2 *)
Variable mod2 : nat -> nat.

Definition even1(n:nat):Prop := exists m, 2*m = n.
Definition even2(n:nat):Prop := mod2 n = 0.

Inductive even:nat -> Prop :=| even_0 : even 0| even_SS : forall n, even n -> even (S (S n)).

End Even.

Require Import List.

Section ACGT.
(* Design Choice #1 : Use of String LibraryRequire Import Ascii.Require Import String.Check "abc"%string.Print string.Check "a"%char.Print ascii.Inductive Word : nat -> string -> Prop :=| Wempty : Word 0 EmptyString| W_A : forall n s, Word n s -> Word (S n) (String "A"%char s) | W_C : forall n s, Word n s -> Word (S n) (String "C"%char s) | W_G : forall n s, Word n s -> Word (S n) (String "G"%char s) | W_T : forall n s, Word n s -> Word (S n) (String "T"%char s).*)
Inductive Letter:Set := A | C | G | T.
Lemma Letter_dec : forall l l':Letter, {l=l'}+{l<>l'}.
Proof.
destruct l; destruct l'; try (left; reflexivity); (right; intro H; discriminate H).
Qed.

Fixpoint combi(n:nat):list (list Letter) :=
match n with| O => nil::nil| S n' => let ss := combi n' in  (map (fun s => A::s) ss) ++  (map (fun s => C::s) ss) ++  (map (fun s => G::s) ss) ++  (map (fun s => T::s) ss)end.

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
Lemma combi_correct : forall (n:nat)(s:list Letter),  In s (combi n) -> length s = n.
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
Inductive hasAAG : list Letter -> Prop :=
| cons_aag : forall (c:Letter) s,
  hasAAG s -> hasAAG (c::s)
| aag_cons : forall s, hasAAG (A::A::G::s).
Lemma hasAAG_dec : forall s, {hasAAG s}+{~hasAAG s}.
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
Fixpoint hasAAGb(s:list Letter):bool :=
match s with
| nil => false
| A::A::G::_ => true
| _::s' => hasAAGb s'
end.
Print hasAAGb.
Lemma hasAAG1 : forall s, hasAAG s -> hasAAGb s = true.
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
Lemma hasAAG2 : forall s, hasAAGb s = true -> hasAAG s.
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
  Eval compute in (filter hasAAGb (combi 4)).
End ACGT.
Require Import List.
Require Import Ascii.
Require Import String.
(* Constructors of string *)Print string.
(* get n:nat and returns all of n-letter strings *)  Fixpoint combi'(n:nat):list string :=
match n with| O => EmptyString :: nil| S n' => let ss := combi' n'  in (map (fun s => String "A"%char s) ss) ++     (map (fun s => String "C"%char s) ss) ++     (map (fun s => String "G"%char s) ss) ++     (map (fun s => String "T"%char s) ss)end.
Eval compute in (combi' 2).
Lemma combi_3 : combi' 3 =    "AAA"%string :: "AAC"%string :: "AAG"%string :: "AAT"%string  :: "ACA"%string :: "ACC"%string :: "ACG"%string :: "ACT"%string  :: "AGA"%string :: "AGC"%string :: "AGG"%string :: "AGT"%string  :: "ATA"%string :: "ATC"%string :: "ATG"%string :: "ATT"%string :: "CAA"%string :: "CAC"%string :: "CAG"%string :: "CAT"%string  :: "CCA"%string :: "CCC"%string :: "CCG"%string :: "CCT"%string  :: "CGA"%string :: "CGC"%string :: "CGG"%string :: "CGT"%string  :: "CTA"%string :: "CTC"%string :: "CTG"%string :: "CTT"%string :: "GAA"%string :: "GAC"%string :: "GAG"%string :: "GAT"%string  :: "GCA"%string :: "GCC"%string :: "GCG"%string :: "GCT"%string  :: "GGA"%string :: "GGC"%string :: "GGG"%string :: "GGT"%string  :: "GTA"%string :: "GTC"%string :: "GTG"%string :: "GTT"%string :: "TAA"%string :: "TAC"%string :: "TAG"%string :: "TAT"%string  :: "TCA"%string :: "TCC"%string :: "TCG"%string :: "TCT"%string  :: "TGA"%string :: "TGC"%string :: "TGG"%string :: "TGT"%string  :: "TTA"%string :: "TTC"%string :: "TTG"%string :: "TTT"%string :: nil.
Proof.
simpl. reflexivity. 
Qed.
(* filter list with conditions *)Check filter.
(* map function *)Check map.
(* judge s:string include "AAG" or not *)Check ascii_dec.
Fixpoint hasAAG'(s:string):bool :=match s with| EmptyString => false| String c1 s1 => if (hasAAG' s1) then true   else match (ascii_dec c1 "A"%char) with  | right _ => false  | left _=> match s1 with    | EmptyString => false    | String c2 s2 => match (ascii_dec c2 "A"%char) with      | right _ => false      | left _ => match s2 with        | EmptyString => false        | String c3 _ => match (ascii_dec c3 "G"%char) with          | right _ => false          | left _ => true          end        end      end    end  endend.
Definition searchAAG(n:nat):list string :=
  filter hasAAG' (combi' n).
Lemma searchAAG_4 : searchAAG 4 =  "AAAG"%string ::   "AAGA"%string :: "AAGC"%string :: "AAGG"%string :: "AAGT"%string                :: "CAAG"%string :: "GAAG"%string :: "TAAG"%string   :: nil.
Proof. auto. Qed.
Inductive Letter' : ascii -> Prop :=| A_letter : Letter' "A"%char| C_letter : Letter' "C"%char| G_letter : Letter' "G"%char| T_letter : Letter' "T"%char.
Inductive Word' : nat -> string -> Prop :=| empty_word : Word' 0 EmptyString| string_word : forall n c s,    Letter' c -> Word' n s -> Word' (S n) (String c s).
Inductive Aag : string -> Prop :=| c_aag : forall c s, Aag s -> Aag (String c s)| aag_s : forall s,    Aag (String "A"%char (String "A"%char (String "G"%char s))).
Lemma combi'_complete : forall n s, Word' n s -> In s (combi' n).
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
Lemma combi'_correct : forall n s, In s (combi' n) -> Word' n s.
Proof.
induction n.
 intros. simpl in *. destruct H.
  rewrite <- H. apply empty_word.
 elim H.
induction s.
 intro. unfold combi in H; fold combi in H.
 assert(forall c s, (fun x => String c x) s <> EmptyString).
  intros. intro. discriminate H0.
 assert(forall c ss,   ~In EmptyString (map (fun x => String c x) ss)).
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
 assert(forall a c s ss,   In (String a s) (map (fun x => String c x) ss) -> a = c).
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
assert(forall a c s ss,  In (String a s) (map (fun x => String c x) ss) -> In s ss).
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
Lemma hasAAG_correct1 : forall s,
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
Lemma hasAAG_correct2 : forall s,  Aag s -> hasAAG' s = true.
Proof.
induction s.
 intro. inversion H.
intro. inversion H.
 simpl. rewrite (IHs H1). auto.
simpl. destruct (hasAAG' s0); auto.
Qed.
Definition Word''(s:string):Prop := exists s1, exists s2, s = (s1 ++ "AAG" ++ s2)%string.
Fixpoint range(n:nat):list nat :=match n with| O => nil| S n' => n' :: (range n')end.
Eval compute in (range 4).
Definition ans_aux(N n:nat):list string :=flat_map (fun s => map   (fun s' => s ++ "AAG" ++ s')%string (combi' n))   (combi' (N-n-3)).

Eval compute in (ans_aux 4 0).
Definition ans(N:nat) :=flat_map (fun n => ans_aux N n) (range (N-2)).
Eval compute in (ans(4)).

