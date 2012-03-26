(* Based on K. Arkoudas and S. Bringsjord
  "Metareasoning for multi-agent epistemic logics"
  http://people.csail.mit.edu/kostas/papers/CLIMA2004.pdf *)

Inductive agent:Set :=
| A : nat -> agent.

Inductive prop:Set :=
| T : prop (* True *)
| F : prop (* False *)
| P : nat -> prop (* Atomic proposition *)
| Not : prop -> prop
| And : prop -> prop -> prop
| Or : prop -> prop -> prop
| Imp : prop -> prop -> prop
| K : agent -> prop -> prop (* Knows *)
| C : prop -> prop. (* Common knowledge *)

Notation "! p" := (Not p) (at level 20).
Notation "p && q" := (And p q).
Notation "p || q" := (Or p q).
Notation "p --> q" := (Imp p q) (right associativity, at level 70).

Require Import Sets.Ensembles.

Notation "p :: G" := (Add prop G p).
Notation "G1 _+_ G2" := (Union prop G1 G2) (right associativity, at level 30).
Definition O := Empty_set prop.

Lemma union_comm : forall U V:(Ensemble prop), U _+_ V = V _+_ U.
Proof.
intros. eapply Extensionality_Ensembles. unfold Same_set.
unfold Included. 
split.
 intros x H; inversion H;
 [eapply Union_intror | eapply Union_introl]; auto.
intros x H; inversion H;
[eapply Union_intror | eapply Union_introl]; auto.
Qed.

Lemma union_assoc : forall U V W:(Ensemble prop), 
 (U _+_ V) _+_ W = U _+_ (V _+_ W).
Proof.
intros. eapply Extensionality_Ensembles. unfold Same_set.
unfold Included. split.
 intros. inversion H.
  inversion H0.
   eapply Union_introl; auto.
  eapply Union_intror; eapply Union_introl; auto.
 eapply Union_intror; eapply Union_intror; auto.
intros. inversion H.
 eapply Union_introl; eapply Union_introl; auto.
inversion H0.
 eapply Union_introl; eapply Union_intror; auto.
eapply Union_intror; auto.
Qed.

Lemma add_comm : forall G p q, p::q::G = q::p::G.
Proof.
intros. unfold Add. repeat rewrite union_assoc.
replace (Singleton prop q _+_ Singleton prop p) with
 (Singleton prop p _+_ Singleton prop q).
 reflexivity.
rewrite union_comm. reflexivity.
Qed.

Reserved Notation "G |-- p" (at level 90, no associativity).

Inductive theorem : (Ensemble prop) -> prop -> Prop :=
| intro_and : forall G p q, (G |-- p) -> (G |-- q) -> (G |-- (p && q))
| elim_and_l : forall G p q, (G |-- (p && q)) -> (G |-- p)
| elim_and_r : forall G p q, (G |-- (p && q)) -> (G |-- q)
| intro_or_l : forall G p q, (G |-- p) -> (G |-- (p || q))
| intro_or_r : forall G p q, (G |-- q) -> (G |-- (p || q))
| elim_or : forall G p1 p2 q, 
   (G |-- (p1 || p2)) -> ((p1::G) |-- q) -> ((p2::G) |-- q) -> (G |-- q)
| intro_imp : forall G p q, ((p::G) |-- q) -> (G |-- (p --> q))
| elim_imp : forall G p q, (G |-- (p --> q)) -> (G |-- p) -> (G |-- q)
| elim_not : forall G p, (G |-- !(!p)) -> (G |-- p)
| intro_not : forall G p, ((p::G) |-- F) -> (G |-- !p)
| reflex : forall G p, (p::G) |-- p
| dilution : forall G G' p, (G |-- p) -> ((G _+_ G') |-- p)
| intro_false : forall G p, (G |-- (p && (!p))) -> (G |-- F)
| intro_true : forall G, G |-- T
| rule_K : forall G a p q, G |-- ((K a (p --> q)) --> (K a p --> K a q))
| rule_T : forall G a p, G |-- (K a p --> p)
| intro_C : forall G p, (O |-- p) -> (G |-- (C p))
| elim_C : forall G a p, G |-- (C p --> K a p)
| rule_C_K : forall G p q, G |-- ((C (p --> q)) --> (C p --> C q))
| rule_R : forall G a p, G |-- (C p --> C (K a p))
where "G |-- p" := (theorem G p).

(* Ltac definition is not perfect. Sometimes it does not
   work well, and I could not fix the problems. *)
Ltac mintro :=
 match goal with
 | [ |- (?G |-- (?p --> ?q)) ] => eapply intro_imp 
 end.
Ltac mintros := repeat mintro.
Ltac msplit :=
 match goal with
 | [ |- (?G |-- (?p && ?q)) ] => eapply intro_and
 end.
Ltac mleft :=
 match goal with
 | [ |- (?G |-- (?p || ?q)) ] => eapply intro_or_l
 end.
Ltac mright :=
 match goal with
 | [ |- (?G |-- (?p || ?q)) ] => eapply intro_or_r
 end.
Ltac mdestruct H :=
 match type of H with
 | ?G |-- (?p || ?q) => eapply (elim_or _ _ _ _ H)
 | ?G |-- (?p && ?q) => assert((G |-- p) /\ (G |-- q)) by
                        (split; [eapply elim_and_l | eapply elim_and_r])
 end.
Ltac mapply H :=
 match type of H with
 | ?G |-- (?p --> ?q) => eapply (elim_imp G p q H)
 end.
Ltac mauto :=
 try auto;
 match goal with
 | [ |- (?p::?G) |-- ?p ] => eapply reflex
 | [ |- (?p::?G) |-- ?q ] => eapply dilution; try mauto
 end.

Ltac mknow a :=
 match goal with
 | [ |- ?G |-- ?p ] => apply (elim_imp G (K a p) p (rule_T G a p))
 end.

Ltac distK H :=
 specialize(elim_imp _ _ _ (rule_K _ _ _ _) H); intro.
Ltac distC H :=
 specialize(elim_imp _ _ _ (rule_C_K _ _ _) H); intro.
Ltac common :=
 match goal with
 | [ |- ?G |-- K ?a ?p ] => apply (elim_imp G (C p) (K a p) (elim_C G a p))
 | [ |- ?G |-- C (K ?a ?p) ] => apply (elim_imp G (C p) (C (K a p)) (rule_R G a p))
 end.
Ltac introC :=
 match goal with
 | [ |- ?G |-- (C ?p) ] => apply (intro_C G p)
 end.

Lemma Falso : forall G p, (G |-- F) -> (G |-- p).
Proof.
intros. eapply elim_not. eapply intro_not. mauto. 
Qed.
Ltac mfalso := eapply Falso.

Ltac mcontra p :=
 match goal with
 | [ |- ?G |-- _ ] => (mfalso;
                       apply (intro_false G p);
                       apply (intro_and G p (!p));
                       mauto)
 end.

Lemma omniscience_axiom : forall G a p, (O |-- p) -> (G |-- K a p).
Proof.
intros. common. introC. auto.
Qed.

Lemma cut_theorem : forall G1 G2 p1 p2, (G1 |-- p1) -> ((p1 :: G2) |-- p2)
 -> ((G1 _+_ G2) |-- p2).
Proof.
intros.
eapply (elim_imp _ p1 p2).
 erewrite union_comm. eapply dilution. mintro. auto.
eapply dilution. auto.
Qed.

Ltac madd p H := 
 match type of H with
 | ?G |-- ?q => assert((p::G) |-- q) by (eapply dilution; auto)
 end.

Lemma imp_trans : forall G p1 p2 p3, 
  (G |-- p1 --> p2) -> (G |-- p2 --> p3) -> (G |-- p1 --> p3).
Proof.
intros. mintro.
madd p1 H0. mapply H1.
madd p1 H. mapply H2. mauto.
Qed.

Lemma contrapositive : forall G p q, (G |-- p --> q) -> (G |-- !q --> !p).
Proof.
intros. mintro. eapply intro_not.
eapply (intro_false _ q). msplit.
 madd (!q) H. madd p H0. mapply H1. mauto.
mauto.
Qed.

Lemma lemma4a : forall p1 p2, O |-- (p1 || p2) --> ((!p2) --> p1).
Proof.
intros. mintros. 
assert(!p2 :: p1 || p2 :: O |-- !p2) by mauto.
assert(!p2 :: p1 || p2 :: O |-- (p1 || p2)) by mauto.
mdestruct H0.
 mauto.
mcontra p2.
Qed.

Lemma lemma4b : forall G p1 p2,
 (O |-- p1 --> p2) -> (G |-- C p1) -> (G |-- C p2).
Proof.
intros.
specialize(intro_C G _ H). intros.
distC H1. mapply H2. auto.
Qed.

Lemma lemma5 : forall G p q, G |-- ((C p && C q) --> C (p && q)).
intros.
eapply intro_imp.
assert(O |-- p --> q --> p && q). mintros. msplit; mauto.
assert(C p && C q :: G |-- C (p --> q --> p && q)). introC. auto.
assert(C p && C q :: G |-- C p && C q). mauto. 
assert(C p && C q :: G |-- C p).
 eapply (elim_and_l (C p && C q :: G) (C p) (C q)). mauto. 
assert(C p && C q :: G |-- C q).
 eapply (elim_and_r (C p && C q :: G) (C p) (C q)). mauto.
distC H0.
specialize(elim_imp _ _ _ H4 H2). intro.
distC H5.
mapply H6. mauto.
Qed.

(* A1 may wear red hat (=M1) or white hat (= !M1).
   A2 may wear red hat (=M2) or white hat (= !M2). *) 
Parameter A1 A2: agent.
Parameter M1 M2: prop.
(* S1 = A1 that said "I do not know whether I wears a red hat".
        Therefore, prop "A1 does not know M1", 
        is commom knowledge. *)
Definition S1 := C (!(K A1 M1)).
(* S2 = Because the king said "At least one of A1 and A2
        wears the red hat". Therefore "M1 or M2" is
        common knowledge. *)
Definition S2 := C(M2 || M1).
(* S3 = Because A1 can see the A2's hat, A1 would know
        !M2 if !M2 stood, and this is common knowledge. *)
Definition S3 := C(!M2 --> K A1 (!M2)). 
(* After A1 said "I do not know whether I wears a red hat",
   using the common knowledge {S1, S2, S3}, it becomes the
   common knowledge that A2 wears the red hat. *) 
Theorem two_wise_men : S1::S2::S3::O |-- C M2.
Proof.
assert(HS1: S1::S2::S3::O |-- S1). mauto.
assert(HS2: S1::S2::S3::O |-- S2). mauto. 
assert(HS3: S1::S2::S3::O |-- S3). mauto. 
remember (S1 :: S2 :: S3 :: O) as G.
unfold S1 in *. unfold S2 in *. unfold S3 in *.
assert(O |-- (M2 || M1) --> (!M2 --> M1)).
 mintros.
 assert(!M2 :: M2 || M1 :: O |-- M2 || M1). mauto.
 eapply (elim_or _ _ _ _ H).
  mcontra M2.
 mauto.
assert(O |-- (!K A1 M1) --> (K A1 (!M2 --> M1)) --> 
 (!M2 --> K A1 (!M2)) --> M2).
 mintros.
 assert(R3:(!M2 --> K A1 (!M2)) :: K A1 (!M2 --> M1) :: !K A1 M1 :: O 
  |-- (!M2 --> K A1 (!M2))) by mauto. 
 assert(R2:(!M2 --> K A1 (!M2)) :: K A1 (!M2 --> M1) :: !K A1 M1 :: O 
  |-- K A1 (!M2 --> M1)) by mauto.
 assert(R1:(!M2 --> K A1 (!M2)) :: K A1 (!M2 --> M1) :: !K A1 M1 :: O 
  |-- !K A1 M1) by mauto.
 remember ((!M2 --> K A1 (!M2)) :: K A1 (!M2 --> M1) :: !K A1 M1 :: O) as G'.
 distK R2.
 assert(R5: G' |-- !M2 --> K A1 M1).
  eapply (imp_trans _ _ _ _ R3 H0).
 eapply elim_not. eapply intro_not.
 madd (!M2) R5. madd (!M2) R1.
 assert(!M2 :: G' |-- !M2) by mauto.
 specialize(elim_imp _ _ _ H1 H3). intro.
 eapply (intro_false _ (K A1 M1)).
 msplit; mauto.
specialize (intro_C G _ H0). intro.
distC H1.
specialize (elim_imp _ _ _ H2 HS1). intro.
distC H3.
specialize (intro_C G _ H). intro.
distC H5.
specialize (elim_imp _ _ _ H6 HS2). intro.
specialize (rule_R G A1 (!M2 --> M1)). intro.
specialize (elim_imp _ _ _ H8 H7). intro.
specialize (elim_imp _ _ _ H4 H9). intro.
distC H10.
mapply H11. auto.
Qed.
