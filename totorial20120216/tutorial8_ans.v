Require Import Arith.
Require Import Omega.
Require Import List.

Section Monoid.
Class Monoid(S:Set) : Type := {
  op : S -> S -> S;
  e : S;
  left_id : forall x, op e x = x;
  right_id : forall x, op x e = x;
  assoc : forall x y z, op (op x y) z = op x (op y z)
}.
Notation "a :+: b" := (op a b)
 (left associativity, at level 50).
Instance nat_monoid:Monoid nat:= {
  op := plus;
  e := O
}.
Proof.
  intros. omega.
 intros. omega.
intros. omega.
Defined.

Eval compute in (2 :+: 3).

Class Monad (M:Type -> Type):Type := {
  return' : forall {A}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B;
  left_unit : forall A B (a:A)(f:A -> M B), bind (return' a) f = f a;
  right_unit : forall A (ma:M A), bind ma return' = ma;
  associativity : forall A B C (ma:M A)(f:A->M B)(g:B->M C),
    bind (bind ma f) g = bind ma (fun a => bind (f a) g)
}.

Notation "m >>= f" := (bind m f) (left associativity, at level 49).
Notation "'do' a <- e ; c" := (e >>= (fun a => c)) (at level 59, right associativity).

Definition id'(A:Type):Type := A.

Instance Identity : Monad id' := {
 return' A a := a;
 bind A B ma f := f ma
}.
Proof.
  intros A B a f. auto.
 intros A ma. auto.
intros A B C ma f g. auto.
Defined.

Instance Maybe : Monad option := {
 return' A a := Some a;
 bind A B ma f :=
   match ma with
   | None => None
   | Some a => f a
   end
}.
Proof.
  intros A B a f. auto.
 intros A m. destruct m; auto.
intros A B C m f g. destruct m; simpl; auto.
Defined.

Eval compute in (None >>= (fun x => Some (x + 1))).
Eval compute in (Some 1 >>= (fun x => Some (x + 1))).

Require Import List.

Lemma flat_map_app : forall (A B:Type)(xs ys:list A)(f:A -> list B),
 flat_map f (xs++ys) = flat_map f xs ++ flat_map f ys.
Proof.
induction xs.
 simpl. auto.
simpl. intros. erewrite IHxs. erewrite app_ass. auto.
Qed.

Instance List : Monad list := {
  return' A x := x :: nil;
  bind A B m f := flat_map f m
}.
Proof.
  intros A B a f. simpl. erewrite <- app_nil_end. auto.
 intros A m. induction m.
  simpl. auto.
 simpl. rewrite IHm. auto.
intros A B C m f g. induction m.
 simpl. auto.
simpl. rewrite <- IHm.
erewrite flat_map_app. auto.
Defined.

Class MonadPlus (M:Type -> Type) : Type := {
 (* MonadPlus is Monad *)
  monad :> Monad M ;
 (* field *)
  mzero : forall A, M A;
  mplus : forall A, M A -> M A -> M A;
 (* axiom *)
  mzero_left : forall A f, bind (@mzero A) f = (@mzero A);
  mzero_right : forall A B (ma:M A), bind ma (fun x => (@mzero B)) = (@mzero B);
  monoid_left_unit : forall A (ma:M A), mplus _ (@mzero A) ma = ma;
  monoid_right_unit : forall A (ma:M A), mplus _ ma (@mzero A) = ma;
  monoid_assoc : forall A (ma mb mc:M A), mplus _ (mplus _ ma mb) mc = mplus _ ma (mplus _ mb mc)
}.

Instance MaybePlus : MonadPlus option := {
 monad := Maybe;
 mzero A := @None A;
 mplus A m1 m2 :=
   match m1 with
   | None => m2
   | Some x => m1
   end
}.
Proof.
    intros A f. simpl. auto.
   intros A B ma. simpl. destruct ma; auto.
  intros A ma; auto.
 intros A ma; destruct ma; auto.
intros A ma mb mc.
destruct ma; destruct mb; destruct mc; auto.
Defined.

Instance ListPlus : MonadPlus list := {
 monad := List;
 mzero A := @nil A;
 mplus A m1 m2 := m1 ++ m2
}.
Proof.
    intros A f. simpl. auto.
   intros A B ma. induction ma; simpl; auto.
  intros A ma; auto.
 intros A ma. erewrite <- app_nil_end. auto.
intros A ma mb mc. erewrite app_ass. auto.
Defined.

Require Import Logic.FunctionalExtensionality.

Definition cont (R A:Type):Type := (A->R)->R.

Instance Cont R : Monad (cont R) := {
 return' A a := fun k:A->R => k a;
 bind A B m f := fun k:B->R => m (fun a => f a k)
}.
Proof.
  intros A B a f. unfold cont in *.
  erewrite <- eta_expansion.  reflexivity.
 intros A ma.  unfold cont in *.  
 erewrite eta_expansion.  extensionality x.
 erewrite <- eta_expansion.  auto.
intros A B C ma f g.  reflexivity.
Defined.
