(*  AGCT in Coq *)
 
Require Import List.
 
Inductive dna : Type :=
  | A : dna
  | G : dna
  | C : dna
  | T : dna.
 
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
 
Fixpoint selection_aux(n:nat)(xs:list (list dna)):list (list dna) :=
match n with
| O => xs
| S n' => let ys := selection_aux n' xs in
  fold_left 
    (fun stat x => stat ++ (map (fun s => x :: s) ys)) 
    [A, G, C, T]    
    []
end.
Definition selection(n:nat) := selection_aux n [[]].
 
Definition beq_dna (a b : dna) : bool :=
  match a, b with
  | A, A => true
  | G, G => true
  | C, C => true
  | T, T => true
  | _, _ => false
  end.
 
Fixpoint match_left (xs ys : list dna) : bool :=
  match xs, ys with
  | [], _ => true
  | x :: xs', [] => false
  | x :: xs', y :: ys' =>
      if beq_dna x y then match_left xs' ys'
               else false
  end.
 
Fixpoint contains_dna (xs ys : list dna) : bool :=
  match ys with
  | [] => false
  | y :: ys' =>
      if match_left xs ys then true
                       else contains_dna xs ys'
  end.
 
Eval compute in filter (fun x => contains_dna [A, A, G] x) (selection 4).
(*
     = [[A, A, A, G], [A, A, G, A], [A, A, G, G], [A, A, G, C], [A, A, G, T],
       [G, A, A, G], [C, A, A, G], [T, A, A, G]]
     : list (list dna)
*)