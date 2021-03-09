Require Import Lia Frap Datatypes.
Require Import Compare_dec.

Notation t := nat.

Inductive tree :=
| Leaf (* an empty tree *)
| Node (d : t) (l r : tree).

Notation compare := Compare_dec.lt_eq_lt_dec.
Notation Lt := (inleft (left _)) (only parsing).
Notation Eq := (inleft (right _)) (only parsing).
Notation Gt := (inright _) (only parsing).

Module Type S.
  Definition Singleton (v: t) := Node v Leaf Leaf.
  Parameter bst : forall (tr : tree) (s : t -> Prop), Prop.

  Parameter rotate : tree -> tree.

  (*[10%]*) Axiom bst_rotate : forall T s (H : bst T s), bst (rotate T) s.

  Fixpoint insert (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Singleton a
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (insert a lt) rt
      | Eq => tr
      | Gt => Node v lt (insert a rt)
      end
    end.

  Fixpoint rightmost (tr: tree) : option t :=
    match tr with
    | Leaf => None
    | Node v _ rt =>
      match rightmost rt with
      | None => Some v
      | r => r
      end
    end.

  Definition is_leaf (tr : tree) : bool :=
    match tr with Leaf => true | _ => false end.

  Fixpoint delete_rightmost (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      if is_leaf rt
      then lt
      else Node v lt (delete_rightmost rt)
    end.

  Definition merge_ordered lt rt :=
    match rightmost lt with
    | Some rv => Node rv (delete_rightmost lt) rt
    | None => rt
    end.

  Fixpoint delete (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (delete a lt) rt
      | Eq => merge_ordered lt rt
      | Gt => Node v lt (delete a rt)
      end
    end.

  (*[40%]*) Axiom bst_insert :
    forall tr s a,
      bst tr s ->
      bst (insert a tr) (fun x => s x \/ x = a).

  (*[50%]*) Axiom bst_delete :
    forall tr s a, bst tr s ->
              bst (delete a tr) (fun x => s x /\ x <> a).
End S.

(* three-way comparisions and [cases] support for them *)
Ltac cases E :=
  (is_var E; destruct E) ||
    match type of E with
    | sumor (sumbool _ _) _ => destruct E as [[]|]
    | {_} + {_} => destruct E
    | _ => let Heq := fresh "Heq" in
           destruct E eqn:Heq
    end;
   repeat
    match goal with
    | H:_ = left _ |- _ => clear H
    | H:_ = right _ |- _ => clear H
    | H:_ = inleft _ |- _ => clear H
    | H:_ = inright _ |- _ => clear H
    end.
