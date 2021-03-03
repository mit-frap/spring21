(** * 6.822 Formal Reasoning About Programs, Spring 2021 - Pset 3 *)

Require Import Frap.Frap.

(* three-way comparisions, and [cases] support for them *)
Notation Lt := (inleft (left _)) (only parsing).
Notation Eq := (inleft (right _)) (only parsing).
Notation Gt := (inright _) (only parsing).
Notation compare := Compare_dec.lt_eq_lt_dec.

Module Type S.
  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  Definition either {A} (xo yo : option A) : option A :=
    match xo with
    | None => yo
    | Some x => Some x
    end.


  (* 1a) HOFs: id and compose *)

  Definition id {A : Type} (x : A) : A := x.
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (*[0.5%]*)
  Parameter compose_id_l : forall (A B : Type) (f : A -> B), compose id f = f.

  (*[0.5%]*)
  Parameter compose_id_r : forall (A B : Type) (f : A -> B), compose f id = f.

  (*[1%]*)
  Parameter compose_assoc :
    forall (A B C D : Type) (f : A -> B) (g : B -> C) (h : C -> D),
      compose h (compose g f) = compose (compose h g) f.

  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => compose f (selfCompose f n')
    end.

  Parameter exp : nat -> nat -> nat.
  (*[0.25%]*)
  Parameter test_exp_3_2 : exp 3 2 = 9.
  (*[0.25%]*)
  Parameter test_exp_4_1 : exp 4 1 = 4.
  (*[0.25%]*)
  Parameter test_exp_5_0 : exp 5 0 = 1.
  (*[0.25%]*)
  Parameter test_exp_1_3 : exp 1 3 = 1.

  (* 1b) HOFs: Left inverses *)

  Definition left_inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := compose g f = id.

  (*[1%]*)
  Parameter plus2minus2 : left_inverse (fun x : nat => x + 2) (fun x : nat => x - 2).

  (*[2.5%]*)
  Parameter minus2plus2 : ~ left_inverse (fun x : nat => x - 2) (fun x : nat => x + 2).

  (*[4%]*)
  Parameter left_invertible_injective:
    forall {A} (f g: A -> A),
      left_inverse f g ->
      (forall x y, f x = f y -> x = y).

  (*[0.25%]*)
  Parameter left_inverse_id : forall {A : Type}, left_inverse (@id A) (@id A).

  (*[8%]*)
  Parameter invert_selfCompose :
    forall {A : Type} (f g : A -> A) (n : nat), left_inverse f g -> left_inverse (selfCompose f n) (selfCompose g n).

  (* 2a) Simple containers *)

  (*[0.25%]*)
  Parameter either_None_right : forall {A : Type} (xo : option A), either xo None = xo.

  (*[0.5%]*)
  Parameter either_assoc :
    forall {A : Type} (xo yo zo : option A), either (either xo yo) zo = either xo (either yo zo).

  Parameter head : forall {A : Type}, list A -> option A.

  (*[1%]*)
  Parameter head_example : head (1 :: 2 :: 3 :: nil) = Some 1.

  (*[1%]*)
  Parameter either_app_head :
    forall {A : Type} (xs ys : list A), head (xs ++ ys) = either (head xs) (head ys).

  Parameter leftmost_Node : forall {A : Type}, tree A -> option A.

  (*[1%]*)
  Parameter leftmost_Node_example : leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf) = Some 2.

  (*[4%]*)
  Parameter leftmost_Node_head : forall {A : Type} (t : tree A), leftmost_Node t = head (flatten t).


  (* 2b) bitwise tries *)

  Definition bitwise_trie A := tree (option A).

  Parameter lookup : forall {A : Type}, list bool -> bitwise_trie A -> option A.

  (*[1%]*)
  Parameter lookup_example1 : lookup nil (Node Leaf (None : option nat) Leaf) = None.

  (*[1%]*)
  Parameter lookup_example2 :
    lookup (false :: true :: nil)
           (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf)) =
    Some 1.

  (*[1%]*)
  Parameter lookup_empty : forall {A : Type} (k : list bool), lookup k (Leaf : bitwise_trie A) = None.

  Parameter insert : forall {A : Type}, list bool -> option A -> bitwise_trie A -> bitwise_trie A.

  (*[1%]*)
  Parameter insert_example1 : lookup nil (insert nil None (Node Leaf (Some 0) Leaf)) = None.

  (*[1%]*)
  Parameter insert_example2 :
    lookup nil (insert (true :: nil) (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.

  (*[8%]*)
  Parameter lookup_insert :
    forall {A : Type} (k : list bool) (v : option A) (t : bitwise_trie A), lookup k (insert k v t) = v.

  (*[2%]*)
  Parameter map_id : forall {A : Type} (xs : list A), List.map id xs = xs.

  (*[3%]*)
  Parameter map_compose :
    forall (A B C : Type) (g : B -> C) (f : A -> B) (xs : list A),
      List.map (compose g f) xs = List.map g (List.map f xs).

  (*[4%]*)
  Parameter invert_map :
    forall (A B : Type) (f : A -> B) (g : B -> A), left_inverse f g -> left_inverse (List.map f) (List.map g).

  (* 2c) HOFs: tree_map *)

  Parameter tree_map : forall {A B : Type}, (A -> B) -> tree A -> tree B.

  (*[1%]*)
  Parameter tree_map_example :
    tree_map (fun x : nat => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf))) =
    Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf)).

  (*[8%]*)
  Parameter tree_map_flatten :
    forall (A B : Type) (f : A -> B) (t : tree A), flatten (tree_map f t) = List.map f (flatten t).

  Fixpoint tree_forall {A} (P: A -> Prop) (tr: tree A) :=
    match tr with
    | Leaf => True
    | Node l d r => tree_forall P l /\ P d /\ tree_forall P r
    end.

  Parameter tree_exists : forall {A: Type}, (A -> Prop) -> tree A -> Prop.

  (*[0.5%]*)
  Parameter tree_exists_Leaf :
    forall (A : Type) (P : A -> Prop), ~ tree_exists P Leaf.
  (*[3%]*)
  Parameter tree_forall_exists :
    forall (A : Type) (P : A -> Prop) (tr : tree A),
      tr <> Leaf -> tree_forall P tr -> tree_exists P tr.

  (*[2%]*)
  (* Explain what tree_forall_sound means *)

  (*[3%]*)
  Parameter tree_forall_sound :
    forall (A : Type) (P : A -> Prop) (tr : tree A),
      tree_forall P tr -> forall d : A, tree_exists (fun d' : A => d' = d) tr -> P d.

  (* 2d) Binary search trees *)

  Fixpoint listset (l: list nat) (s: nat -> Prop) :=
    match l with
    | [] =>
      (* An empty list represents an empty set *)
      forall x, ~ s x
    | hd :: tl =>
      (* Note how we remove an element from the propositional set: *)
      s hd /\ listset tl (fun x => x <> hd /\ s x)
    end.

  Fixpoint list_member (a: nat) (l: list nat) :=
    match l with
    | [] => false
    | hd :: tl =>
      if a ==n hd then true else list_member a tl
    end.

  (*[4%]*)
  Parameter list_member_lset: forall l s a,
      listset l s ->
      list_member a l = true <-> s a.

  (*[3%]*)
  Parameter list_member_lset': forall l s a,
      listset l s ->
      list_member a l = false <-> ~ (s a).

  Definition list_insert (a: nat) (l: list nat) :=
    if list_member a l then l else a :: l.

  (*[8%]*)
  Parameter list_insert_listset : forall l s a,
      listset l s ->
      listset (list_insert a l)
              (fun x => s x \/ x = a).

  Fixpoint bst (tr : tree nat) (s : nat -> Prop) :=
    match tr with
    | Leaf => forall x, not (s x) (* s is empty set *)
    | Node l d r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (*[3%]*)
  Parameter bst_implies :
    forall (tr : tree nat) (s : nat -> Prop), bst tr s -> tree_forall s tr.

  (*[1%]*)
  Parameter bst_node_ordered :
    forall (l : tree nat) (d : nat) (r : tree nat) (s : nat -> Prop),
      bst (Node l d r) s ->
      tree_forall (fun x : nat => x < d) l /\ tree_forall (fun x : nat => x > d) r.

  (*[5%]*)
  Parameter bst_iff :
    forall (tr : tree nat) (P Q : nat -> Prop),
      bst tr P -> (forall x : nat, P x <-> Q x) -> bst tr Q.

  Fixpoint bst_member (a: nat) (tr: tree nat) : bool :=
    match tr with
    | Leaf => false
    | Node lt v rt =>
      match compare a v with
      | Lt => bst_member a lt
      | Eq => true
      | Gt => bst_member a rt
      end
    end.

  (*[10%]*)
  Parameter member_bst :
    forall (tr : tree nat) (s : nat -> Prop) (a : nat),
      bst tr s -> bst_member a tr = true <-> s a.
End S.

(* Here's a technical note on why this pset overrides a Frap tactic.
   There's no need to understand this at all.

   The "simplify" tactic provided by the Frap library is not quite suitable for this
   pset, because it does "autorewrite with core in *" (which we commented out below),
   and there's a Hint in Coq.Program.Combinators

        Hint Rewrite <- @compose_assoc : core.

   which causes "autorewrite with core in *." to have the
   same effect as

   rewrite <-? Combinators.compose_assoc.

   and apparently, rewrite does not just syntactic matching,
   but matching modulo unification, so it will replace
   our "compose" by "Basics.compose", and rewrite using
   associativity of "compose" as many times as it can.
   It's confusing to have "Basics.compose" appear in our goals,
   and rewriting with associativity is something we want to teach in this
   pset, so we redefine "simplify" to not use "autorewrite": *)
Ltac simplify ::=
  repeat (unifyTails; pose proof I); repeat match goal with
                                            | H:True |- _ => clear H
                                            end;
   repeat progress (simpl in *; intros(*; try autorewrite with core in * *); simpl_maps);
   repeat normalize_set || doSubtract.

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
