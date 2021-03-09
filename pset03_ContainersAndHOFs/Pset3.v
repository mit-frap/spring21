(** * 6.822 Formal Reasoning About Programs, Spring 2021 - Pset 3 *)

Require Import Frap.Frap.
Require Import Pset3Sig.

Module Impl.
  (* In this pset, we will practice two topics:
     1) Polymorphic container types, i.e. types which are parametrized by a
        type, such as "option A", "list A", "tree A", and finally, "bitwise_trie A",
        which combines option and tree to obtain a new useful data structure.
     2) Higher-order functions (HOFs), i.e. functions which take other functions
        as arguments.

     Remember that we post hints on the website!  Consult them if you're stuck.
  *)

  (* As usual, the grading rubric for this pset is in Pset3Sig.v. *)

  (** ** Higher-order functions **)

  (* Recall the identity function [id] we used in class, which just returns its
     argument without modification: *)
  Definition id {A : Type} (x : A) : A := x.

  (* We also saw [compose], another higher-order function: [compose g f]
   * applies [f] to its input and then applies [g]. Argument order
   * follows the general convention of functional composition in
   * mathematics denoted by the small circle.
   *)
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (* Let's use a small circle to refer to [compose]. This will make our
     goals much more readable.
     It's up to you to decide whether you also want to use the circle notation
     in your definitions or whether you prefer to write "compose".

     Users of Emacs with company-coq can simply type \circ RET
     to insert ∘ *)
  Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

  (* Here are three simple properties of function composition.
     Together, these properties mean that functions with ∘ form
     a “monoid”. *)

  (* Hint: In the following, it might be helpful to use the following fact:
     If two functions return the same value for all inputs, they are the same. *)
  Check @FunctionalExtensionality.functional_extensionality.
  (* Aside: We called it a "fact" above, but logicians disagree about whether
     we should believe this or not -- maybe you remember Adam's argument from
     class that even if merge sort and bubble sort return the same result for
     all inputs, they are two different things.
     Therefore, this "fact" is not actually built into Coq's kernel, but it's
     an axiom written down in the standard library, and if you believe in it,
     you can import it (the Frap library already does so).
     In any case, it is consistent with the rest of Coq's logic, i.e. by
     assuming this axiom, you will not be able to prove False, so we're safe.*)

  (* Let's make a shorthand for this: *)
  Definition fun_ext := @FunctionalExtensionality.functional_extensionality.

  Lemma compose_id_l : forall A B (f: A -> B),
      id ∘ f = f.
  Proof.
  Admitted.

  Lemma compose_id_r : forall A B (f: A -> B),
      f ∘ id = f.
  Proof.
  Admitted.

  Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
      h ∘ (g ∘ f) = h ∘ g ∘ f.
  Proof.
  Admitted.

  (* The selfCompose function takes a function and applies this function n times
     to the argument. There are different ways of defining it, but let's
     define it using only [id] and [compose]. *)
  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => f ∘ (selfCompose f n')
    end.

  (* Here's an example of what [selfCompose] can do:
     If we apply the function which adds 2 to its argument 7 times to the starting
     value 3, we obtain 3 + 7 * 2 = 17. *)
  Example selfCompose_plus1: selfCompose (plus 2) 7 3 = 17. Proof. equality. Qed.

  (* We can also use [selfCompose] to define exponentiation on natural numbers, by
     saying "to raise [base] to the power [e], apply the function which multiplies
     its argument by [base] to [1] [e] times".
     Define [exp] using [selfCompose] and [Nat.mul]. *)
  Definition exp(base e: nat): nat. Admitted.

  (* Once you define [exp], you can replace [Admitted.] below by [Proof. equality. Qed.] *)
  Lemma test_exp_2_3: exp 2 3 = 8. Admitted.
  Lemma test_exp_3_2: exp 3 2 = 9. Admitted.
  Lemma test_exp_4_1: exp 4 1 = 4. Admitted.
  Lemma test_exp_5_0: exp 5 0 = 1. Admitted.
  Lemma test_exp_1_3: exp 1 3 = 1. Admitted.

  (* And here's another example to illustrate [selfCompose]. Make sure you understand
     why its result is 256. *)
  Example selfCompose_square: selfCompose (fun (x: nat) => x * x) 3 2 = 256. Proof. equality. Qed.

  (** ** Inverse functions **)

  (* Using [compose] and [id], we can write a concise definition of when
     a function [g] is the left inverse of a function [f]: *)
  Definition left_inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := g ∘ f = id.

  (* Here's an example: The function which subtracts two from its argument
     is the left inverse of the function which adds two to its argument. *)
  Example plus2minus2: left_inverse (fun (x: nat) => x + 2) (fun (x: nat) => x - 2).
  Proof.
  Admitted.

  (* On the other hand, note that the other direction does not hold, because
     if a subtraction on natural numbers underflows, it just returns 0, so
     there are several [x] for which [x-2] returns 0 (namely 0, 1, and 2),
     so it can't have a left inverse. *)
  Example minus2plus2: ~ left_inverse (fun (x: nat) => x - 2) (fun (x: nat) => x + 2).
  Proof.
  Admitted.

  (* Let us make the intuition from the previous paragraph more
     concrete, by proving that a function that is not injective
     cannot have a left inverse; or, in other words, that
     functions with left inverses are injective. *)
  Lemma left_invertible_injective {A}:
    forall (f g: A -> A),
      left_inverse f g ->
      (forall x y, f x = f y -> x = y).
  Proof.
  Admitted.

  (* Bonus question (no points): can you prove the reverse;
     i.e., can you prove that all injective functions have left
     inverses? *)

  (* The identity function is the inverse of itself.
     Note: we're using "@" in front of "id" to say "we want to provide all implicit
     type arguments explicitly, because otherwise Coq would not be able to infer them." *)
  Lemma left_inverse_id: forall A, left_inverse (@id A) (@id A).
  Proof.
  Admitted.


  (* Now we can start proving interesting facts about inverse functions: *)
  (* Here's how to invert the power function: *)
  Lemma invert_selfCompose{A: Type}: forall (f g: A -> A) (n: nat),
      left_inverse f g ->
      left_inverse (selfCompose f n) (selfCompose g n).
  Proof.
  Admitted.

  (** ** Polymorphic container types *)

  (* First, we'll reproduce some definitions we need from Lecture 2,
     [tree] and [flatten]: *)

  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  (* And here's one additional definition that we'll use in this problem set.
   * [either] combines two [option] values into one.
   * If either argument to [either] is a [Some], then so is
   * the result of the [either], preferring the contents of
   * the first argument if both are [Some].
   *
   * We will observe an "analogy" between the [either]
   * function on options and the [++] function on lists.
   *)
  Definition either {A} (xo yo : option A) : option A :=
    match xo with
    | None => yo
    | Some x => Some x
    end.

  (* If we [either] an [option] value with [None]
   * on the right, it leaves that value unchanged,
   * (just as if we put the [None] on the left).
   * This is analogous to how appending [nil]
   * on either side of a list leaves it unchanged.
   *)
  Theorem either_None_right : forall {A} (xo : option A),
      either xo None = xo.
  Proof.
  Admitted.

  (* [either] is associative, just like [++]. *)
  Theorem either_assoc : forall {A} (xo yo zo : option A),
      either (either xo yo) zo = either xo (either yo zo).
  Proof.
  Admitted.

  (* [head] should compute the head of a list, that is,
   * it should return [Some] with the first element of
   * the list if the list is nonempty, and [None]
   * if the list is empty.
   *)
  Definition head {A} (xs : list A) : option A. Admitted.

  Example head_example : head [1; 2; 3] = Some 1.
  Proof.
  Admitted.

  (* The following theorem makes a formal connection
   * between [either] and [++].
   *)
  Theorem either_app_head : forall {A} (xs ys : list A),
      head (xs ++ ys) = either (head xs) (head ys).
  Proof.
  Admitted.


  (* [leftmost_Node] should compute the leftmost node of
   * a tree.
   *
   * Please implement [leftmost_Node] directly using
   * recursion (i.e., pattern matching) on the [tree] argument,
   * without using the [flatten] operation.
   *)
  Fixpoint leftmost_Node {A} (t : tree A) : option A. Admitted.

  Example leftmost_Node_example :
      leftmost_Node (Node (Node Leaf 2 (Node Leaf 3 Leaf)) 1 Leaf)
      = Some 2.
  Proof.
  Admitted.

  (* Prove that the leftmost node of the tree is the same
   * as the head of the list produced by flattening the tree
   * with an in-order traversal.
   *)
  Theorem leftmost_Node_head : forall {A} (t : tree A),
      leftmost_Node t = head (flatten t).
  Proof.
  Admitted.

  (* Bitwise trie are finite maps keyed by lists of Booleans.
   * We will implement a bitwise trie with entries of type [A]
   * by [tree (option A)]. The value at the root of the tree
   * corresponds to the entry for the key [nil : list bool],
   * the left subtree contains entries for those keys that
   * begin with [true], and the right subtree contains entries
   * for those keys that begin with [false].
   *
   * Tries are a common and powerful data structure; you can read
   * more about them at https://en.wikipedia.org/wiki/Trie .
   *)
  Definition bitwise_trie A := tree (option A).

  (* Define [lookup] such that [lookup k t] looks up the
   * map entry corresponding to the key [k : list bool] in the
   * bitwise trie [t : bitwise_trie A], interpreting [t] such that
   * the value at the root of [t] corresponds to the
   * entry for the key [nil], the left subtree contains entries
   * for those keys that begin with [true], and the right subtree
   * contains entries for those keys that begin with [false].
   *
   * Look at the examples below to get a better sense of what
   * this operation does: the argument [k] is a path, in which
   * [true] means "go left" and [false] means "go right".
   *)
  Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A. Admitted.

  Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
  Proof.
  Admitted.

  Example lookup_example2 : lookup [false; true]
      (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                            = Some 1.
  Proof.
  Admitted.

  (* [Leaf] represents an empty bitwise trie, so a lookup for
   * any key should return [None].
   *)
  Theorem lookup_empty {A} (k : list bool)
    : lookup k (Leaf : bitwise_trie A) = None.
  Proof.
  Admitted.


  (* Define an operation to "insert" a key and optional value
   * into a bitwise trie. The [insert] definition should satisfy two
   * properties: one is [lookup_insert] below, which says that if we
   * look up a key [k] in a trie where [(k, v)] has just been inserted,
   * the result should be [v]. The other is that lookups on keys different
   * from the one just inserted should be the same as on the original map.
   *
   * If an entry for that key already exists, [insert] should replace
   * that entry with the new one being inserted. Note that [insert] can
   * be used to remove an entry from the trie, too, by inserting [None]
   * as the value.
   *
   * Hint: it may be helpful to define an auxiliary function
   * that creates a singleton tree (a tree containing a single
   * key-value pair).
   *)
  Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct t}
    : bitwise_trie A. Admitted.

  Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
  Proof.
  Admitted.

  Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
  Proof.
  Admitted.

  Theorem lookup_insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) :
    lookup k (insert k v t) = v.
  Proof.
  Admitted.

  (** ** HOFs on lists and trees **)

  (* If we map the [id] function over any list, we get the
   * same list back.
   *)
  Theorem map_id : forall {A : Type} (xs : list A),
      map id xs = xs.
  Proof.
  Admitted.

  (* If we map the composition of two functions over a list,
   * it's the same as mapping the first function over the whole list
   * and then mapping the second function over that resulting list.
   *)
  Theorem map_compose : forall {A B C : Type} (g : B -> C) (f : A -> B) (xs : list A),
      map (g ∘ f) xs = map g (map f xs).
  Proof.
  Admitted.

  (* If g is the inverse of f, then [map g] is the inverse of [map f]: *)
  Lemma invert_map : forall A B (f: A -> B) (g: B -> A),
      left_inverse f g ->
      left_inverse (map f) (map g).
  Proof.
  Admitted.

  (* Just like we defined [map] for lists, we can similarly define
   * a higher-order function [tree_map] which applies a function on
   * elements to all of the elements in the tree, leaving the tree
   * structure intact.
   *)
  Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
    : tree B. Admitted.

  Example tree_map_example :
    tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
    = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
  Proof.
  Admitted.

  (* [tree_map_flatten] shows that [map]
   * and [tree_map] are related by the [flatten] function.
   *)
  Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
      flatten (tree_map f t) = map f (flatten t).
  Proof.
  Admitted.

  (* This function asserts that a predicate holds over all
     elements of a tree. *)
  Fixpoint tree_forall {A} (P: A -> Prop) (tr: tree A) :=
    match tr with
    | Leaf => True
    | Node l d r => tree_forall P l /\ P d /\ tree_forall P r
    end.

  (* Define a similar function for the [exists] case; that is, define
     a function that asserts that a predicate holds for at least
     one value of a tree. *)
  Fixpoint tree_exists {A} (P: A -> Prop) (tr: tree A) {struct tr} : Prop.
  Admitted.

  (* Two sanity checks for your function: *)
  Lemma tree_exists_Leaf {A} (P: A -> Prop):
    ~ tree_exists P Leaf.
  Proof.
  Admitted.

  Lemma tree_forall_exists {A} (P: A -> Prop):
    forall tr, tr <> Leaf -> tree_forall P tr -> tree_exists P tr.
  Proof.
  Admitted.

  (* What does the following theorem mean? Write a short
     explanation below. *)


  Lemma tree_forall_sound {A} (P: A -> Prop):
    forall tr, tree_forall P tr ->
          forall d, tree_exists (fun d' => d' = d) tr ->
               P d.
  Proof.
  Admitted.

  (** ** Binary search trees **)

  (* Like tries, binary search trees (BSTs) are a popular way to
     store structured data.  We will use them to implement a set
     data type, with methods to insert a new element, remove an
     existing element, and check whether the set contains a
     given element.

     Proving a complete BST implementation in a week is a bit
     too much at this point in the term, so we will start this
     week with definitions and correctness proofs for membership
     tests. *)

  (* BSTs will allow us to illustrate an important idea: data
     abstraction, the general principle that data structures
     should expose interfaces that abstract over (i.e., hide)
     the complexities of their internal representation.  Data
     abstraction is a key ingredient of modularity in most
     programming languages.

     Concretely, this means that client code using our set
     library built with BSTs shouldn't have to think about
     binary trees at all: instead, we'll write all specs in
     terms of abstract sets, representing a set of values of
     type [A] using the type [A -> Prop].

     Wrapping your head around this can be a bit tricky the
     first time, so let's start with list-based sets instead.
     Keeping with the idea of data abstraction, we will provide
     the exact same API and prove the same theorems about
     list-based sets as we will with BST-based sets.

     First, our representation invariant. [listset l s] means
     that the list l contains exactly the elements of the set
     [s].  That set is encoded as function that takes a [t] and
     returns the proposition "[t] is in this set". *)

  Fixpoint listset (l: list nat) (s: nat -> Prop) :=
    match l with
    | [] =>
      (* An empty list represents an empty set *)
      forall x, ~ s x
    | hd :: tl =>
      (* Note how we remove an element from the propositional set: *)
      s hd /\ listset tl (fun x => x <> hd /\ s x)
    end.

  (* The following lemma may turn out to be useful; it says that
     if two propositional sets have the same elements, they
     characterize the same listsets. *)

  Lemma listset_same_elements:
    forall l s1,
      listset l s1 ->
      forall s2,
        (forall x, s1 x <-> s2 x) ->
        listset l s2.
  Proof.
    induct l; simplify.
    - rewrite <- H0. (* Tip: you can rewrite with equivalences, not just equalities! *)
      trivial.
    - propositional.
      rewrite <- H0; trivial.
      apply IHl with (s1 := (fun x : nat => x <> a /\ s1 x)).
      + trivial.
      + simplify.
        rewrite H0.
        propositional.
  Qed.

  (* We can now define methods on listsets: *)

  Fixpoint list_member (a: nat) (l: list nat) :=
    match l with
    | [] => false
    | hd :: tl =>
      if a ==n hd then true else list_member a tl
    end.

  (* How do we specify this membership test?  By relating it to
     the set that the listset represents.

     Hint: [not P] in Coq means [P -> False]; use [unfold not] to reveal
     that.  If you find yourself with inconsistent hypotheses,
     like [h: P] and [H': P -> False], you can use [exfalso] to
     change the goal to [False].

     Hint 2: Pay special attention to the [s] that you use when
     applying the induction hypothesis. *)

  Lemma list_member_lset: forall l s a,
      listset l s ->
      list_member a l = true <-> s a.
  Proof.
  Admitted.

  (* This lemma should be a direct consequence of the previous
     one: no need for induction. *)
  Lemma list_member_lset': forall l s a,
      listset l s ->
      list_member a l = false <-> ~ (s a).
  Proof.
  Admitted.

  (* Inserting an element in a listset is easy, but we must make
     sure that the element isn't already in the list (do you see
     why?): *)

  Definition list_insert (a: nat) (l: list nat) :=
    if list_member a l then l else a :: l.

  (* How do we specify insertion?  By relating it to
     the set that the listset represents. *)

  Lemma list_insert_listset : forall l s a,
      listset l s ->
      listset (list_insert a l)
              (fun x => s x \/ x = a).
  Proof.
  Admitted.

  (* Now let's do the same with sets implemented as BSTs:

     The representation predicate for BSTs is a bit more
     complex, because it asserts two things: that the tree is
     related to a given propositional set *and* that the tree
     is well-formed (i.e., that it is indeed structured as a
     BST).

     The [bst] predicate below relates a well-formed binary
     search tree to the set of elements it contains. Note that
     invalid trees with misordered elements are not valid
     representations of any set. All operations on a binary tree
     are specified in terms of how they affect the set that the
     tree represents. *)

  Fixpoint bst (tr : tree nat) (s : nat -> Prop) :=
    match tr with
    | Leaf => forall x, ~ (s x) (* s is empty set *)
    | Node l d r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (* First, let's get familiar with this definition by proving
     that [bst tr s] implies that all elements of [tr] have
     property [s].  Recall that you may need to prove a stronger
     lemma than the one we show here.  If you get stuck, check
     out the Hints page on the website! *)


  Lemma bst_implies:
    forall tr s, bst tr s -> tree_forall s tr.
  Proof.
  Admitted.

  (* Next, let's prove that elements of the left subtree of a
     BST node are less than the node's data, and that all
     elements of the right subtree are greater than it.  This
     should be a consequence of the lemma you proved for
     [bst_implies]; our solution does not use induction here. *)

  Lemma bst_node_ordered :
    forall l d r s,
      bst (Node l d r) s ->
      tree_forall (fun x => x < d) l /\ tree_forall (fun x => x > d) r.
  Proof.
  Admitted.

  (* Here is another convenient property: if two sets are the
     same, then a bst representing one also represents the
     other.  If you have trouble with this proof, consult the
     proof of [listset_same_elements] above.  *)

  Lemma bst_iff : forall tr P Q,
      bst tr P ->
      (forall x, P x <-> Q x) ->
      bst tr Q.
  Proof.
  Admitted.

  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)

  (* Data abstraction!  The API and proofs of [bst_member] and
     [list_member] are same! *)

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

  Lemma member_bst : forall tr s a,
      bst tr s -> bst_member a tr = true <-> s a.
  Proof.
  Admitted.

  (* Next week, we will look at insertion and deletion in
     BSTs. *)

  (** ****** Optional exercises ****** *)

  (* Everything below this line is optional! *)

  (* You've reached the end of the problem set. Congrats!
   *
   * If you're up for a completely optional additional challenge,
   * try defining a left-biased merge function below that merges two
   * bitwise tries, preferring map entries from the first bitwise trie
   * when an entry exists for both bitwise tries. Then prove
   * [lookup_left_biased_merge], which formally states that lookups
   * on the merged bitwise trie operate in exactly this manner.
   *
   * If you don't want to complete this additional challenge, you
   * can just leave everything below unmodified.
   *)

  Fixpoint left_biased_merge {A} (t t' : bitwise_trie A) : bitwise_trie A. Admitted.

  Theorem lookup_left_biased_merge {A} (k : list bool) (t t' : bitwise_trie A) :
    lookup k (left_biased_merge t t') = either (lookup k t) (lookup k t').
  Proof.
  Admitted.


  (* And here are a few more optional exercises about [fold]: *)

  (* [fold] is a higher-order function that is even more general
   * than [map]. In essence, [fold f z] takes as input a list
   * and produces a term where the [cons] constructor is
   * replaced by [f] and the [nil] constructor is replaced
   * by [z].
   *
   * [fold] is a "right" fold, which associates the bitwise operation
   * the opposite way as the [fold_left] function from Coq's
   * standard library.
   *)
  Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
           (xs : list A) : B :=
    match xs with
    | nil => b_nil
    | cons x xs' => b_cons x (fold b_cons b_nil xs')
    end.

  (* For instance, we have
         fold plus 10 [1; 2; 3]
       = 1 + (2 + (3 + 10))
       = 16
   *)
  Example fold_example : fold plus 10 [1; 2; 3] = 16.
  Proof.
    simplify.
    equality.
  Qed.

  (* Prove that [map] can actually be defined as a particular
   * sort of [fold].
   *)
  Lemma map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
      map f xs = fold (fun x ys => cons (f x) ys) nil xs.
  Proof.
  Admitted.

  (* Since [fold f z] replaces [cons] with [f] and [nil] with
   * [z], [fold cons nil] should be the identity function.
   *)
  Theorem fold_id : forall {A : Type} (xs : list A),
      fold cons nil xs = xs.
  Proof.
  Admitted.

  (* If we apply [fold] to the concatenation of two lists,
   * it is the same as folding the "right" list and using
   * that as the starting point for folding the "left" list.
   *)
  Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                               (xs ys : list A),
      fold f z (xs ++ ys) = fold f (fold f z ys) xs.
  Proof.
  Admitted.

  (* Using [fold], define a function that computes the
   * sum of a list of natural numbers.
   *)
  Definition sum : list nat -> nat. Admitted.

  Example sum_example : sum [1; 2; 3] = 6.
  Proof.
  Admitted.

  (* Using [fold], define a function that computes the
   * conjunction of a list of Booleans (where the 0-ary
   * conjunction is defined as [true]).
   *)
  Definition all : list bool -> bool. Admitted.

  Example all_example : all [true; false; true] = false.
  Proof.
  Admitted.


  (* The following two theorems, [sum_append] and [all_append],
   * say that the sum of the concatenation of two lists
   * is the same as summing each of the lists first and then
   * adding the result.
   *)
  Theorem sum_append : forall (xs ys : list nat),
      sum (xs ++ ys) = sum xs + sum ys.
  Proof.
  Admitted.


  Theorem all_append : forall (xs ys : list bool),
      all (xs ++ ys) = andb (all xs) (all ys).
  Proof.
  Admitted.

  (* Using [fold], define a function that composes a list of functions,
   * applying the *last* function in the list *first*.
   *)
  Definition compose_list {A : Type} : list (A -> A) -> A -> A. Admitted.

  Example compose_list_example :
    compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
  Proof.
  Admitted.


  (* Show that [sum xs] is the same as converting each number
   * in the list [xs] to a function that adds that number,
   * composing all of those functions together, and finally
   * applying that large composed function to [0].
   * Note that function [plus], when applied to just one number as an
   * argument, returns a function over another number, which
   * adds the original argument to it!
   *)
  Theorem compose_list_map_add_sum : forall (xs : list nat),
      compose_list (map plus xs) 0 = sum xs.
  Proof.
  Admitted.
End Impl.

Module ImplCorrect : Pset3Sig.S := Impl.

(* Authors:
 * Ben Sherman,
 * Adam Chlipala,
 * Samuel Gruetter
 * Clément Pit-Claudel
 *)
