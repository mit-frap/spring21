(*|
===================================================================
 6.822 Formal Reasoning About Programs, Spring 2021 - Pset 9 Hints
===================================================================

Using Hoare logic
=================

The strength of Hoare logic is how well it lends itself to automation, so it's natural to be tempted to just run `ht` on every goal.  This is not a bad idea!  But as you get started, it's best to spend a bit of time familiarizing yourself with the way `ht1` works, first, to get a feeling of the way the proofs work.

In particular, note that using `ht1` and `ht` *can* lead to incorrect goals: this is due to the while loop rule: it checks that the invariant that you provide holds at the beginning of the loop and that it is preserved by the loop, and then it gives you that invariant at the end of the loop (plus the negation of the loop condition).

Ask yourself: what happens if you use `fun/inv _ _ _ => True` as your invariant?  What about `fun/inv _ _ _ => False`?

Writing invariants
------------------

The key difficulty of this pset is figuring out the right invariant for each problem.  You want something that is weak enough to be true before the loop start and to remain true across loop iterations (under the assumption that the loop condition holds) and that is strong enough to prove your final postcondition.

In general, it pays to make the invariant as precise as possible.


Tips for this pset
==================

Fibonacci
---------

Our invariant says two things: the trace is “valid”, and the latest values in the output correspond to the values of the local variables `x` and `y`.

Factorial
---------

This one is similar to the previous one, but with two extra twists: a condition on the value of the variable `"n"` relative to the parameter `n` and a condition on the value of the variable `cnt` (the first one is needed because the loop rule forgets everything that is not explicitly part of the invariant).

Mailbox
-------

Our invariant for this problem is very short; it checks if `done` is 0 and says something slightly different in both cases.

Search
------

The invariant here combines tricks from the previous invariants:

- A condition on the value of the `ptr` variable
- A condition on the value of the `length` variable
- A relation between the parameters `ptr` and `data`
- A well-formedness criterion for the partial stream of output.

The last one is the trickiest.  Here is some intuition (spoilers ahead):

- After running to completion, we want the program to obey `search_done`, which is essentially the same as `exists needle, search_spec needle …`.  The `exists` part is needed because we don't know what the needle will be when we start the program.  But when we get to the loop we have the needle: it's in `v $! "needle"`.

- Now we need to phrase a form of `search_spec` for the stream of results up to a point.  We had the same issue in factorial (stating that the program had run up to `n`).  Ask yourself: which part of the list have we processed after, say, 3 iterations?  What will be the value of `v $! "length"` at that point?

- Can you straightforwardly compute the list of elements that has already been processed?  You might find one of the `List.skipn` and `List.firstn` functions useful.  Once you do that, can you use the result to state a `search_spec` property?

- Finally, you'll want to make sure that when `length` reaches 0, your prefix is empty or your suffix covers the whole list, so that you recover a `search_spec` predicate about the complete list, which is exactly the program's postcondition.

Here are two lemmas about these functions that might prove useful (our proof only uses one of these):
|*)

Require Import Pset9Sig.

Lemma firstn_S_app:
  forall (data : list nat) (n : nat),
    S n <= Datatypes.length data ->
    firstn (S n) data =
    firstn n data ++ [nth n data 0].
Proof.
  induct data; simplify.
  - linear_arithmetic.
  - cases n; simplify; eauto using f_equal with arith.
Qed.

Lemma skipn_sub_app:
  forall (data : list nat) (n : nat),
    0 < n <= Datatypes.length data ->
    List.skipn (n - 1) data =
    List.nth (n - 1) data 0 :: List.skipn n data.
Proof.
  induct data; simplify.
  - linear_arithmetic.
  - assert (n = 1 \/ n - 1 = S (n - 1 - 1)) as Heq by linear_arithmetic.
    cases Heq; rewrite Heq.
    + reflexivity.
    + replace n with (S (n - 1)) at 3 by linear_arithmetic.
      simplify; apply IHdata; linear_arithmetic.
Qed.

(*|
One you've phrased your invariant using `List.firstn` or `List.skipn`, the main difficulty will be reasoning about the relation between `array_at` and the heap.  In our solution, we used the following two lemmas (phrased in slightly strange ways, chosen to play well with our automation):
|*)

Require Import Pset9.
Import Impl.

Lemma array_at_nth_eq :
  forall data ptr (h: heap) n x,
    array_at h ptr data ->
    S n <= Datatypes.length data ->
    h $! (ptr + n) = x ->
    nth n data 0 = x.
Admitted.

Lemma array_at_nth_neq :
  forall data ptr (h: heap) n x,
    array_at h ptr data ->
    S n <= Datatypes.length data ->
    h $! (ptr + n) <> x ->
    nth n data 0 <> x.
Admitted.

(*|
Good luck!
|*)
