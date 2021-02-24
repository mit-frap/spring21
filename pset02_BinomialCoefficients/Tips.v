Require Import Coq.NArith.NArith.
Open Scope N_scope.
Require Import Frap.Frap.
Require Import Pset2.
Import Pset2.Impl.

Notation "x !" := (fact x) (at level 12, format "x !"). (* local in Pset2 *)

(* This file demonstrates a number of useful Coq tactics.  Step though the
   examples, and check Coq's reference manual or ask us in office hours if
   you're confused about any of these tactics.

   There are no exercises to complete in this file, just neat examples; feel
   free to work on it at your pace over multiple psets and to refer to it at
   later points; no need to go through it all at once.  *)

(* The tactic we introduce in each example is underlined like this. *)
                                             (********************)

Parameter whatever: Prop.

(* ‘apply’ matches the conclusion of a theorem to the current goal, then
   replaces it with one subgoal per premise of that theorem: *)

Goal forall (P Q R: Prop) (H1: P) (H2: Q) (IH: P -> Q -> R), R.
Proof.
  simplify.
  apply IH.
 (********)
Abort.

(* Apply works with implications (`A -> B`) but also with equivalences, where
   it tries to pick the right direction based on the goal: *)
Goal forall (n m k: N), n = m.
Proof.
  simplify.
  Check N.mul_cancel_r.

  (* Careful: apply only works if it's clear how the theorem applies to your goal: *)
  Fail apply N.mul_cancel_r.
  (* Here, Coq wants to know the value of ‘p’ before it can apply the lemma; so,
     we use the ‘with’ for of ‘apply’ to supply it: *)
  apply N.mul_cancel_r with (p := n - k + 1).
 (****)               (****)
Abort.

(* Apply also works in hypotheses, where it tuns premises into conclusions: *)
Goal forall (n m k: N), n = m -> whatever.
Proof.
  simplify.
  apply N.mul_cancel_r with (p := n - k + 1) in H.
 (*****)              (****)                (**)
Abort.

Goal forall (n m k: N), n - k + 1 <> 0 -> n = m -> whatever.
Proof.
  simplify.

  (* Specifying parameters by hand is not always convenient, so we can ask Coq
     to create placeholders instead, to be filled later: *)
  eapply N.mul_cancel_r in H0.
 (******)              (**)
  2: { (* This ‘2:’ notation means: operate on the second goal *)
    apply H.
  } (* … and the curly braces delimit a subproof. *)
Abort.

Goal forall (P Q R S: Prop), (P -> S) -> (R -> S) -> P \/ Q \/ R -> S.
Proof.
  simplify.
  cases H1. (* You are familiar with ‘cases’ from pset 1. *)
 (*****)
  - apply H. apply H1.
  - admit. (* ‘admit’ is just like ‘Admitted’ but for a single goal *)
   (*****)
  - apply H0. apply H1.
Fail Qed. (* But if you use ‘admit’, no ‘Qed’ for you! *)
Admitted.

(* Here is a convenient pattern that you will be familiar with from math
   classes.  It's called a “cut”.  We state an intermediate fact and prove it
   as part of a larger proof. *)

Goal forall (f : N -> N) (count : N)
       (IHcount : forall i start : N, i < count ->
                                 ith i (seq f count start) = f (start + i))
       (i start : N)
       (H : i < count + 1),
  ith i (f start :: seq f count (start + 1)) = f (start + i).
Proof.
  simplify.

  (* ‘assert’ introduces the fact that we want to prove, then uses *)
  assert (i = 0 \/ 0 < i) as A. { (* the ‘as’ clause to name the resulting fact *)
 (******)                (**)
    linear_arithmetic.          (* The proof of the lemma comes first. *)
  }
  cases A.                      (* Then we get to use the lemma itself. *)
  - subst. (* ‘subst’ rewrites all equalities. *)
   (*****)  (* or "subst i" for just one var *)
    simplify. admit.
  - (* Another assertion! This time we fit the whole proof in a ‘by’ clause. *)
    assert (i = i - 1 + 1) as E by linear_arithmetic.
   (******)                    (**)
    rewrite E.
    unfold_recurse ith (i - 1).
Abort.

Goal forall (n x0 k: N),
    0 < k ->
    k + 1 < n ->
    n! = x0 * ((n - (k - 1))! * (k - 1)!) ->
    whatever.
Proof.
  intros n m.
 (******)
  (* ‘simplify’ takes care of moving variables into the “context” above the
     line, but ‘intros’ gives finer grained control and lets you name
     hypotheses.  Users of Proof General with company-coq can type ‘intros!’ to
     get names automatically inserted. *)
  intros. (* A plain ‘intros’ takes care of all remaining variables. *)
  (******)

  (* Sometimes we want to say “a = b, so replace all ‘a’s with ‘b’s.”.  Replace
     is the perfect tactic for these cases; it's like ‘assert’ followed by
     ‘rewrite’. *)
  replace (n - (k - 1)) with (n - k + 1) in H1 by linear_arithmetic.
 (*******)             (****)           (**)  (**)
  (* "in" and "by" are optional *)
  unfold_recurse fact (n - k).
Abort.

Goal forall (P Q R: Prop) (H0: Q) (x: N) (H: forall (a b: N), P -> Q -> a < b -> R), whatever.
Proof.
  simplify.
  (* Often you have a general hypothesis, and you want to make it more specific
     to your case.  Then, ‘specialize’ is the tactic you want: *)
  specialize H with (b := x).
 (**********) (****)
  assert (3 < x) by admit.
  specialize H with (2 := H0) (3 := H1).
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.

  (* We have seen ‘apply’ earlier, which applies a theorem ending with an
     implication to a complete goal.  ‘rewrite’ takes theorems ending in an
     equality and replaces matching subterms of the goal according to that
     equality: *)
  rewrite N.add_0_r.
 (*******)
  (* Options like "with (a := 2)", "in H", "by tactic" also work! *)
  equality.
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  (* Alternatively, sometimes, it helps to apply the principle that, if two
     function arguments match, then the function calls themselves match: *)
  f_equal.
 (*******)
  linear_arithmetic.
Abort.

Goal forall (f : N -> N) (start : N),
    f start = f (start + 0).
Proof.
  simplify.
  (* How many other ways can we find to deal with this theorem? *)
  assert (start + 0 = start) as E by linear_arithmetic.
  rewrite E.
Abort.

Goal forall (A B: Type) (f: A -> B) (a1 a2 a3: A),
    Some a1 = Some a2 ->
    Some a2 = Some a3 ->
    f a3 = f a1.
Proof.
  (* ‘simplify’ is a favorite of this class, which does all sorts of small goal
     reorganization to make things more readable. *)
  simplify.

  (* ‘invert’ is another favorite: it “replaces hypothesis H with other facts that can be deduced from the structure of H's statement”.

     Specifically, it looks at the structure of the arguments passed to the
     constructor of inductive types appearing in H and deduces equalities from
     that and then substitutes the equalities.  It's also particularly useful
     for inductive ‘Prop’s, which we will see later in this class. *)
  invert H. (* Watch what happens carefully in this example *)
 (******)
  invert H0.
  equality.
Abort.

Goal forall (A B: Type) (f: A -> B) (a1 a2 a3: A),
    Some a1 = Some a2 ->
    Some a2 = Some a3 ->
    f a3 = f a1.
Proof.
  simplify.
  equality. (* Of course, ‘equality’ can do all the work for us here. *)
 (********)
Abort.

Goal forall (a1 a2 b1 b2: N) (l1 l2: list N),
    a1 :: b1 :: l1 = a2 :: b2 :: l2 ->
    a1 = a2 /\ b1 = b2 /\ l1 = l2.
Proof.
  simplify.
  (* ‘invert’ works at arbitrary depth, btw: *)
  invert H.
 (******)
Abort.

(* If you ever end up with contradictory hypotheses, you'll want to apply the
   pompously named “ex falso quodlibet” principle (also known under the
   scary-sounding name of “principle of explosion”), through the aptly named
   ‘exfalso’ tactic: *)
Goal forall (P: Prop) (a b: N),
    (a < b -> ~P) ->
    P ->
    whatever.
Proof.
  simplify.
  assert (a < b \/ b <= a) as C by linear_arithmetic. cases C.
  - exfalso.
   (*******)
    unfold not in H.
    apply H.
    all: assumption.
Abort.

(* Contradictions can take many forms; a common one is Coq is an impossible equality between two constructors; here the empty list ‘[]’ and a non-empty list ‘a :: l’. *)
Goal forall (a : N) (l : list N),
    a :: l = [] ->
    whatever.
Proof.
  simplify.
  discriminate.
 (************)
Abort.

Goal forall (P Q R S T: Prop), (P \/ Q -> T) -> (R \/ S -> T) -> P \/ S -> T.
Proof.
  simplify.
  cases H1.
  - apply H. left. assumption.
  - apply H0. right. assumption.
Abort.

(* Here are some more interesting tactics to look into along your Coq journey.
   Happy proving!

   - constructor, econstructor
   - eassumption
   - eexists
   - first_order
   - induct
   - left, right
   - trivial
   - transitivity
   - symmetry
*)

(* References:

   - FRAP book Appendix A.2. Tactic Reference (http://adam.chlipala.net/frap/frap_book.pdf)
   - Coq Reference Manual, Chapter on Tactics (https://coq.inria.fr/refman/proof-engine/tactics.html)
*)
