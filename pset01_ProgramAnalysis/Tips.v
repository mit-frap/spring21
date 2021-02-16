(*|
A few things to keep in mind as you work through pset 1
=======================================================
|*)

Require Import Frap.

(*|
Coq resources
-------------

- Start by looking for examples in the course textbook, including the tactic appendix at the end of the book.

- For help on standard Coq tactics, consult Coq's reference manual (https://coq.inria.fr/distrib/current/refman/), starting from the indices at https://coq.inria.fr/distrib/current/refman/appendix/indexes/index.html.  The manual can be overwhelming, so it's best used for looking up fine details.

Useful commands
---------------

Coq comes with many predefined types, functions, and theorems (“objects”).  The most important commands to help you discover them are `Check`, `About`, `Print`, `Search`, and `Compute`.  Try the following examples:

`Check` gives the type of any term, even with holes:
|*)

Check (1 + _).
Check (fun b => match b with true => 0 | false => 1 end).

(*|
`About` gives general information about an object:
|*)

About bool.
About nat.

(*|
`Print` displays the definition of an object:
|*)

Print bool.
Print Nat.add.

(*|
`Search` finds objects.  Its syntax is very flexible:
|*)

(* Find functions of type [nat -> nat -> bool]. *)
Search (nat -> nat -> bool).
(* Find theorems about "+". *)
Search "+".
(* Find theorems whose statement mentions S and eq. *)
Search eq S.
(* Search for a lemma proving the symmetry of eq. *)
Search (?x = ?y -> ?y = ?x).

(*|
If you are puzzled by a notation, the `Locate` command can help:
|*)

Locate "*".

(*|
To evaluate an expression, use `Compute`:
|*)

Compute (2 * 3, 4 + 4, 0 - 2 + 2, pred (S (S (S 0)))).

(*|
Syntax recap
------------

To define a function inline, use `fun`:
|*)

Check (fun x => x + 1).
Check (fun x: bool => xorb x x).

(*|
To perform a case analysis on a value, use `match`:
|*)

Check (fun b (x y: nat) =>
         match b with
         | true => x
         | false => y
         end).

Check (fun (n: nat) =>
         match n with
         | 0 => 1
         | S n => n
         end).

(*|
In Coq, `if` is just short for `match`:
|*)

Check (fun (b: bool) (x y: nat) =>
         if b then x else y).

(*|
To define a global object, use `Definition` or `Lemma` (`Theorem` is an alias of `Lemma`):
|*)

Definition choose (b: bool) (x y: nat) :=
  if b then x else y.

Compute (choose true 6 822).

Lemma plus_commutes :
  forall x, x = x + 0 + 0.
Proof.
  intros.
  Search (_ + 0).
  rewrite <- plus_n_O.
  rewrite <- plus_n_O.
  equality.
Qed.

(*|
Recursive functions use the keyword `Fixpoint`:
|*)

Fixpoint do_n_times (ntimes: nat) (step: nat -> nat) (start_from: nat) :=
  match ntimes with
  | 0 => start_from
  | S ntimes' => step (do_n_times ntimes' step start_from)
  end.

Compute (6, do_n_times 12 (fun x => x + 65) 42).

(*|
You can use bullets or braces to structure your proofs:
|*)

Lemma both_zero:
  forall x y z: nat, x + y + z = 0 -> x = 0 /\ y = 0 /\ z = 0.
Proof.
  intros x.
  cases x.
  - intros.
    cases y.
    + propositional.
    + simplify.
      invert H.
  - intros y z Heq.
    simplify.
    invert Heq.
Qed.

(*|
A few gotchas
-------------

Natural numbers saturate at 0:
|*)

Compute (3 - 5 + 3).

(*|
The order in which you perform induction on variables matters: if `x` comes before `y` and you induct on `y`, your induction hypothesis will not be general enough.
|*)

Lemma add_comm:
  forall x y: nat, x + y = y + x.
Proof.
  induct y.
  - induct x; simplify; equality.
  - simplify.
    (* `IHy` is valid only for one specific `y` *)
Abort.

Lemma add_comm:
  forall x y: nat, x + y = y + x.
Proof.
  induct x.
  - induct y; simplify; equality.
  - simplify.
    (* `IHx` starts with `forall y`. *)
Abort.

(*|
Here's an example where this subtlety matters:
|*)

Fixpoint factorial (n: nat) :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Fixpoint factorial_acc (n: nat) (acc: nat) :=
  match n with
  | O => acc
  | S n' => factorial_acc n' (n * acc)
  end.

(*|
First attempt, but our lemma is too weak.
|*)

Lemma factorial_acc_correct:
  forall n, factorial n = factorial_acc n 1.
Proof.
  induct n.
  - equality.
  - simplify.
    Search (_ * 1).
    rewrite Nat.mul_1_r.

(*|
Stuck!  We have no way to simplify `factorial_acc n (S n)`.
|*)

Abort.

(*|
Second attempt: a generalized lemma, but we put the `acc` first, so induction will not generalize it.
|*)

Lemma factorial_acc_correct:
  forall acc n, factorial n * acc = factorial_acc n acc.
Proof.
  induct n.
  - simplify.
    Search (_ + 0).
    rewrite Nat.add_0_r.
    equality.
  - simplify.
    Fail rewrite <- IHn.

(*|
Stuck!  IHn is too weak.
|*)

Abort.

(*|
Third time's the charm!  Note how we ordered `n` and `acc`.
|*)

Lemma factorial_acc_correct:
  forall n acc, factorial n * acc = factorial_acc n acc.
Proof.
  induct n.
  - simplify.
    linear_arithmetic.
  - simplify.

(*|
IHn is strong enough now!
|*)

    rewrite <- IHn.
    linear_arithmetic.
Qed.
