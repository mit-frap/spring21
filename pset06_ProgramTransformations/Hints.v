(*|
==============
 Pset 6 Hints
==============
|*)

Require Import Pset6Sig.
Module Hints (I: S). Import I.

(*|
General hints
=============

Throughout the pset, think carefully on what you want to be doing induction on: commands, or proofs of `eval`?  In many cases both are possible, but not always: theorems that require reasoning about equivalences between loops will typically not be provable by induction on a command. You might find it useful to review the debriefing for Pset 4 (the link is in the course calendar).

---

Do not assume that all lemmas are directly provable as stated: you will often need intermediate lemmas.  For example, for `eval_deterministic`, you will likely want to prove an variant with premises reordered to get a stronger induction hypothesis.  For `opt_constprop_sound`, you'll want to make a generalized version with an arbitrary `consts` set instead of `$0`.

---

Automation can help with many of the proofs in this psets.  The tactics `eval_intro` and `eval_elim` may be convenient building blocks to use in your own tactics.

To detect an arbitrary match from Ltac, use `match ?x with _ => _ end`:
|*)

Ltac cases_any :=
  match goal with
  | [ |- context[match ?x with _ => _ end] ] => cases x
  end.

Goal (forall x y z: bool, x || y || z || true = true).
Proof.
  unfold orb.
  simplify; repeat cases_any; eauto.
Qed.

(*|
---

Coq's standard library contains many lemmas — you do not need to prove
everything from first principles!  Among other lemmas, our solution uses the
following, which gets automatically picked up by `simplify`.
|*)

Hint Rewrite Nat.mul_0_r Nat.div_1_r Nat.add_0_r.
Hint Rewrite <- Nat.ones_equiv.
Hint Rewrite Nat.mul_1_r Nat.shiftl_mul_pow2 Nat.shiftr_div_pow2 Nat.land_ones.

(*|
As always, use `Search` to find relevant lemmas.

---

Beware of issues with operator precedence:
- `(n - 1) mod 2` is not the same as `n - 1 mod 2`.
- `a $<= b /\ P` is not the same as `(a $<= b) /\ P`

Problem-specific hints
======================

Constant propagation
--------------------

You will have an easier time if you define a function to test for constants, like so:
|*)

Definition as_const (e: expr) : option nat :=
  match e with
  | Const n => Some n
  | _ => None
  end.

(*|
Otherwise, goals will get very large.

----

In the proof of `opt_constprop_sound`, or more likely the strengthened version of it, you will probably find the following lemma useful:
|*)

Lemma includes_remove_add (consts v: valuation) x n:
  consts $<= v ->
  consts $- x $<= v $+ (x, n).
Proof.
  simplify; apply includes_intro; simplify.
  cases (x ==v k); subst; simplify; try equality.
  eauto using includes_lookup.
Qed.

(*|
Loop unrolling
--------------

In the implementation of `read_only`, you can use `if x ==v x0 then true else false` to get a Boolean indicating whether two variables are equal.

---

Programs in this section can get pretty big — consider adding intermediate definitions and proving lemmas about them.  For example, I used this:
|*)

Definition loop1 x body :=
  body;; x <- x - 1.

Lemma opt_unroll_decr : forall {phi v v' x body n},
    eval phi v (loop1 x body) v' ->
    read_only body x = true ->
    v $? x = Some n ->
    v' $? x = Some (n - 1).
Abort.

(*|
The key difficulty in this problem is connecting the unrolled loop body to the original loop body.  Because of the way `EvalWhileTrue` and `EvalWhileFalse` are defined, regular induction gives you two cases: one where the loop exists immediately and one where it runs `n + 1` times.

Instead, you want to think about three cases: the loops exits immediately, the loop runs a single time, and the loop runs `n + 2` times.  The key is to make a lemma that mentions both of these cases at once.  Let's look at a concrete example:
|*)

Fixpoint even (n: nat) :=
  match n with
  | 0 => True
  | 1 => False
  | S (S n) => even n
  end.

Lemma even_sum : forall x y, even x -> even y -> even (x + y).
Proof.
  induct x; simplify.
  - assumption.
  - cases x.
    + equality.
    + simpl.

(*|
This proof is stuck: intuitively, IH steps one step forward, and we want to take two steps at once.
|*)

Abort.

(*|
The trick is to generalize the lemma to assert two "levels":
|*)

Lemma even_sum : forall x y,
    (even x -> even y -> even (x + y)) /\
    (even (S x) -> even y -> even (S x + y)).
Proof.
  induct x.
  - simplify; cases y; first_order.
  - simplify; firstorder.
Qed.

(*|
What does that mean for this pset?  Chances are you'll probably come up with a lemma that looks like this at some point:
|*)

Lemma opt_unroll_template_sound : forall phi v v' x body n,
    n mod 2 = 0 ->
    v $? x = Some n ->
    read_only body x = true ->
    eval phi v (while x loop (loop1 x body) done) v' ->
    eval phi v (while x loop (loop1 x body);; (loop1 x body) done) v'.
Abort.

(*|
… but it won't work by induction.  No, what you need is this, which *will* work by induction:
|*)

Lemma opt_unroll_template_mx_sound : forall phi v v' x body n,
    v $? x = Some n ->
    read_only body x = true ->
    eval phi v (while x loop (loop1 x body) done) v' ->
    eval phi v (if n mod 2 ==n 0 then
                while x loop (loop1 x body);; (loop1 x body) done
              else
                (loop1 x body);;
                while x loop (loop1 x body);; (loop1 x body) done) v'.
Abort.

(*|
One last trick: this form with an `if` is essentially a partially-evaluated version of the full loop-unrolling template, with the “fixup” phase at the beginning.  In other words, you can prove the following theorem:
|*)

Lemma opt_unroll_eqn {phi v v' body x}:
  let n := match v $? x with Some n => n | None => 0 end in
  eval phi v (if n mod 2 ==n 0 then
              while x loop (loop1 x body);; (loop1 x body) done
            else
              (loop1 x body);;
              while x loop (loop1 x body);; (loop1 x body) done) v' ->
  eval phi v (when (x mod 2) then loop1 x body else Skip done;;
            while x loop (loop1 x body);; (loop1 x body) done) v'.
Abort.
