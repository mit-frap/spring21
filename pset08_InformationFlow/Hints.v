(*|
============================================
 Hints for Pset 8: Information-flow control
============================================
|*)

Require Import Frap.Frap.

(*|
The `set` type
==============

- `set A` is a set of values of type `A`.

- Common operators include `x \in s` (membership), `s1 \subseteq s2`
  (inclusion), `s1 \cup s2` (union).  Because of the way sets are implemented,
  `x \in s` is the same as `s x`.

- Sets can be used in conjunction with maps: `restrict s m` computes a new map
  from `m` with all variables in set `s` removed.

- If you find yourself proving properties of sets, especially regarding
  `restrict`, try the `sets` tactic — it often helps.

- If you want to reason on whether a particular element `k` is in set `s`, you
  can use the `excluded_middle` tactic, as `excluded_middle (k \in s)`.

Here is an example demonstrating some of these points (remember that, to prove
equality on maps, you can use the `maps_equal` tactic):
|*)

Goal forall {K V} (k: K) (v: V) (s: set K) (m: fmap K V),
    k \in s ->
    restrict s (m $+ (k, v)) = (restrict s m) $+ (k, v).
Proof.
  simplify.
  maps_equal.
  - rewrite lookup_restrict_true.
    + simplify; equality.
    + eassumption.
  - excluded_middle (k0 \in s).
    + rewrite !lookup_restrict_true by assumption.
      simplify; equality.
    + rewrite !lookup_restrict_false by assumption.
      equality.
Qed.

(*|
Tips
====

- You will need to generalize the theorem statement to prove it by induction.

- The noninterference property says that running a program in states with private variables holding potentially different values does not change the public outputs of the program.

  The key difficulty is to deal with *divergence* — the cases where the two program executions take different paths.

  1. When does this happen?  How does that translate in terms of the variables in `pc`?
  2. Can a divergent execution affect the value of public variables?

- Some of your theorems will take a `Confidential … c` premise.  In the case of a while loop, `invert`-ing `Confidential pub pc (While e body)` will give you, `Confidential pub (pc \cup vars e)`, but you will lose the original `Confidential pub pc (While e body)` fact.  In our proof, we had to reprove it (you could also make a copy of it) a few times, to apply a theorem to the `eval _ (While _ _) _` premise of the `EvalWhileTrue` constructor.  (This hint will make more sense when you get there.)

Good luck!
|*)
