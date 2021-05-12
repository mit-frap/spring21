Hints for Pset 12
=================

Summarizing the effects of other threads as "rely"
--------------------------------------------------

The challenge of the first problem is of course to come up with the right 'rely' and 'guarantee' and weakened precondition (which needs to be stable).  How can you summarize the effects of other threads in a compact 'rely'?

Here is the one used by our solution:
```
  fork (fun h => h $! 0 >= init)
       (fun h h' => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) h => h $! 0 > init)
       (fun h => h $! 0 >= init)
       (fun h h' => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) h => h $! 0 > init).
```

Soundness strategy
------------------

Our proof template for logic soundness starts as usual by appealing to an 'invariant weaking' lemma and an 'invariant induction' lemma.  We can also call them the 'progress' lemma and the 'preservation' lemma. Roughly, the first one says that commands that have a Hoare triple in the current state are not about to fail, and the second says that if a command with a Hoare triple in the current state takes a step, the resulting command will still have a Hoare triple in the resulting state.

A particularly useful lemma from Pset12Sig that is easily missed is `always_stableP`:

```
Lemma always_stableP : forall (t : Set) P R c G (Q : t -> _),
    hoare_triple P R c G Q -> stableP P R.
```

Progress
--------

We strengthen the invariant to say that some Hoare triple holds of the current program such that the current heap satisfies the precondition of the Hoare triple: `progress` says that this indeed implies that the program is not about to fail:
```
Lemma progress :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h, P h ->
         notAboutToFail c.
```

Preservation
------------

Then the 'invariant induction' lemma says that this is in fact an inductive invariant: `preservation` says that if some Hoare triple holds and the current heap satisfies its precondition and we take a step, then another Hoare triple holds with a particular precondition that holds of the new heap:
```
Lemma preservation :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        hoare_triple (fun h'' => R^* h' h'') R c' G Q.
```

Using guarantee for soundness
-----------------------------

In proving the preservation lemma, you will need to think what the 'guarantee' part of a Hoare triple gives you.  That is, you will need to prove that the 'guarantee' actually guarantees the range of effects. Formally, here is a lemma you will want to prove:
```
Lemma guarantee :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        G^* h h'.
```

Equalities involving existT
---------------------------

When inverting facts involving `cmd`s, you may find that you have
equalities of the form `existT P p x = existT P p y`. The following
tactic derives the equality `x = y` from facts of this sort and
performs substitution. You may find this useful for your soundness
proof of the rely-guarantee logic.
(This tactic performs a subset of what `simp` does.)
So what makes these strange-looking goals pop into existence, anyway?
They arise from inversion on hypotheses involving fancy types.
In general, inversion derives new equalities.  Sometimes a particular
derived equality relates terms whose *types* are computed via some
fancy recipe.  The constructor `existT` is used to package a term together
with its (first-class) type.  Interestingly, the natural inversion
principle, for equalities on those sorts of packages, is not provable in
Coq!  It's actually formally independent of Coq's logic.  However, a
standard-library lemma `inj_pair2` proves the inversion principle from a
more basic axiom.  For more detail (orthogonal to this course), see the
`Eqdep` module of the Coq standard library.
```
Ltac existT_subst :=
   repeat match goal with
   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H
   end; subst.
```
