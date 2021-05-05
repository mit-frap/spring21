Hints for Pset 11
=================

META-HINT
---------

If you are stuck trying to prove any fiddly but obvious-seeming fact, say about sets or lists, please ask the course staff for advice!

Most lemma statements are at the bottom of the file; the pset will be more interesting if you start with just the textual hints, and then look at the statements only if you need them!

Structure of the proof
----------------------

The key trick in this proof is two distinguish two cases: does any thread hold a lock, or not?
You can use the `excluded_middle` tactic for this.  See [1] below for the exact invocation we used.

Progress without locking
------------------------

This is the first of two cases: the case in which no thread holds any lock (see [2]).  In that case, can threads get blocked?  If yes, how?  Does the `goodCitizen` assumption rule that case out, and if so what can you say about the progress of each individual thread? [3]

Progress with locking
---------------------

If some lock is taken, we need a bit more work [4].  Unlike the previous case, some threads may in fact be waiting on other threads, and hence cannot make progress.  But, could all threads be blocked?  If not, how can we identify a thread that's ready to run?

We phrased this intuition in the following way (to prove this lemma, you may need [5], a specialized version of it applied to a single command.
)

```
Lemma who_has_the_lock : forall l h a p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> a \in locksOf p
      -> locksOf p \subseteq l
      -> (exists h_l_p', step (h, l, progOf p) h_l_p')
        \/ (exists a', a' < a /\ a' \in l).
```

What this means is that we can either find a command that's ready to run, or we can find another owned lock that is *less than* `a`, the one we already knew had an owner.  If we apply this lemma repeatedly, we will eventually find a command that can run; can you see why? (hint: the key part is a' < a).

Of course, we can't actually “apply this lemma repeatedly”; we need induction — specifically, strong induction (that's why [4] mentions a `bound`).

Lemma statements
----------------

[1] Our proof of the lemma `deadlock_freedom'` begins by using calling `excluded_middle (exists a, a \in locksOf p)`.

[2] The no-locks lemma looks like this:

```
Theorem if_no_locks_held_then_progress : forall h p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> locksOf p = {}
      -> Forall (fun l_c => finished (snd l_c)) p
        \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
```

[3] We use the following sublemma in the no-locks case:

```
Lemma if_no_locks_held_then_progress' : forall h c l,
    goodCitizen {} c l
    -> finished c \/ exists h' l' c', step0 (h, {}, c) (h', l', c').
```

[4] The with-locks lemma looks like this:

```
Theorem if_lock_held_then_progress : forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
```

[5] Zooming in on a single command:

```
Lemma who_has_the_lock' : forall h a l l1 c,
      goodCitizen l1 c {}
      -> a \in l1
      -> l1 \subseteq l
      -> (exists h' l' c', step0 (h, l, c) (h', l', c'))
        \/ (exists a', a' < a /\ a' \in l).
```

To prove this sub-lemma, we relax the restriction on the owned-lock set from *after* running `c`, so now we must also consider the case where `c` is finished. (A good-citizen command that owns a lock before and owns no locks afterward can never be finished, since it must do its civic duty and release the lock.):

```
Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
```
