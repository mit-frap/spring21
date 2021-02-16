(** * 6.822 Formal Reasoning About Programs, Spring 2021 - Pset 1 *)

(* Welcome to the wonderful world of Coq programming! *)

(* This pset dives straight in to building a program-analysis pass and
 * proving it sound in Coq. But before that, you will need to get set up
 * with Coq. *)

(*
 * Start by installing the Coq system, either from your operating system's
 * repositories (`apt install coq`, `brew install coq`, etc.) or from the Coq
 * website at <https://coq.inria.fr/download>.  For this class, you can use any
 * version from 8.11 to 8.13 (the latest).
 *
 * Beware: versions of Ubuntu prior to 20.04 (and Debian stable) ship outdated
 * Coq releases.
 *
 * Run `coqc -v` to check that the right version was installed.
 *
 * It will also be *essential* to install a UI for editing Coq proofs!  The most
 * popular Coq IDE in the research world, which the course staff use and
 * recommend, is the venerable Proof General <https://proofgeneral.github.io/>,
 * a package for the Emacs IDE, which can optionally be extended with
 * company-coq <https://github.com/cpitclaudel/company-coq/>.
 *
 * If you're not ready to take the Emacs plunge (but it's worth it! We
 * promise!), then install one of the alternatives listed on the Coq website at
 * <https://coq.inria.fr/user-interfaces.html>.  The one called “CoqIDE” has a
 * the least steep learning curve, but Proof General will make you significantly
 * more productive after spending some practice time.
 *
 * We will have special office hours the first week of class,
 * to help everyone get these packages set up.
 *
 * Now, on to the actual assignment, once you have Coq and a UI installed!  This
 * course uses a special Coq library, so we'll start by compiling that:
 *
 * Run `make -C frap lib` in the root directory of your 6.822 git clone.
 *)

Require Import Frap.
(* If this import command doesn't work, something may be wrong with the copy
 * of the FRAP book source that has been included as a Git submodule.
 * Running `git submodule init' or `git submodule update' in the repository
 * base directory (followed by rerunning `make -C frap lib` here) might help.
 *)

(* The first part of this assignment involves the [bool] datatype,
 * which has the following definition.
 * <<
     Inductive bool :=
     | true
     | false.
   >>
 * We will define logical negation and conjunction of Boolean values,
 * and we will prove some properties of these definitions.

 * In the second part of this assignment, we will work with a simple language
 * of imperative arithmetic programs that sequentially apply operations
 * to a natural-number-valued state.

 * The file that you are currently reading contains only the *signature* of the
 * programs that we will implement: the module type `S` below defines the
 * interface of the code.

 * Your job is to write a module implementing this interface by fleshing out the
 * skeleton given in the file `Pset1Implementation.v`.  For the last problem, we
 * also ask you to give an informal explanation of the proof in addition to the
 * Coq proof script.
 *
 * Your `Pset1Implementation.v` file is what you upload to the course web site
 * to get credit for doing the assignment.  A line at the end of
 * `Pset1Implementation.v` (`Module Impl := …`) checks that your code conforms
 * to the expected signature.  Make sure that the file that you submit can be
 * compiled and checked: use `Admitted` if you're not sure how to complete a
 * proof.
 *
 * Percentages in square brackets below show the approximate rubric that we will
 * apply.
 *)

(*
 * First, here's the [Prog] datatype that defines abstract syntax trees for this
 * pset's language.
 *)

Inductive Prog :=
  | Done                             (* Don't modify the state. *)
  | AddThen (n : nat) (p : Prog)     (* Add [n] to the state, then run [p]. *)
  | MulThen (n : nat) (p : Prog)     (* Multiply the state by [n], then run [p]. *)
  | DivThen (n : nat) (p : Prog)     (* Divide the state by [n], then run [p]. *)
  | VidThen (n : nat) (p : Prog)     (* Divide [n] by the state, then run [p]. *)
  | SetToThen (n : nat) (p : Prog)   (* Set the state to [n], then run [p]. *)
  .

(* Then, here's the actual signature to implement. *)

Module Type S.

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  (*[2%]*) Parameter Neg : bool -> bool.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  (*[1%]*) Axiom Neg_true : Neg true = false.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  (*[4%]*) Axiom Neg_involutive : forall b : bool, Neg (Neg b) = b.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  (*[3%]*) Parameter And : bool -> bool -> bool.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  (*[1%]*) Axiom And_true_true : And true true = true.
  (*[1%]*) Axiom And_false_true : And false true = false.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  (*[4%]*) Axiom And_comm : forall x y : bool, And x y = And y x.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  (*[4%]*) Axiom And_true_r : forall x : bool, And x true = x.


  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   * Use the +, *, and / operators for natural numbers provided
   * by the Coq standard library, and for this part of the
   * exercise, don't worry about division by 0; doing the same
   * thing as division from the standard library does is fine.
   *)
  (*[3%]*) Parameter run : Prog -> nat -> nat.

  (*[1%]*) Axiom run_Example1 : run Done 0 = 0.
  (*[1%]*) Axiom run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  (*[1%]*) Axiom run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  (*[3%]*) Parameter numInstructions : Prog -> nat.

  (*[1%]*) Axiom numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  (*[3%]*) Parameter concatProg : Prog -> Prog -> Prog.

  (*[1%]*) Axiom concatProg_Example :
     concatProg (AddThen 1 Done) (MulThen 2 Done)
   = AddThen 1 (MulThen 2 Done).

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  (*[8%]*) Axiom concatProg_numInstructions : forall p1 p2,
      numInstructions (concatProg p1 p2)
      = numInstructions p1 + numInstructions p2.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  (*[8%]*) Axiom concatProg_run : forall p1 p2 initState,
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).

  (* As there is no intuitive or broadly useful definition for x/0,
     common processors handle it differently. We would like to model the
     portable behavior of a program, that is, its behavior to the extent
     it is known without relying on arbitrary choices about division by
     zero. The following interpreter returns (b, s), where the Boolean [b]
     indicates whether the execution completed without division by
     zero, and if it did, then [s] is the final state. First, you will be
     asked to prove that [s] matches [run] in those cases. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.

  (*[8%]*) Axiom runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.

  (* Static analysis to validate that a program never divides by 0 *)

  (* The final goal of this pset is to implement [validate : Prog -> bool] *)
  (*[5%]*) Parameter validate : Prog -> bool.
  (* such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     a division by zero, but it must recognize as good the examples given below.
     In jargon, [validate] is required to be sound but not complete, but
     "complete enough" for the use cases defined by the examples given here.
     We also ask you to define one additional negative test and prove that
     [validate] correctly flags it. *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).
  (*[0.5%]*) Axiom validate1 : validate goodProgram1 = true.
  (*[0.5%]*) Axiom validate2 : validate goodProgram2 = true.
  (*[0.5%]*) Axiom validate3 : validate goodProgram3 = true.
  (*[0.5%]*) Axiom validate4 : validate goodProgram4 = true.
  (*[0.5%]*) Axiom validate5 : validate goodProgram5 = true.
  (*[0.5%]*) Axiom validate6 : validate goodProgram6 = true.
  (*[0.5%]*) Axiom validate7 : validate goodProgram7 = true.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  (*[0.5%]*) Axiom validateb1 : validate badProgram1 = false.
  (*[0.5%]*) Axiom validateb2 : validate badProgram2 = false.

  (*[1.5%]*) Parameter badProgram3 : Prog.
  (*[1%]*) Axiom validateb3 : validate badProgram3 = false.

  (*[10%]*) (* Informal proof sketch for `validate_sound`. *)
  (* Before diving into the Coq proof, try to convince yourself that your code
   * is correct by applying induction by hand.  Can you describe the high-level
   * structure of the proof?  Which cases will you have to reason about?  What
   * do the induction hypotheses look like?  Which key lemmas do you need?
   * Write a short (~10-20 lines) informal proof sketch before proceeding. *)

  (*[20%]*) Axiom validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
End S.

(* Authors:
 * Peng Wang
 * Adam Chlipala
 * Joonwon Choi
 * Benjamin Sherman
 * Andres Erbsen
 * Clément Pit-Claudel
 *)
