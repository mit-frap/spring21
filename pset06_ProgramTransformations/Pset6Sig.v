Require Export Frap.Frap.
From Coq Require Export NArith.
From Coq Require Export Program.Equality.

Arguments N.add : simpl nomatch.
Arguments N.sub : simpl nomatch.
Arguments N.mul : simpl nomatch.
Arguments N.div : simpl nomatch.
Arguments N.shiftl : simpl nomatch.
Arguments N.shiftr : simpl nomatch.

(*|
Totals below don't sum up to 100%!  This is because this pset is a
chose-your-own-adventure assignment, so you can pick what to do.  Here is the
complete rubric, which choice points indicated by `==`::

    1    Axiom opt_binop_fold_test1
    8    Axiom opt_binop_fold_sound
         = Arith (23 points)
           == Precompute
   17         Axiom opt_binop_precompute_sound
    3         Axiom opt_arith_precompute_test1
    3         Axiom opt_arith_precompute_test2
           == Log
   17         Axiom opt_binop_log2_sound
    3         Axiom opt_arith_log2_test1
    3         Axiom opt_arith_log2_test2
           == Bitwise
   17         Axiom opt_binop_bitwise_sound
    3         Axiom opt_arith_bitwise_test1
    3         Axiom opt_arith_bitwise_test2
    4    Axiom opt_arith_fold_test1
   10    Axiom opt_arith_sound
    3    Axiom opt_unskip_test1
    3    Axiom opt_unskip_test2
   16    Axiom opt_unskip_sound
         = Eval (32 points)
           == ConstProp
    8         Axiom opt_arith_constprop_sound
    3         Axiom opt_constprop_test1
    3         Axiom opt_constprop_test2
   18         Axiom opt_constprop_sound
           == Unroll
    6         Parameter eval_read_only
    3         Axiom opt_unroll_test1
    3         Axiom opt_unroll_test2
   20         Axiom opt_unroll_sound
         -- Total 100
|*)

Module Type S.
  Inductive BinopName : Set :=
    LogAnd : BinopName
  | Eq : BinopName
  | ShiftLeft : BinopName
  | ShiftRight : BinopName
  | Times : BinopName
  | Divide : BinopName
  | Plus : BinopName
  | Minus : BinopName
  | Modulo : BinopName.

  Inductive expr : Set :=
    Const : nat -> expr
  | Var : var -> expr
  | Binop : BinopName -> expr -> expr -> expr.

  Inductive cmd : Set :=
    Skip : cmd
  | Assign : var -> expr -> cmd
  | AssignCall : var -> var -> expr -> expr -> cmd
  | Sequence : cmd -> cmd -> cmd
  | If : expr -> cmd -> cmd -> cmd
  | While : expr -> cmd -> cmd.

  Declare Scope expr.
  Delimit Scope expr with expr.

  Coercion Const : nat >-> expr.
  Coercion Var : var >-> expr.

  Infix "&" := (Binop LogAnd) (at level 80) : expr.
  Infix "==" := (Binop Eq) (at level 70) : expr.
  Infix ">>" := (Binop ShiftRight) (at level 60) : expr.
  Infix "<<" := (Binop ShiftLeft) (at level 60) : expr.
  Infix "+" := (Binop Plus) (at level 50, left associativity) : expr.
  Infix "-" := (Binop Minus) (at level 50, left associativity) : expr.
  Infix "*" := (Binop Times) (at level 40, left associativity) : expr.
  Infix "/" := (Binop Divide) (at level 40, left associativity) : expr.
  Infix "mod" := (Binop Modulo) (at level 40) : expr.

  Notation "x <- e" :=
    (Assign x e%expr)
      (at level 75).
  Notation "x <- 'call1' f e1" :=
    (AssignCall x f e1%expr (Const 0))
      (at level 75, f at level 0, e1 at level 0).
  Notation "x <- 'call2' f e1 e2" :=
    (AssignCall x f e1%expr e2%expr)
      (at level 75, f at level 0, e1 at level 0, e2 at level 0).
  Infix ";;" :=
    Sequence (at level 76).
  Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
    (If e%expr then_ else_)
      (at level 75, e at level 0).
  Notation "'while' e 'loop' body 'done'" :=
    (While e%expr body)
      (at level 75).

  Example Times3Plus1Body :=
    ("n" <- "n" * 3 + 1).

  Example FactBody :=
    ("f" <- 1;;
     while "n" loop
       "f" <- "f" * "n";;
       "n" <- "n" - 1
     done).

  Example FactRecBody :=
    (when "n" == 1 then
       "f" <- 1
     else
       "f" <- call1 "fact_r" ("n" - 1);;
       "f" <- "f" * "n"
     done).

  Example FactTailRecBody :=
    (when "n" == 1 then
       "f" <- "acc"
     else
       "f" <- call2 "fact_tr" ("n" - 1) ("acc" * "n")
     done).

  Example CollatzBody :=
    (when ("start" == 1) then
       Skip
     else when ("start" mod 2 == 0) then
            "start" <- "start" / 2
          else
            (* `call1 f arg` is short for `call2 f arg 0` *)
            "start" <- call1 "times3plus1" ("start" + 0)
          done;;
          "flight" <- call2 "collatz" "start" ("flight" + 1)
     done).

  Notation TimesThreePlus1_signature := (("n", ""), "n", Times3Plus1Body).
  Notation Fact_signature := (("n", ""), "f", FactBody).
  Notation FactRec_signature := (("n", ""), "f", FactRecBody).
  Notation FactTailRec_signature := (("n", "acc"), "f", FactTailRecBody).
  Notation Collatz_signature := (("start", "flight"), "flight", CollatzBody).

  Notation Collatz_env :=
  ($0
    $+ ("collatz", Collatz_signature)
    $+ ("times3plus1", TimesThreePlus1_signature)).

  Notation Fact_env :=
    ($0
      $+ ("fact", Fact_signature)
      $+ ("fact_r", FactRec_signature)
      $+ ("fact_tr", FactTailRec_signature)).

  Parameter interp_binop : BinopName -> nat -> nat -> nat.

  Definition valuation := fmap var nat.
  Parameter interp_arith : expr -> valuation -> nat.

  Definition environment := fmap string ((var * var) * var * cmd).

  Inductive eval (phi: environment): valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval phi v Skip v
  | EvalAssign: forall v x e a,
      interp_arith e v = a ->
      eval phi v (Assign x e) (v $+ (x, a))
  | EvalAssignCall: forall x f e1 e2 x1 x2 y body a1 a2 a v v',
      phi $? f = Some ((x1, x2), y, body) ->
      interp_arith e1 v = a1 ->
      interp_arith e2 v = a2 ->
      eval phi ($0 $+ (x1, a1) $+ (x2, a2)) body v' ->
      v' $? y = Some a ->
      eval phi v (AssignCall x f e1 e2) (v $+ (x, a))
  | EvalSequence: forall v c1 v1 c2 v2,
      eval phi v c1 v1 ->
      eval phi v1 c2 v2 ->
      eval phi v (Sequence c1 c2) v2
  | EvalIfTrue: forall v e thn els v' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval phi v thn v' ->
      eval phi v (If e thn els) v'
  | EvalIfFalse: forall v e thn els v',
      interp_arith e v = 0 ->
      eval phi v els v' ->
      eval phi v (If e thn els) v'
  | EvalWhileTrue: forall v e body v' v'' c,
      interp_arith e v = c ->
      c <> 0 ->
      eval phi v body v' ->
      eval phi v' (While e body) v'' ->
      eval phi v (While e body) v''
  | EvalWhileFalse: forall v e body,
      interp_arith e v = 0 ->
      eval phi v (While e body) v.

  Definition eval_returns phi v cmd outVar result :=
    exists v', eval phi v cmd v' /\ v' $? outVar = Some result.

  Axiom TwoPlusTwoIsFour :
    eval_returns $0 $0 ("out" <- 2 + 2) "out" 4.
  Axiom EvalVars :
    eval_returns $0 $0 ("x" <- 1 + 1;; "x" <- "x" + "x" + "y") "x" 4.
  Axiom EvalSimpleArith :
    eval_returns $0 $0 ("out" <- (((14 >> 1) + 8 / 4 / 2) * (7 - 2) << 1) + 2 == 82) "out" 1.
  Axiom EvalTimes3Plus1 : forall n : nat,
      eval_returns $0 ($0 $+ ("n", n)) Times3Plus1Body "n" (3 * n + 1).
  Axiom EvalFact6 : exists v : valuation,
      eval $0 ($0 $+ ("n", 3)) FactBody v /\ v $? "f" = Some 6.
  Axiom EvalFactRec6 : exists v : valuation,
      eval Fact_env ($0 $+ ("n", 3)) FactRecBody v /\ v $? "f" = Some 6.
  Axiom EvalFactTailRec6 : exists v : valuation,
      eval Fact_env ($0 $+ ("n", 3) $+ ("acc", 1)) FactTailRecBody v /\
      v $? "f" = Some 6.
  Axiom collatz_result : exists v : valuation,
      eval Collatz_env ($0 $+ ("flight", 0) $+ ("start", 10)) CollatzBody v /\
      v $? "flight" = Some 6.

  Parameter opt_binop_fold : BinopName -> expr -> expr -> expr.
  (*[1%]*) Axiom opt_binop_fold_test1 : opt_binop_fold Plus "x" 0 = "x".

  (*[8%]*) Axiom opt_binop_fold_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_fold b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_precompute : BinopName -> expr -> expr -> expr.
  (*[Arith/Precompute:17%]*) Axiom opt_binop_precompute_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_precompute b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_log2 : BinopName -> expr -> expr -> expr.
  (*[Arith/Log:17%]*) Axiom opt_binop_log2_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_log2 b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_bitwise : BinopName -> expr -> expr -> expr.
  (*[Arith/Bitwise:17%]*) Axiom opt_binop_bitwise_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_bitwise b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_arith : expr -> expr.

  (*[4%]*) Axiom opt_arith_fold_test1 :
    opt_arith (1 + "z" * ("y" * ("x" * (0 + 0 / 1))))%expr =
    (1)%expr.
  (*[Arith/Precompute:3%]*) Axiom opt_arith_precompute_test1:
    opt_arith (("x" + (3 - 3)) / (0 + 1) + ("y" + "y" * 0))%expr =
    ("x" + "y")%expr.
  (*[Arith/Precompute:3%]*) Axiom opt_arith_precompute_test2 :
    opt_arith ((("y" / ("x" * 0 + 7 / 1)) mod (12 - 5)) / (2 * 3))%expr =
    (("y" / 7) mod 7 / 6)%expr.
  (*[Arith/Log:3%]*) Axiom opt_arith_log2_test1 :
    opt_arith (("y" * 8) mod 8 / 4)%expr =
    (("y" << 3 & 7) >> 2)%expr.
  (*[Arith/Log:3%]*) Axiom opt_arith_log2_test2 :
    opt_arith (("y" * 1 + (4 + 0)) mod 9 / 3)%expr =
    (("y" + 4) mod 9 / 3)%expr.
  (*[Arith/Bitwise:3%]*) Axiom opt_arith_bitwise_test1 :
    opt_arith ("y" * 13)%expr =
    ("y" + (("y" << 2) + ("y" << 3)))%expr.
  (*[Arith/Bitwise:3%]*) Axiom opt_arith_bitwise_test2 :
    opt_arith ("y" * (3 + 0))%expr =
    ("y" + ("y" << 1))%expr.

  (*[10%]*) Axiom opt_arith_sound :
    forall (e : expr) (v : valuation),
      interp_arith (opt_arith e) v = interp_arith e v.

  Parameter opt_unskip : cmd -> cmd.

  (*[3%]*) Axiom opt_unskip_test1 :
    opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) =
    Skip.
  (*[3%]*) Axiom opt_unskip_test2 :
    opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
                while 0 loop Skip;; Skip done;; Skip) =
    (when 0 then Skip else Skip done;; while 0 loop Skip done).

  (*[16%]*) Axiom opt_unskip_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_unskip c) v'.

  Parameter opt_arith_constprop : expr -> valuation -> expr.

  (*[Eval/ConstProp:8%]*) Axiom opt_arith_constprop_sound :
    forall (e : expr) (v consts : fmap var nat),
      consts $<= v ->
      interp_arith (opt_arith_constprop e consts) v = interp_arith e v.

  Parameter opt_constprop : cmd -> cmd.

  (*[Eval/ConstProp:3%]*) Axiom opt_constprop_test1 :
    opt_constprop FactBody = FactBody.
  (*[Eval/ConstProp:3%]*) Axiom opt_constprop_test2 :
    opt_constprop ("x" <- 7;; "y" <- "x";;
                   when "x" mod "w" then
                     "z" <- "x";; "t" <- "z";; while "t" loop "t" <- "t" - 1 done
                   else
                     "z" <- "u" + "x";; "t" <- "z"
                   done;;
                   "r" <- "z") =
   ("x" <- 7;; "y" <- 7;;
    when 7 mod "w" then
      "z" <- 7;; "t" <- 7;; while "t" loop "t" <- "t" - 1 done
    else
      "z" <- "u" + 7;; "t" <- "z"
    done;;
    "r" <- "z").

  (*[Eval/ConstProp:18%]*) Axiom opt_constprop_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_constprop c) v'.

  Parameter read_only : forall (c: cmd) (x0: var), bool.

  (*[Eval/Unroll:6%]*)
  Parameter eval_read_only: forall {phi v v' x c},
      eval phi v c v' ->
      read_only c x = true ->
      v' $? x = v $? x.

  Parameter opt_unroll : cmd -> cmd.

  (*[Eval/Unroll:3%]*) Axiom opt_unroll_test1 :
    opt_unroll CollatzBody = CollatzBody.
  (*[Eval/Unroll:3%]*) Axiom opt_unroll_test2 :
    opt_unroll FactBody <> FactBody.

  (*[Eval/Unroll:20%]*) Axiom opt_unroll_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_unroll c) v'.
End S.

Global Arguments Nat.modulo !_ !_ /.
Global Arguments Nat.div !_ !_.
Global Arguments Nat.log2 !_ /.
