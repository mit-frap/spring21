(*|
=============================================================
 6.822 Formal Reasoning About Programs, Spring 2021 - Pset 9
=============================================================
|*)

Require Export Frap.

Module Type S.
  Inductive nat_op :=
  | Plus
  | Minus
  | Times.

  Inductive exp :=
  | Const (n : nat)
  | Var (x : string)
  | Read (e1 : exp)
  | NatOp (b: nat_op) (e1 e2 : exp).

  Inductive bool_op :=
  | Equal
  | Less.

  Inductive bexp :=
  | BoolOp (b: bool_op) (e1 e2 : exp).

  Definition heap := fmap nat nat.
  Definition valuation := fmap var nat.

  Inductive io := In (v : nat) | Out (v : nat).
  Definition trace := list io.

  Definition assertion := trace -> heap -> valuation -> Prop.

  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : exp)
  | Write (e1 e2 : exp)
  | Seq (c1 c2 : cmd)
  | If_ (be : bexp) (then_ else_ : cmd)
  | While_ (inv : assertion) (be : bexp) (body : cmd)
  | Input (x : var)
  | Output (e : exp).

  (* BEGIN NOTATION MAGIC *)
  Coercion Const : nat >-> exp.
  Coercion Var : string >-> exp.
  Declare Scope cmd_scope.
  Notation "*[ e ]" := (Read e) : cmd_scope.
  Notation "a + b" := (NatOp Plus a b) : cmd_scope.
  Notation "a - b" := (NatOp Minus a b) : cmd_scope.
  Notation "a * b" := (NatOp Times a b) : cmd_scope.
  Notation "a = b" := (BoolOp Equal a b) : cmd_scope.
  Notation "a < b" := (BoolOp Less a b) : cmd_scope.
  Definition set (dst src : exp) : cmd :=
    match dst with
    | Read dst' => Write dst' src
    | Var dst' => Assign dst' src
    | _ => Assign "Bad LHS" 0
    end.
  Infix "<-" := set (no associativity, at level 70) : cmd_scope.
  Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
  Notation "'when' b 'then' then_ 'else' else_ 'done'" :=
    (If_ b then_ else_) (at level 75, b at level 0) : cmd_scope.
  Notation "'when' b 'then' then_ 'done'" :=
    (If_ b then_ Skip) (at level 75, b at level 0) : cmd_scope.
  Notation "{{ I }}  'while' b 'loop' body 'done'" := (While_ I%nat%type b body) (at level 75) : cmd_scope.
  Notation "x '<--' 'input'" := (Input x) (at level 75) : cmd_scope.
  Notation "'output' e" := (Output e) (at level 75) : cmd_scope.
  Delimit Scope cmd_scope with cmd.
  (* END NOTATION MAGIC *)

  Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

  Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
    match e with
    | Const n => n
    | Var x => v $! x
    | Read e1 => h $! eval e1 h v
    | NatOp b e1 e2 =>
      let e1 := eval e1 h v in
      let e2 := eval e2 h v in
      match b with
      | Plus => e1 + e2
      | Minus => e1 - e2
      | Times => e1 * e2
      end
    end.

  Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
    match b with
    | BoolOp b e1 e2 =>
      let e1 := eval e1 h v in
      let e2 := eval e2 h v in
      match b with
      | Equal => if eval e1 h v ==n eval e2 h v then true else false
      | Less => if eval e2 h v <=? eval e1 h v then false else true
      end
    end.

  Inductive exec : trace -> heap -> valuation -> cmd ->
                   trace -> heap -> valuation -> Prop :=
  | ExSkip : forall tr h v,
      exec tr h v Skip tr h v
  | ExAssign : forall tr h v x e,
      exec tr h v (Assign x e) tr h (v $+ (x, eval e h v))
  | ExWrite : forall tr h v e1 e2,
      exec tr h v (Write e1 e2) tr (h $+ (eval e1 h v, eval e2 h v)) v
  | ExSeq : forall tr1 h1 v1 c1 tr2 h2 v2 c2 tr3 h3 v3,
      exec tr1 h1 v1 c1 tr2 h2 v2 ->
      exec tr2 h2 v2 c2 tr3 h3 v3 ->
      exec tr1 h1 v1 (Seq c1 c2) tr3 h3 v3
  | ExIfTrue : forall tr1 h1 v1 b c1 c2 tr2 h2 v2,
      beval b h1 v1 = true ->
      exec tr1 h1 v1 c1 tr2 h2 v2 ->
      exec tr1 h1 v1 (If_ b c1 c2) tr2 h2 v2
  | ExIfFalse : forall tr1 h1 v1 b c1 c2 tr2 h2 v2,
      beval b h1 v1 = false ->
      exec tr1 h1 v1 c2 tr2 h2 v2 ->
      exec tr1 h1 v1 (If_ b c1 c2) tr2 h2 v2
  | ExWhileFalse : forall I tr h v b c,
      beval b h v = false ->
      exec tr h v (While_ I b c) tr h v
  | ExWhileTrue : forall I tr1 h1 v1 b c tr2 h2 v2 tr3 h3 v3,
      beval b h1 v1 = true ->
      exec tr1 h1 v1 c tr2 h2 v2 ->
      exec tr2 h2 v2 (While_ I b c) tr3 h3 v3 ->
      exec tr1 h1 v1 (While_ I b c) tr3 h3 v3
  | ExInput : forall tr h v x inp,
      exec tr h v (Input x) (In inp :: tr) h (v $+ (x, inp))
  | ExOutput : forall tr h v e,
      exec tr h v (Output e) (Out (eval e h v) :: tr) h v.

  Reserved Notation "<{ P }> c <{ Q }>"
           (at level 90, c at next level,
            format "'[hv' <{  P  }> '/'  c  '/' <{  Q  }> ']'").

  Notation "'fun/inv' tr h v => e" :=
    (fun (tr : trace) (h : heap) (v : valuation) => e%nat%type)
      (at level 90, tr ident, h ident, v ident).

  Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
  | HtSkip : forall P, <{ P }> Skip <{ P }>
  | HtAssign : forall P x e,
      <{ P }>
      Assign x e
      <{ fun/inv tr h v => exists v', P tr h v' /\ v = v' $+ (x, eval e h v') }>
  | HtWrite : forall P (e1 e2 : exp),
      <{ P }>
      Write e1 e2
      <{ fun/inv tr h v =>
           exists h', P tr h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v) }>
  | HtSeq : forall (P Q R : assertion) c1 c2,
      <{ P }> c1 <{ Q }> -> <{ Q }> c2 <{ R }> -> <{ P }> c1;; c2 <{ R }>
  | HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
      <{ fun/inv tr h v => P tr h v /\ beval b h v = true }> c1 <{ Q1 }> ->
      <{ fun/inv tr h v => P tr h v /\ beval b h v = false }> c2 <{ Q2 }> ->
      <{ P }> (when b then c1 else c2 done) <{ fun/inv tr h v => Q1 tr h v \/ Q2 tr h v }>
  | HtWhile : forall (I P : assertion) b c,
      (forall tr h v, P tr h v -> I tr h v) ->
      <{ fun/inv tr h v => I tr h v /\ beval b h v = true }> c <{ I }> ->
      <{ P }>
      {{ I }} while b loop c done
      <{ fun/inv tr h v => I tr h v /\ beval b h v = false }>
  | HtInput : forall (P : assertion) x,
      <{ P }>
      x <-- input
      <{ fun/inv tr h v =>
           exists tr' v' inp, P tr' h v' /\ tr = In inp :: tr' /\ v = v' $+ (x, inp) }>
  | HtOutput : forall (P : assertion) e,
      <{ P }>
      output e
      <{ fun/inv tr h v => exists tr', P tr' h v /\ tr = Out (eval e h v) :: tr' }>
  | HtConsequence : forall (P Q P' Q' : assertion) c,
      <{ P }> c <{ Q }> ->
      (forall tr h v, P' tr h v -> P tr h v) ->
      (forall tr h v, Q tr h v -> Q' tr h v) ->
      <{ P' }> c <{ Q' }>
  where "<{ P }> c <{ Q }>" := (hoare_triple P c%cmd Q).

  Example max3 :=
    ("x" <-- input;;
     "y" <-- input;;
     "z" <-- input;;
     when "x" < "y" then
       when "y" < "z" then
         output "z"
       else
         output "y"
       done
     else
       when "x" < "z" then
         output "z"
       else
         output "x"
       done
     done)%cmd.

  Definition max3_spec (tr: trace): Prop :=
    exists x y z,
      tr = [Out (max x (max y z)); In z; In y; In x].

  (*[10%]*) Axiom max3_ok:
    <{ fun/inv tr _ _ => tr = [] }>
    max3
    <{ fun/inv tr' _ _ => max3_spec tr' }>.

  Example fibonacci n inv :=
    ("cnt" <- 0;;
     "x" <- 0;;
     output "x";;
     "y" <- 1;;
     output "y";;
     {{ inv }}
     while "cnt" < n loop
       "tmp" <- "y";;
       "y" <- "x" + "y";;
       "x" <- "tmp";;
       "cnt" <- "cnt" + 1;;
       output "y"
     done)%cmd.

  Inductive fibonacci_spec : trace -> Prop :=
  | FibInit: fibonacci_spec [Out 1; Out 0]
  | FibRec: forall x y tr,
      fibonacci_spec (Out y :: Out x :: tr) ->
      fibonacci_spec (Out (x + y) :: Out y :: Out x :: tr).

  Parameter fibonacci_invariant : forall (n: nat), assertion.

  (*[20%]*) Axiom fibonacci_ok : forall (n: nat),
    <{ fun/inv tr _ _ => tr = [] }>
    fibonacci n (fibonacci_invariant n)
    <{ fun/inv tr' _ _ => fibonacci_spec tr' }>.

  Example fact inv :=
    ("cnt" <- 0;;
     "x" <- 1;;
     output "x";;
     {{ inv }}
     while "cnt" < "n" loop
       "x" <- "x" * "cnt";;
       "cnt" <- "cnt" + 1;;
       output "x"
     done)%cmd.

  Inductive fact_spec : nat -> trace -> Prop :=
  | FactInit: fact_spec 0 [Out 1]
  | FactRec: forall x n tr,
      fact_spec n (Out x :: tr) ->
      fact_spec (n + 1) (Out (x * n) :: Out x :: tr).

  Parameter fact_invariant : forall (n: nat), assertion.

  (*[20%]*) Axiom fact_ok : forall (n: nat),
    <{ fun/inv tr _ v => tr = [] /\ v $! "n" = n }>
    fact (fact_invariant n)
    <{ fun/inv tr' _ _ => fact_spec n tr' }>.

  Example mailbox inv :=
    ("done" <- 0;;
     {{ inv }}
     while "done" = 0 loop
       "address" <-- input;;
       when "address" = 0 then
         "done" <- 1
       else
         "val" <-- input;;
         output *["address"];;
         *["address"] <- "val"
       done
     done)%cmd.

  Inductive mailbox_spec : forall (h: heap) (tr: trace), Prop :=
  | MBNil: mailbox_spec $0 []
  | MBPut: forall h address val ret tr,
      address <> 0 ->
      ret = h $! address ->
      mailbox_spec h tr ->
      mailbox_spec (h $+ (address, val)) (Out ret :: In val :: In address :: tr).

  Inductive mailbox_done (h: heap) : trace -> Prop :=
  | MBDone: forall tr,
      mailbox_spec h tr ->
      mailbox_done h (In 0 :: tr).

  Parameter mailbox_invariant : assertion.

  (*[20%]*) Axiom mailbox_ok:
    <{ fun/inv tr h _ => tr = [] /\ h = $0 }>
    mailbox mailbox_invariant
    <{ fun/inv tr' h' _ => mailbox_done h' tr' }>.

  Example search inv :=
    ("needle" <-- input;;
     {{ inv }}
     while 0 < "length" loop
       "length" <- "length" - 1;;
       when *["ptr" + "length"] = "needle" then
         output "length" done
     done)%cmd.

  Inductive search_spec (needle: nat) : forall (offset: nat) (haystack: list nat), trace -> Prop :=
  | SearchNil: forall offset,
      search_spec needle offset [] [In needle]
  | SearchConsYes: forall n offset haystack tr,
      0 < offset ->
      n = needle ->
      search_spec needle offset haystack tr ->
      search_spec needle (offset - 1) (n :: haystack) (Out (offset - 1) :: tr)
  | SearchConsNo: forall n offset haystack tr,
      0 < offset ->
      n <> needle ->
      search_spec needle offset haystack tr ->
      search_spec needle (offset - 1) (n :: haystack) tr.

  Inductive search_done haystack tr : Prop :=
  | SearchDone: forall needle offset,
      offset = 0 ->
      search_spec needle offset haystack tr ->
      search_done haystack tr.

  Inductive array_at (h: heap) : nat -> list nat -> Prop :=
  | ArrayEmpty : forall ptr, array_at h ptr []
  | ArrayCons : forall ptr hd tl,
      h $! ptr = hd ->
      array_at h (S ptr) tl ->
      array_at h ptr (hd :: tl).

  Parameter search_invariant : forall (ptr: nat) (data: list nat), assertion.

  (*[30%]*) Axiom search_ok : forall ptr data,
    <{ fun/inv tr h v =>
         tr = [] /\
         v $! "ptr" = ptr /\
         v $! "length" = Datatypes.length data /\
         array_at h ptr data }>
    search (search_invariant ptr data)
    <{ fun/inv tr' h' _ =>
         array_at h' ptr data /\
         search_done data tr' }>.
End S.
