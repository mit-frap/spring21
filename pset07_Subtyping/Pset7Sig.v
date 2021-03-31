(** * 6.822 Formal Reasoning About Programs, Spring 2021 - Pset 7 *)

Require Import Frap.Frap.

Module Type S.

  (* --- DEFINITIONS --- *)

  Inductive exp  :=
  | Var (x : var)
  | Abs (x : var) (e1 : exp)
  | App (e1 e2 : exp)
  | TupleNil
  | TupleCons (e1 e2 : exp)
  | Proj (e : exp) (n : nat)
  .

  Inductive value : exp -> Prop :=
  | VAbs : forall x e1, value (Abs x e1)
  | VTupleNil : value TupleNil
  | VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
  .

  Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
    match e2 with
    | Var y => if y ==v x then e1 else Var y
    | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
    | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
    | TupleNil => TupleNil
    | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
    | Proj e2' n => Proj (subst e1 x e2') n
    end.

  Inductive context :=
  | Hole
  | App1 (C : context) (e2 : exp)
  | App2 (v1 : exp) (C : context)
  | TupleCons1 (C : context) (e2 : exp)
  | TupleCons2 (v1 : exp) (C : context)
  | Proj1 (C : context) (n : nat)
  .

  Inductive plug : context -> exp -> exp -> Prop :=
  | PlugHole : forall e, plug Hole e e
  | PlugApp1 : forall e e' C e2,
      plug C e e'
      -> plug (App1 C e2) e (App e' e2)
  | PlugApp2 : forall e e' v1 C,
      value v1
      -> plug C e e'
      -> plug (App2 v1 C) e (App v1 e')
  | PlugTupleCons1 : forall C e e' e2,
      plug C e e'
      -> plug (TupleCons1 C e2) e (TupleCons e' e2)
  | PlugTupleCons2 : forall v1 C e e',
      value v1
      -> plug C e e'
      -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
  | PlugProj : forall C e e' n,
      plug C e e'
      -> plug (Proj1 C n) e (Proj e' n)
  .

  Inductive step0 : exp -> exp -> Prop :=
  | Beta : forall x e v,
      value v
      -> step0 (App (Abs x e) v) (subst v x e)
  | Proj0 : forall v1 v2,
      value v1
      -> value v2
      -> step0 (Proj (TupleCons v1 v2) 0) v1
  | ProjS : forall v1 v2 n,
      value v1
      -> value v2
      -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
  .

  Inductive step : exp -> exp -> Prop :=
  | StepRule : forall C e1 e2 e1' e2',
      plug C e1 e1'
      -> plug C e2 e2'
      -> step0 e1 e2
      -> step e1' e2'.

  Definition trsys_of (e : exp) :=
    {| Initial := {e}; Step := step |}.

  Inductive type :=
  | Fun (dom ran : type)
  | TupleTypeNil
  | TupleTypeCons (t1 t2 : type)
  .

  Inductive subtype : type -> type -> Prop :=
  | StFun : forall t1' t2' t1 t2,
      subtype t1 t1' ->
      subtype t2' t2 ->
      subtype (Fun t1' t2') (Fun t1 t2)
  | StTupleNilNil :
      subtype TupleTypeNil TupleTypeNil
  | StTupleNilCons : forall t1 t2,
      subtype (TupleTypeCons t1 t2) TupleTypeNil
  | StTupleCons : forall t1' t2' t1 t2,
      subtype t1' t1 ->
      subtype t2' t2 ->
      subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
  .

  Infix "$<:" := subtype (at level 70).

  Inductive proj_t : type -> nat -> type -> Prop :=
  | ProjT0 : forall t1 t2,
      proj_t (TupleTypeCons t1 t2) 0 t1
  | ProjTS : forall t1 t2 n t,
      proj_t t2 n t ->
      proj_t (TupleTypeCons t1 t2) (1 + n) t
  .

  Inductive hasty : fmap var type -> exp -> type -> Prop :=
  | HtVar : forall G x t,
      G $? x = Some t ->
      hasty G (Var x) t
  | HtAbs : forall G x e1 t1 t2,
      hasty (G $+ (x, t1)) e1 t2 ->
      hasty G (Abs x e1) (Fun t1 t2)
  | HtApp : forall G e1 e2 t1 t2,
      hasty G e1 (Fun t1 t2) ->
      hasty G e2 t1 ->
      hasty G (App e1 e2) t2
  | HtTupleNil : forall G,
      hasty G TupleNil TupleTypeNil
  | HtTupleCons: forall G e1 e2 t1 t2,
      hasty G e1 t1 ->
      hasty G e2 t2 ->
      hasty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
  | HtProj : forall G e n t t',
      hasty G e t' ->
      proj_t t' n t ->
      hasty G (Proj e n) t
  | HtSub : forall G e t t',
      hasty G e t' ->
      t' $<: t ->
      hasty G e t
  .

  (* --- THEOREMS TO PROVE (in Pset7.v) --- *)

  (*[5%]*)
  Axiom subtype_refl : forall t, t $<: t.

  (*[25%]*)
  Axiom subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.

  (*[70%]*)
  Axiom safety :
    forall e t,
      hasty $0 e t -> invariantFor (trsys_of e)
                                   (fun e' => value e'
                                              \/ exists e'', step e' e'').

End S.
