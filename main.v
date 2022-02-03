Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.


Module TLC.

Inductive Ty: Type :=
  | T_Bool: Ty
  | T_Func: Ty -> Ty -> Ty.

Inductive Tm: Type :=
  | Tm_var: string -> Tm
  | Tm_abs: string -> Ty -> Tm -> Tm
  | Tm_app: Tm -> Tm -> Tm
  | Tm_true: Tm
  | Tm_false: Tm.

Declare Custom Entry tlc.
Notation "“ e ”" := e (e custom tlc at level 99).
Notation "( x )" := x (in custom tlc, x at level 99).
Notation "x" := x (in custom tlc at level 0, x constr at level 0).
Notation "S -> T" := (T_Func S T) (in custom tlc at level 50, right associativity).
Notation "x y" := (Tm_app x y) (in custom tlc at level 1, left associativity).
Notation "\ x : t => y" :=
  (Tm_abs x t y) (in custom tlc at level 90, x at level 99,
                     t custom tlc at level 99,
                     y custom tlc at level 99,
                     left associativity).
Coercion Tm_var : string >-> Tm.
Notation "'Bool'" := T_Bool (in custom tlc at level 0).
Notation "'true'" := true (at level 1).
Notation "'true'" := Tm_true (in custom tlc at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := Tm_false (in custom tlc at level 0).
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Inductive value: Tm -> Prop :=
  | value_abs: forall x T t,
    value “ \x: T => t ”
  | value_true: value Tm_true
  | value_false: value Tm_false.

Inductive closed: Tm -> Prop :=
  | Cl_abs: forall x T t,
    closed “ \x: T => t ”
  | Cl_app: forall t1 t2, 
    closed t1 /\ closed t2 ->
    closed “t1 t2”
  | Cl_true: closed Tm_true
  | Cl_false: closed Tm_false.

Reserved Notation "i '[' x ':=' s ']' =a u" (in custom tlc at level 20, x constr).

Inductive substitution (x: string) (s: Tm): Tm -> Tm -> Prop :=
  | Subst_var1: forall t,
      t = (Tm_var x) ->
      “t [x := s] =a t”

  | Subst_var2: forall t y,
      t = (Tm_var y) /\ ~(x = y) ->
      “t [x := s] =a t”

  | Subst_fun1: forall m T,
      “(\x:T => m) [x := s] =a (\x:T => m)”
  | Subst_fun2: forall y m m' T,
      “m [x := s] =a m'” ->
      “(\y:T => m) [x := s] =a (\x:T => m')”

  | Subst_app: forall m m' n n',
      “m [x := s] =a m'” /\
      “n [x := s] =a n'” ->
      “(m n) [x := s] =a (m' n')”
  | Subst_true:
      “true [x := s] =a true”
  | Subst_false:
      “false [x := s] =a false”
  where "i '[' x ':=' s ']' =a u" := (substitution x s i u) (in custom tlc).

Reserved Notation "t1 '-->' t1'" (at level 40).

Inductive step: Tm -> Tm -> Prop :=
  | E_App1: forall t1 t1' t2,
      t1 --> t1' ->
      “t1 t2” --> “t1' t2”
  | E_App2: forall t2 t2' v,
      value v ->
      t2 --> t2' ->
      “v t2” --> “v t2'”
  | E_AppAbs: forall x T t v t',
      value v ->
      “t [x:=v] =a t'” ->
      “(\x:T => t) v” --> t' 
  where "t1 '-->' t1'" := (step t1 t1').

Definition Context := list (string * Ty).

Notation "t ';' L" := (cons t L) (at level 40).
Reserved Notation "G '|-' t \in T" (at level 30).

Inductive has_type: Context -> Tm -> Ty -> Prop :=
  | T_Var: forall G x T,
      In (x, T) G ->
      (G |- x \in T)
  | T_Abs: forall G x T1 t2 T2,
      ((x, T1); G) |- t2 \in T2 ->
      G |- “\x:T1 => t2” \in (T_Func T1 T2)
  | T_App: forall G t1 t2 T11 T12,
      G |- t1 \in (T_Func T11 T12) /\
      G |- t2 \in T11 ->
      G |- “t1 t2” \in T12
  | T_True: forall G, G |- “true” \in “Bool”
  | T_False: forall G, G |- “false” \in “Bool”

  where "G '|-' t \in T" := (has_type G t T).

Notation "'|-' t \in T" := (has_type nil t T) (at level 30).

Example has_bool: |- “(\x:Bool => x) true” \in “Bool”.
Proof.
  apply T_App with “Bool”.
  split.
  - apply T_Abs.
    apply T_Var.
    unfold In.
    left.
    reflexivity.
  - apply T_True.
Qed.
