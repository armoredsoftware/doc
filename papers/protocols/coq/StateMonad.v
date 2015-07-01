(*
 TODO:
 + add put and get
 + add >>
 + convert to use >>= and >> notations
 - create StateMonad class by extending monad class
*)

Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Monad.

(** First attempt that simply copies the PVS implementation.  The datatype
 is not parameterized, but [A] and [S] are specified as a uninterpretted
 types. *)

Module definition1.

Definition A := nat.
Definition S := nat.

(** [State] is an algebraic type that encapsulates [state] as done in Haskell
  and PVS *)

Inductive State :=
  | state : (S -> A * S) -> State.

(** [unit :: A -> M A] has the classical definition of lifting a state into
  the monad and waiting for an input *)

Definition unit(x:A):State := state(fun (s:S) => (x,s)).


(** [bind :: M A -> (A -> M B) -> M B] has the classical definition of taking
  a monad, running it, and feeding the result into the next monadic expression
  in sequence. *)

Definition bind(m:State)(f:A -> State):State :=
  (state (fun (s0:S) =>
            match m with 
              | state m' => 
                match (m' s0) with
                  | (a,s1) => 
                    match (f a) with
                      | state m'' => (m'' s1)
                    end
                end
            end)).

Example unit_ex1 : (unit 3) = (unit 3).
Proof.
  reflexivity.
Qed.

End definition1.

(** Second attempt that removes the constructed type in favor of a simple
    type definition. Coq supports general functions over types.  Thus, we
    redefine [State] directly as the type [S -> A * S] *)

Module definition2.

(** Still use uninterpretted types for [A] and [S] *)
Definition A := nat.
Definition S := nat.

(** [State] is a type that defines the state monad in the classical fashion
  without using a constructed type *)

Definition State := S -> A * S.

(** Definitions of [unit] and [bind] follow directly from [State].  The
  [sequence] operation is added in this definition *)

Definition unit(x:A):State := (fun (s:S) => (x,s)).

Definition bind(m:State)(f:A -> State):State :=
  (fun (s0:S) =>
     match (m s0) with
           | (a,s1) => (f a) s1
     end).

Definition sequence(m:State)(n:State):State :=
  (fun (s0:S) =>
     match (m s0) with
           | (a,s1) => n s1
     end).

Example unit_ex1 : unit(0)(1) = (0,1).
Proof.
  unfold unit.
  reflexivity.
Qed.

Example bind_ex1 : ((bind (unit 0) (fun (a:A) => (fun (s:S) => (a,(s+1))))) 0) = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example bind_ex2 : ((bind
                       (bind
                          (unit 0) (fun (a:A) => (fun (s:S) => (0,(s+1)))))
                       (fun (a:A) => (fun (s:S) => (0,(s+1))))) 0) = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

(** Add the standard notations for [bind] and [sequence]. *)

Notation "m >>= f" :=
  (bind m f) (left associativity, at level 49).

Notation "m >> f" :=
  (sequence m f) (left associativity, at level 49).

Example bind_ex1' : ((unit 0) >>= (fun (a:A) => (fun (s:S) => (a,(s+1))))) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example bind_ex2' : (((unit 0) >>= (fun (a:A) => (fun (s:S) => (0,(s+1)))))
                               >>= (fun (a:A) => (fun (s:S) => (0,(s+1))))) 0
                    = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

(** Not at all this notation is useful given that it appears to sequence only
   two operations and does not support sequence. *)

Notation "'do' a <- e ; c" :=
  (e >>= (fun a => c)) (at level 59, right associativity).

Example bind_ex1'' : (do a <- (unit 0) ; (fun (s:S) => (0,(s+1)))) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

End definition2.

(** Third attempt that parameterizes [State] over types. Instead of using
 uninterpreted types for [S] and [A] the are now parameters to the [State]
 type. *)

Module definition3.

Definition State (S A:Type) := S -> A * S.

(** [unit] and [bind] change only in that [A] and [S] are now inferred types
  rather than explicitly defined. *)

Definition unit{S A:Type}(x:A):(State S A) := (fun (s:S) => (x,s)).

Definition bind{S A:Type}(m:(State S A))(f:A -> (State S A)):(State S A) :=
  (fun (s0:S) =>
     match (m s0) with
           | (a,s1) => (f a) s1
     end).

Definition sequence{S A:Type}(m:(State S A))(n:(State S A)):(State S A) :=
  (fun (s0:S) =>
     match (m s0) with
           | (a,s1) => n s1
     end).

(** [put] and [get] are defined for all state monads in addition to [unit]
 and [bind].  Still need to find the laws for these operations. *)

Definition put{S A:Type}(a:A)(s1:S):(State S A) := (fun (s0:S) => (a,s1)).

Eval compute in unit 0 1.

Example unit_ex1 : unit(0)(1) = (0,1).
Proof.
  unfold unit.
  reflexivity.
Qed.

Eval compute in ((bind (unit 0) (fun a => (fun s => (a,(s+1))))) 0).

Example bind_ex1: ((bind (unit 0) (fun a => (fun s => (a,(s+1))))) 0) = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Eval compute in ((bind
                   (bind
                      (unit 0) (fun a => (fun s => (0,(s+1)))))
                   (fun a => (fun s => (0,(s+1))))) 0).

Example bind_ex2 : ((bind
                       (bind
                          (unit 0) (fun a => (fun s => (0,(s+1)))))
                       (fun a => (fun s => (0,(s+1))))) 0) = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Eval compute in (put 0 1).

Eval compute in ((bind (unit 0) (fun a => (put 0 1))) 50).

Example bind_put  : ((bind (unit 0) (fun a => (put 0 1))) 50) = (0,1).
Proof.
  unfold bind, unit, put. reflexivity.
Qed.

Print bind_put.

(** Prove the three basic monad laws - left unit, right unit and associativity.
   None of these proofs is particularly challenging.

   Proofs should be parameterized over both [A] and [B] allowing 
   [f:A->State S B] to change the output type.
   Something is fouling that up.  Will come back to it later.  Right now
   [State] and its functions are a monoid and not a monad.  Specifically, the
   associative operator, [bind] is closed.
*)

Theorem left_unit :
  forall {S A} (a:A) (f:A -> (State S A)), bind (unit a) f = f a.
Proof.
  intros. unfold bind. reflexivity.
Qed.

Theorem right_unit : forall {S A} (ma:(State S A)), bind ma unit = ma.
Proof.
  intros. unfold bind. extensionality x.
  unfold unit.
  destruct (ma x) as (a,s1).
  reflexivity.
Qed.

Theorem assoc :
  forall {S A} (ma:(State S A)) (f:A -> (State S A)) (g:A -> (State S A)),
    bind (bind ma f) g = bind ma (fun a => bind (f a) g).
Proof.
  intros. unfold bind. extensionality x.
  destruct (ma x) as (a,s1).
  reflexivity.
Qed.

Eval compute in unit 0 1.

End definition3.

Module definition4.

(** Define the [StateMonad] as a typeclass rather than a single type.  This
 will enable defining things to be state monads rather than defining a single
 monad.*)

Definition State (S A:Type) := S -> A * S.

(** Define a [StateMonad] as an instance of [Monad]. Note that this includes
 only the definitions of [unit] and [bind].  [put] and [get] are defined later
 outside the typeclass.  This is not optimal, but we'll fix it later *)

Instance StateMonad (S:Type) : Monad (State S) :=
{
  unit A x := (fun s => (x,s))
  ; bind A B m f := (fun s0 =>
                       match (m s0) with
                         | (a,s1) => (f a) s1
                       end)
  ; sequence A B m1 m2 := (fun s0 =>
                             match (m1 s0) with
                               | (a,s1) => m2 s1
                             end)
}.
Proof.
  intros. extensionality x. reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
Defined.

Example unit_ex1 : ((unit 0) 1) = (0,1).
Proof.
  unfold unit.
  simpl.
  reflexivity.
Qed.

Definition incState:(State nat nat) := (fun s => (0, (s+1))).

Eval compute in ((unit 2) >>= (fun a => incState)) 0.

Eval compute in ((unit 2) >> incState) 0.

Example bind_ex1: ((unit 0) >>= (fun a => incState)) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex1: ((unit 0) >> incState) 0 = (0,1).
Proof.
  unfold sequence. reflexivity.
Qed.

Example bind_ex2 :
  ((unit 0) >>= (fun a => incState) >>= (fun a => incState)) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex2 : ((unit 0) >> incState >> incState) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Definition addInput:(nat -> (State nat nat)) :=
  (fun a => (fun s => (a,(a+s)))).

Example bind_ex3 :
  ((unit 1) >>= addInput >>= addInput) 0 = (1,2).
Proof.
  unfold bind. reflexivity.
Qed.

Definition put{S A:Type}(s:S)(a:A):(State S A) := (fun (_:S) => (a,s)).

Example put_ex1 : ((unit 1) >>= (put 10)) 0 = (1,10).
Proof.
  unfold bind. simpl. unfold put. reflexivity.
Qed.

Definition get{S:Type}(a:S):(State S S) := (fun (s:S) => (s,s)).

Example get_ex1 : ((unit 0) >>= get) 10 = (10,10).
Proof.
  unfold bind. simpl. unfold get. reflexivity.
Qed.

End definition4.

Module abelianmonoid.

(** Example using subclasses from web discussion.  Start with a Semigroup
and buid up an Abelian Monoid *)

(** A semigroup is a set ([A]) with an associative operator ([op]) *)

Class Semigroup {A : Type} (op : A -> A -> A) : Type := {
  op_associative : forall x y z : A, op x (op y z) = op (op x y) z
}.

(** Monoid is a semigroup with left and right IDs *)
Class Monoid `(M : Semigroup) (id : A) : Type := {
  id_ident_left  : forall x : A, op id x = x;
  id_ident_right : forall x : A, op x id = x
}.

(** Abelian monoid is a monoid whose operator is commutative *)
Class AbelianMonoid `(M : Monoid) : Type := {
  op_commutative : forall x y : A, op x y = op y x
}.

Instance ExSemigroup : (Semigroup mult) := {
}.
Proof.
  intros. apply mult_assoc.
Qed.

Instance ExMonoid : (Monoid ExSemigroup 1) := {
}.
Proof.
  intros. apply mult_1_l.
  intros. apply mult_1_r.
Qed.

Instance ExAbMonoid : (AbelianMonoid ExMonoid) :=
{
}.
Proof.
  intros. apply mult_comm.
Qed.

End abelianmonoid.

Module definition5.

(** Try the same approach extending the [Monad] typeclass to implement a
  [StateMonad] typeclass.  [M] is the monad constructor. *)

Definition State (S A:Type) := S -> A * S.

Class StateMonad {S A:Type} (State: Type -> Type -> Type) `(Monad (State S)) :Type :=
{
  get: A -> State S S
  ; put: S -> A -> State S A
}.

Print StateMonad.

Instance StateMonadI {S:Type} : Monad (State S) :=
{
  unit A x := (fun s => (x,s))
  ; bind A B m f := (fun s0 =>
                       match (m s0) with
                         | (a,s1) => (f a) s1
                       end)
  ; sequence A B m1 m2 := (fun s0 =>
                             match (m1 s0) with
                               | (a,s1) => m2 s1
                             end)
}.
Proof.
  intros. extensionality x. reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
Defined.

Print StateMonadI.

Instance StateMonadEx {S A:Type} (a:A) : StateMonad State StateMonadI :=
{
  put := (fun (s:S) => (fun (a:A) => (fun (_:S) => (a,s))))
  ; get := (fun (a:A) => (fun (s:S) => (s,s)))
}.

Print StateMonadEx.

Example unit_ex1 : ((unit 0) 1) = (0,1).
Proof.
  unfold unit.
  simpl.
  reflexivity.
Qed.

Definition incState:(State nat nat) := (fun s => (0, (s+1))).

Eval compute in ((unit 2) >>= (fun a => incState)) 0.

Eval compute in ((unit 2) >> incState) 0.

Example bind_ex1: ((unit 0) >>= (fun a => incState)) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex1: ((unit 0) >> incState) 0 = (0,1).
Proof.
  unfold sequence. reflexivity.
Qed.

Example bind_ex2 :
  ((unit 0) >>= (fun a => incState) >>= (fun a => incState)) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex2 : ((unit 0) >> incState >> incState) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Definition addInput:(nat -> (State nat nat)) :=
  (fun a => (fun s => (a,(a+s)))).

Example bind_ex3 :
  ((unit 1) >>= addInput >>= addInput) 0 = (1,2).
Proof.
  unfold bind. reflexivity.
Qed.

(* Definition put{S A:Type}(s:S)(a:A):(State S A) := (fun (_:S) => (a,s)). *)

Eval compute in (put 0 10).

Eval compute in (fun (a:nat) => (fun (s:nat) => (0,10)):(State nat nat)).

Eval compute in (((unit 1):(State nat nat)) >>= ((fun (a:nat) => (put 0 10):(State nat nat)))) 10.

Example put_ex2: (((unit 1):(State nat nat)) >>= ((fun (a:nat) => (fun (s:nat) => (0,10)):(State nat nat)))) 10 = (0,10).
Proof.
  unfold unit, bind.
  trivial.
Qed.

Eval compute in ((((unit 1) >>= (put 10)):(State nat nat)) 8).

(* Example put_ex1 : ((((unit 1) >>= (put 10)):(State nat nat)) 8) = (1,10).
Proof.
  unfold bind. simpl. unfold put. reflexivity.
Qed.
*)

(* Definition get{S:Type}(a:S):(State S S) := (fun (s:S) => (s,s)). *)


Eval compute in ((unit 0) >>= get).

Check ((unit 0) >>= get).

Eval compute in ((unit 0) >>= get) 10.

Example get_ex1 : ((unit 0) >>= get) 10 = (10,10).
Proof.
  unfold bind. simpl. unfold get. reflexivity.
Qed.

End definition5.
