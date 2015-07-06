(**
 [StateMonad] type class definition

 Provides a simple type class for defining structures to be of the form
 of a state monad.

 TODO:
 - add state monad laws for put and get
*)

Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Monad.

(** Extend the [Monad] typeclass to implement a [StateMonad] typeclass.  Note
  that [StateMonad S] is the monad, not just [StateMonad].  This will be
  important when we instantiate the [Monad] typeclass.  *)

(** [State] is the classic definition of the state monad type.  Note that
  although its name is [State] its really a next state function.  Keeping
  the tradition name here. *)
Definition State (S A:Type) := S -> A * S.

(** Extend the [Monad] class with [put] and [get].  Still need to add the
  state monad laws for [put] and [get]. *)
Class StateMonad {S A:Type} (State: Type -> Type -> Type) `(Monad (State S)) :Type :=
{
  get: A -> State S S
  ; put: S -> A -> State S A
}.

(** Create an instance of [Monad] from [(State S)] and prove the monad laws.
  [StateMonadI] is of type [Monad (State S)] and can now be used to
  instantiate the third parameter if [StateMonad] that requires [(State S)]
  to be an instance of [Monad] *)
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
  intros. extensionality x. reflexivity.
Defined.

(** Create an instance of [StateMonad] using [State] as the type constructor
  and [StateMonadI] as a witness to something being of type [(Monad (State S))]   called [StateMonadX].  Note that PVS would have done some of the type-foo
  automatically. *)
Instance StateMonadEx {S A:Type} : StateMonad State StateMonadI :=
{
  put := (fun (s:S) => (fun (a:A) => (fun (_:S) => (a,s))))
  ; get := (fun (a:A) => (fun (s:S) => (s,s)))
}.

Example unit_ex1 : ((unit 0) 1) = (0,1).
Proof.
  unfold unit.
  simpl.
  reflexivity.
Qed.

(** [incState] is a simple [f] that increments a state value consisting of 
  a natural numnber. *)

Definition incState:nat->(State nat nat) := (fun _ => (fun s => (0, (s+1)))).

(** [incStateCurry] is a [State] resuting from currying [f]. *)

Definition incStateCurry:(State nat nat) := (incState 0).

Example bind_ex1: ((unit 0) >>= incState) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex1: ((unit 0) >> incStateCurry) 0 = (0,1).
Proof.
  unfold sequence. reflexivity.
Qed.

(** [sequence] is a specialization of [bind]. *)

Lemma bind_seq_eq : forall (A S:Type) (f g:(State S A)),
                      (f >> g) = (f >>= (fun a => g)).
Proof.
  intros. unfold unit, incState. simpl. extensionality x. reflexivity.
Qed.

Example bind_ex2 :
  ((unit 0) >>= incState >>= incState) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Example sequence_ex2 : ((unit 0) >> incStateCurry >> incStateCurry) 0 = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

(** [addInput] is a simple [f] that adds the result of a previous execution
  to the current state *)

Definition addInput:(nat -> (State nat nat)) :=
  (fun a => (fun s => (a,(a+s)))).

Example bind_ex3 :
  ((unit 1) >>= addInput >>= addInput) 0 = (1,2).
Proof.
  unfold bind. reflexivity.
Qed.

Example put_ex2: (((unit 1):(State nat nat)) >>= ((fun (a:nat) => (fun (s:nat) => (0,10)):(State nat nat)))) 10 = (0,10).
Proof.
  unfold unit, bind.
  trivial.
Qed.

Example put_ex1 : ((((unit 1) >>= (put 10)):(State nat nat)) 8) = (1,10).
Proof.
  unfold bind. simpl. unfold put. reflexivity.
Qed.

Example get_ex1 : ((unit 0) >>= get) 10 = (10,10).
Proof.
  unfold bind. simpl. unfold get. reflexivity.
Qed.

