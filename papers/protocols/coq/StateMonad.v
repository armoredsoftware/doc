Require Import FunctionalExtensionality.

(** First attempt that simply copies the PVS implementation *)

Module definition1.

Definition A := nat.
Definition S := nat.

Inductive State :=
  | state : (S -> A * S) -> State.

Definition unit(x:A):State := state(fun (s:S) => (x,s)).

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
    type definition. *)

Module definition2.

Definition A := nat.
Definition S := nat.

Definition State := S -> A * S.

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

(* Not at all this notation is useful given that it appears to sequence only
   two operations and does not support sequence. *)

Notation "'do' a <- e ; c" :=
  (e >>= (fun a => c)) (at level 59, right associativity).

Example bind_ex1'' : (do a <- (unit 0) ; (fun (s:S) => (0,(s+1)))) 0 = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

End definition2.

(** Third attempt that parameterizes State over types. *)

Module definition3.

Definition State (S A:Type) := S -> A * S.

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

(* Definition get{S A:Type}. *)

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

(*
   This should be parameterized over both A and B allowing f:A->State S B,
   but something is fouling that up.  Will come back to it later.  Right now
   State and its functions are monoids and not monads.  Specifically, the
   associative operator is closed.
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

(* Again should be parameterized over B and C to allow types to change *)

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

(** Making the StateMonad a Monad using the Monad typeclass. *)

Class Monad (M: Type -> Type):Type := 
{
  unit: forall {A}, A -> M A
  ; bind: forall {A B}, M A -> (A -> (M B)) -> M B
  ; left_unit : forall {A B} (a:A) (f:A -> M B), bind (unit a) f = f a
  ; right_unit : forall {A} (ma:M A), bind ma unit = ma
  ; assoc : forall {A B C} (ma:M A) (f:A -> M B) (g:B -> M C),
              bind (bind ma f) g = bind ma (fun a => bind (f a) g)
}.

Definition State (S A:Type) := S -> A * S.

(* Something going haywire with types in this instance definition. Proofs
   pop out, but I can't get functions to evaluate properly. *)

(* Definition put{S A:Type}(a:A)(s1:S):(State S A) := (fun (s0:S) => (a,s1)). *)


Instance StateMonad (S:Type) : Monad (State S) :=
{
  unit A x := (fun s => (x,s))
  ; bind A B m f := (fun s0 =>
                       match (m s0) with
                         | (a,s1) => (f a) s1
                       end)
}.
Proof.
  intros. extensionality x. reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
  intros. extensionality x. destruct (ma x) as (a,s1). reflexivity.
Defined.

(* Proof used to ouse compute instead of simpl, but now works with simpl. *)

Example unit_ex1 : ((unit 0) 1) = (0,1).
Proof.
  unfold unit.
  simpl.
  reflexivity.
Qed.

Definition incState:(State nat nat) := (fun s => (0, (s+1))).

Eval compute in ((bind (unit 2) (fun a => incState)) 0).

Example bind_ex1: ((bind (unit 0) (fun a => incState)) 0) = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example bind_ex2 : ((bind
                       (bind
                          (unit 0) (fun a => incState))
                       (fun a => incState) 0)) = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

Definition addInput:(nat -> (State nat nat)) :=
  (fun a => (fun s => (a,(a+s)))).

Example bind_ex3 : ((bind
                       (bind
                          (unit 1) addInput)
                       addInput) 0) = (1,2).
Proof.
  unfold bind. reflexivity.
Qed.

End definition4.