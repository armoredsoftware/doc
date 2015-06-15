(*
Definition A := Type.
Definition S := Type.
*)

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

Module definition3.

(* Let's parameterize State over types *)

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

Example unit_ex1 : unit(0)(1) = (0,1).
Proof.
  unfold unit.
  reflexivity.
Qed.

Example bind_ex1: ((bind (unit 0) (fun a => (fun s => (a,(s+1))))) 0) = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example bind_ex2 : ((bind
                       (bind
                          (unit 0) (fun a => (fun s => (0,(s+1)))))
                       (fun a => (fun s => (0,(s+1))))) 0) = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.

End definition3.

Module definition4.

(* Let's make this puppy a monad using a typeclass *)

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

Instance StateMonad : Monad (State nat) :=
{
  unit A x := (fun s => (x,s))
  ; bind S A m f := (fun s0 =>
                       match (m s0) with
                         | (a,s1) => (f a) s1
                       end)
}.
Proof.
  intros. reflexivity.
Admitted.

Example unit_ex1 : unit(0)(1) = (0,1).
Proof.
  unfold unit.
  reflexivity.
Qed.

Example bind_ex1: ((bind (unit 0) (fun a => (fun s => (a,(s+1))))) 0) = (0,1).
Proof.
  unfold bind. reflexivity.
Qed.

Example bind_ex2 : ((bind
                       (bind
                          (unit 0) (fun a => (fun s => (0,(s+1)))))
                       (fun a => (fun s => (0,(s+1))))) 0) = (0,2).
Proof.
  unfold bind. reflexivity.
Qed.
