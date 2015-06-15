Require Export SfLib.

(* Define a Monad class that can be instantiated *)

Class Monad (M: Type -> Type):Type := 
{
  unit: forall {A}, A -> M A
  ; bind: forall {A B}, M A -> (A -> (M B)) -> M B
  ; left_unit : forall {A B} (a:A) (f:A -> M B), bind (unit a) f = f a
  ; right_unit : forall {A} (ma:M A), bind ma unit = ma
  ; assoc : forall {A B C} (ma:M A) (f:A -> M B) (g:B -> M C),
              bind (bind ma f) g = bind ma (fun a => bind (f a) g)
}.

Print option.

(* Declaring built-in option to be a monad *)

Instance Maybe : Monad option :=
{
  unit A a := Some a
  ; bind A B ma f :=
      match ma with 
        | None => None
        | Some a => f a
      end
}.
Proof.
  intros. reflexivity.
  intros. destruct ma; reflexivity.
  intros. destruct ma; reflexivity.
Defined.

(* Creating an error monad that can be instantiated as a monad *)

Inductive error (A : Type) : Type :=
| V : A -> error A
| E : nat -> error A.

Print error.

Instance Error : Monad error :=
{
  unit A a := V A a
  ; bind A B ma f :=
      match ma with
        | V a => f a
        | E n => E B n
      end
}.
Proof.
  intros. reflexivity.
  intros. destruct ma. reflexivity. reflexivity.
  intros. destruct ma. reflexivity. reflexivity.
Qed.

Inductive state (S A : Type) : Type :=
  runState : S -> A * S -> state S A.

Definition S := nat.

Instance State : Monad (state S) :=
{
  unit A a := runState (fun s => (a,s))
  ; bind s f := state(fun (s0:S) =>
                        match runState(s)(s0) with
                            | (a,s1) => runState(f a)(s1)
                        end)
}.

(*
 State : DATATYPE
 BEGIN
   state(runState:[S->[A,S]]):state?
 END State
*)

Class State (M:Type -> Type): Type := 
{
  unitS: forall {A}, A -> M A
  ; bindS: forall {A B}, M A -> (A -> (M B)) -> M B
  ; seqS: forall {A B}, M A -> M B -> M B
  ; getS: forall {A}, M A 
  ; putS: forall {A}, A -> M A
  ; left_unitS : forall {A B} (a:A) (f:A -> M B), bindS (unitS a) f = f a
  ; right_unitS : forall {A} (ma:M A), bindS ma unitS = ma
  ; assocS : forall {A B C} (ma:M A) (f:A -> M B) (g:B -> M C),
               bindS (bindS ma f) g = bindS ma (fun a => bindS (f a) g)
  ; state1 : forall {A} (s s':A), seqS (putS s) (putS s') = putS s'
  ; state2 : forall {A} (s:A), seqS (putS s) (getS) = seqS (putS s) (unitS s)
  ; state3 : forall {A:Type}, bindS getS putS = unitS A
  (* ; state4 : forall {A} (s:A), bindS getS (fun x => (bindS getS k x)) = bind get (fun x => k x x) *)
}.

(* put s >> put s'            = put s'
   put s >> get               = put s >> return s
   get  >>= put               = return ()
   get  >>= λs → get >>= k s = get >>= λs → k s s *)

Print State.

Notation "m >>= f" :=
  (bind m f) (left associativity, at level 49).

Notation "m >> f" :=
  (bind m f) (left associativity, at level 49).

Notation "'do' a <- e ; c" :=
  (e >>= (fun a => c)) (at level 59, right associativity).

Eval compute in (Some 1 >>= (fun x => unit (x + 1))).
Eval compute in (None >>= (fun x => unit (x + 1))).

Print option.

Inductive state {A B:Type} : Type :=
{
  runState : A -> (A * B)
}.

Instance S {A B:Type} : State A B :=
{
}.