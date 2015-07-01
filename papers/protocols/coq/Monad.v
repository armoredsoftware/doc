(* Define a Monad class that can be instantiated *)

(** Start with typeclass for [Monad] parameterized over the type
 [M:Type -> Type].  Note that [M] is a single parameter function.
 Definition is taken original from the web at *find the link* *)
 
Class Monad (M: Type -> Type):Type := 
{
  unit: forall {A}, A -> M A
  ; bind: forall {A B}, M A -> (A -> (M B)) -> M B
  ; sequence: forall {A B}, M A -> M B -> M B
  ; left_unit : forall {A B} (a:A) (f:A -> M B), bind (unit a) f = f a
  ; right_unit : forall {A} (ma:M A), bind ma unit = ma
  ; assoc : forall {A B C} (ma:M A) (f:A -> M B) (g:B -> M C),
              bind (bind ma f) g = bind ma (fun a => bind (f a) g)
}.

Notation "m >>= f" :=
  (bind m f) (left associativity, at level 49).

Notation "m >> f" :=
  (sequence m f) (left associativity, at level 49).

