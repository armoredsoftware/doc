Require Export SfLib.

(* Define a Monad class that can be instantiated *)

Class Monad (M: Type -> Type) := 
{
  unit : forall {A}, A -> M A
  ; bind : forall {A B}, M A -> (A -> (M B)) -> M B
  ; left_unit : forall {A B} (a:A) (f:A -> M B), bind (unit a) f = f a
  ; right_unit : forall {A} (ma:M A), bind ma unit = ma
  ; assoc : forall {A B C} (ma:M A) (f:A -> M B) (g:B -> M C),
              bind (bind ma f) g = bind ma (fun a => bind (f a) g)
}.

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
  intros. destruct ma. reflexivity. reflexivity.
  intros. destruct ma. reflexivity. reflexivity.
Qed.
