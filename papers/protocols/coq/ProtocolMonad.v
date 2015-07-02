Require Export StateMonad.

Definition C := Type.
Definition ID := Type.

(**
- [send] - Send a message of type [A] to [ID] over channel [C] and result in a [State] to be evaluated locally.
- [receive] - Receive a message of type [A] from [ID] on channel [C] and result in a [State] to be evaluated locally.
- [vtpm] - Communicate with the vTPM with result [A] and [State] for evaluation
locally
- [ifM] - Evaluate [Prop] locally and return the appropriate next state.  Note
this is an if statement, not an if expression.
- [mapM] - _Definition is pending_
- [foldM] - _Definition is pending_
- [bundle] - _Definition is pending_
*)

Class ProtocolMonad {S A:Type} `(StateMonad) : Type :=
{
  send : C -> ID -> A -> (State S A)
  ; receive : C -> ID -> A -> (State S A)
  ; vtpm : A -> (State S A)                              
  ; ifM : bool -> (State S A) -> (State S A) -> (State S A)
  ; mapM : (State S A)
  ; foldM : (State S A)
  ; bundle : A -> (State S A)
}.

Instance ProtocolMonadI (S A:Type) : StateMonad State StateMonadI :=
{
  put := (fun (s:S) => (fun (a:A) => (fun (_:S) => (a,s))))
  ; get := (fun (a:A) => (fun (s:S) => (s,s)))
}.


Instance ProtocolMonadEx : ProtocolMonad (ProtocolMonadI nat nat) :=
{
  send := (fun (_:C) => (fun (_:ID) => (fun (a:nat) => (fun (s:nat) => (a,s)))))
  ; receive := (fun (_:C) => (fun (_:ID) => (fun (a:nat) => (fun (s:nat) => (a,s)))))
  ; ifM := (fun (p:bool) => (fun (t:(State nat nat)) => (fun (f:(State nat nat)) => if p then t else f)))
  ; mapM := (fun (s:nat) => (0,s))
  ; foldM := (fun (s:nat) => (0,s))
  ; vtpm := (fun (a:nat) => (fun (s:nat) => (a,s)))
  ; bundle := (fun (a:nat) => (fun (s:nat) => (a,s)))
}.