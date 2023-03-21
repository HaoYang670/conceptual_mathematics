From Coq Require Import Logic.FunctionalExtensionality.

Definition Object: Type := Type.

(* ‘singleton’ set, a set with exactly one element. *)
Definition Singleton: Object := True.

Definition Morphism (domain: Object) (codomain: Object): Type:= domain -> codomain.

(* All Objects has an identity morphism *)
Definition identity (x: Object): (Morphism x x) :=
  fun x => x.

(* Composition of 2 morphisms *)
Definition composition {domain: Object} {mid: Object} {codomain: Object} 
  (f: Morphism domain mid) (g: Morphism mid codomain): (Morphism domain codomain)
  := fun x => g (f x).

(** The identity function is a unit in the composition *)
Theorem composition_id: forall (A B: Object) (f: Morphism A B),
  composition (identity A) f = f /\ composition f (identity B) = f.
Proof.
  unfold composition. unfold identity. intros.
  split; apply functional_extensionality; intros;
  reflexivity.
Qed.

(** h o (g o f) = (h o g) o f *)
Theorem composition_assoc: forall (A B C D: Object) (f: Morphism A B) (g: Morphism B C) (h: Morphism C D),
  composition (composition f g) h = composition f (composition g h).
Proof.
  intros. unfold composition. reflexivity.
Qed.