From Coq Require Import Logic.FunctionalExtensionality.

Definition Object: Type := Type.

Definition Morphism (domain: Object) (codomain: Object): Type:= domain -> codomain.

(* All Objects has an identity morphism *)
Definition identity (x: Object): (Morphism x x) :=
  fun x => x.

(* Composition of 2 morphisms *)
Definition composition {domain: Object} {mid: Object} {codomain: Object} 
  (f: Morphism domain mid) (g: Morphism mid codomain): (Morphism domain codomain)
  := fun x => g (f x).

(** The identity function is a unit in the composition *)
Theorem identity_law_a: forall (a b: Object) (f: Morphism a b),
  composition (identity a) f = f /\ composition f (identity b) = f.
Proof.
  unfold composition. unfold identity. intros.
  split; apply functional_extensionality; intros;
  reflexivity.
Qed.
