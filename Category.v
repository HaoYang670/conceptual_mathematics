From Coq Require Import Logic.FunctionalExtensionality.

Definition Object := Type.

(* ‘singleton’ set, a set with exactly one element. *)
Definition Singleton: Object := True.

Definition Morphism (domain: Object) (codomain: Object): Type:= domain -> codomain.

Definition EndoMorphism (domain: Object): Type := Morphism domain domain.

(* All Objects has an identity morphism *)
Definition identity (x: Object): (Morphism x x) :=
  fun x => x.

(* Composition of 2 morphisms *)
Definition compose {domain: Object} {mid: Object} {codomain: Object} 
  (f: Morphism domain mid) (g: Morphism mid codomain): (Morphism domain codomain)
  := fun x => g (f x).

Definition Idempotent {A: Object} (e: EndoMorphism A) := compose e e = e.

(** The identity function is a unit in the composition *)
Theorem composition_id: forall (A B: Object) (f: Morphism A B),
  compose (identity A) f = f /\ compose f (identity B) = f.
Proof.
  unfold compose. unfold identity. intros.
  split; apply functional_extensionality; intros;
  reflexivity.
Qed.

(* Split composition_id, for easily using *)
Theorem composition_id_left: forall (A B: Object) (f: Morphism A B),
  compose (identity A) f = f.
Proof. auto. Qed.

Theorem composition_id_right: forall (A B: Object) (f: Morphism A B),
  compose f (identity B) = f.
Proof. auto. Qed.

(** h o (g o f) = (h o g) o f *)
Theorem composition_assoc: forall (A B C D: Object) (f: Morphism A B) (g: Morphism B C) (h: Morphism C D),
  compose (compose f g) h = compose f (compose g h).
Proof.
  intros. unfold compose. reflexivity.
Qed.