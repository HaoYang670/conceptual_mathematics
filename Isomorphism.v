From Coq Require Import Logic.FunctionalExtensionality.
From CM Require Import Category.

Definition inverse {A B: Object} (f: Morphism A B) (g: Morphism B A) :=
  composition f g = identity A /\ composition g f = identity B.

(** A morphism cannot have more than one inverse.
  The Idea is to prove (g . f . k = g . f . g),
  then use the associtivity law to prove ((g . f) . k = (g . f) . g),
  finally use the identity law to prove (k = g).
*)
Theorem inverse_unique: forall (A B: Object) (f: Morphism A B) (g k: Morphism B A),
  inverse f g ->
  inverse f k ->
  g = k.
Proof.
  intros. unfold inverse in *. destruct H, H0.
  assert (H3: composition g (composition f k) = composition g (composition f g)).
  { rewrite H. rewrite H0. reflexivity. }
  repeat rewrite <- composition_assoc in H3.
  rewrite H1 in H3. destruct (composition_id B A k) as [H4 _].
  destruct (composition_id B A g) as [H5 _].
  rewrite H4 in H3. rewrite H5 in H3.
  symmetry. apply H3.
Qed.

Definition isomorphism {A B: Object} (f: Morphism A B) :=
  exists g: Morphism B A, inverse f g.

Definition isomorphic (A B: Object) :=
  exists f: Morphism A B, isomorphism f.

(* A is isomorphic to A. *)
Theorem isomorphic_refl: forall A: Object,
  isomorphic A A.
Proof.
  intros. unfold isomorphic. exists (identity A).
  unfold isomorphism. exists (identity A). 
  split; apply composition_id.
Qed.

(* If A is isomorphic to B, then B is isomorphic to A. *)
Theorem isomorphic_symm: forall (A B: Object),
  isomorphic A B -> isomorphic B A.
Proof.
  intros. destruct H. destruct H. destruct H. 
  exists x0. exists x. split; assumption.
Qed.

(* If A is isomorphic to B, and B is isomorphic to C, then A is isomorphic to C. *)
Theorem isomorphic_tran: forall (A B C: Object),
  isomorphic A B ->
  isomorphic B C ->
  isomorphic A C.
Proof.
  intros. destruct H. destruct H0. exists (composition x x0).
  destruct H. destruct H0. exists (composition x2 x1).
  destruct H. destruct H0. split; rewrite composition_assoc.
  - assert (composition x0 (composition x2 x1) = composition (composition x0 x2) x1).
    { rewrite <- composition_assoc. reflexivity. }
    rewrite H3. rewrite H0. destruct (composition_id B A x1). rewrite H4. assumption.
  - assert (composition x1 (composition x x0) = composition (composition x1 x) x0).
    { rewrite <- composition_assoc. reflexivity. }
    rewrite H3. rewrite H1. destruct (composition_id B C x0). rewrite H4. assumption.
Qed.
