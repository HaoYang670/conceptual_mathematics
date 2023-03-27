From Coq Require Import Logic.FunctionalExtensionality.
From CM Require Import Category.

Module Inverse.
  Definition inverse {A B: Object} (f: Morphism A B) (g: Morphism B A) :=
    compose f g = identity A /\ compose g f = identity B.

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
    assert (H3: compose g (compose f k) = compose g (compose f g)).
    { rewrite H. rewrite H0. reflexivity. }
    repeat rewrite <- composition_assoc in H3.
    rewrite H1 in H3. repeat rewrite composition_id_left in H3.
    symmetry. apply H3.
  Qed.
End Inverse.

Module Isomorphism.
  Import Inverse.
  Definition isomorphism {A B: Object} (f: Morphism A B) :=
    exists g: Morphism B A, inverse f g.

  Theorem isomorphism_cancellation_left: 
    forall (A B C: Object) (f: Morphism A B) (h k: Morphism B C),
      isomorphism f ->
      compose f h = compose f k ->
      h = k.
  Proof.
    intros. destruct H as [g H].
    assert (compose (compose g f) h = compose (compose g f) k).
    {
      repeat rewrite composition_assoc. rewrite H0. reflexivity.
    }
    unfold inverse in H. destruct H. rewrite H2 in H1. 
    repeat rewrite composition_id_left in H1. apply H1.
  Qed.

  Theorem isomorphism_cancellation_right: 
    forall (A B C: Object) (f: Morphism A B) (h k: Morphism C A),
      isomorphism f ->
      compose h f = compose k f ->
      h = k.
  Proof.
    intros. destruct H as [g H].
    assert (compose h (compose f g) = compose k (compose f g)).
    {
      repeat rewrite <- composition_assoc. rewrite H0. reflexivity.
    }
    unfold inverse in H. destruct H. rewrite H in H1. 
    repeat rewrite composition_id_right in H1. apply H1.
  Qed.
End Isomorphism.

Module Isomorphic.
  Import Isomorphism.

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
    intros. destruct H. destruct H0. exists (compose x x0).
    destruct H. destruct H0. exists (compose x2 x1).
    destruct H. destruct H0. split; rewrite composition_assoc.
    - assert (compose x0 (compose x2 x1) = compose (compose x0 x2) x1).
      { rewrite <- composition_assoc. reflexivity. }
      rewrite H3. rewrite H0. destruct (composition_id B A x1). rewrite H4. assumption.
    - assert (compose x1 (compose x x0) = compose (compose x1 x) x0).
      { rewrite <- composition_assoc. reflexivity. }
      rewrite H3. rewrite H1. destruct (composition_id B C x0). rewrite H4. assumption.
  Qed.
End Isomorphic.