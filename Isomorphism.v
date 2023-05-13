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
  Definition isIsomorphism {A B: Object} (f: Morphism A B) :=
    exists g: Morphism B A, inverse f g.

  Definition isomorphismSet (A B: Object): Object :=
    {f: Morphism A B | isIsomorphism f}.

  Theorem isomorphism_cancellation_left: 
    forall (A B C: Object) (f: Morphism A B) (h k: Morphism B C),
      isIsomorphism f ->
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
      isIsomorphism f ->
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

  Theorem isomorphism_compose:
    forall (A B C: Object) (f: Morphism A B) (g: Morphism B C),
      isIsomorphism f ->
      isIsomorphism g ->
      isIsomorphism (compose f g).
  Proof.
    unfold isIsomorphism. intros A B C f g [f' [Hf0 Hf1]] [g' [Hg0 Hg1]].
    exists (compose g' f'). unfold inverse.
    split; rewrite composition_assoc.
    - assert (compose g (compose g' f') = f').
      { rewrite <- composition_assoc. rewrite Hg0. auto. }
      rewrite H. auto.
    - assert (compose f' (compose f g) = g).
      { rewrite <- composition_assoc. rewrite Hf1. auto. }
      rewrite H. auto.
  Qed.

End Isomorphism.

Module Isomorphic.
  Import Isomorphism.

  Definition isomorphic (A B: Object) :=
    exists f: Morphism A B, isIsomorphism f.

  (* A is isomorphic to A. *)
  Theorem isomorphic_refl: forall A: Object,
    isomorphic A A.
  Proof.
    intros. unfold isomorphic. exists (identity A).
    unfold isIsomorphism. exists (identity A). 
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

Module RetractionAndSection.
  Definition retraction {A B} (f: Morphism A B) (r: Morphism B A): Prop :=
    compose f r = identity A.
  Definition section {A B} (f: Morphism A B) (s: Morphism B A): Prop :=
    retraction s f.

  Lemma Proposition1: forall (A B: Object) (f: Morphism A B),
    (exists s, section f s) ->
    forall (T: Object) y, exists (x: Morphism T A), compose x f = y.
  Proof.
    intros A B f [s H] T y. exists (compose y s).
    rewrite composition_assoc. rewrite H. apply composition_id_right.
  Qed.

  Lemma Proposition1_dual: forall (A B: Object) (f: Morphism A B),
    (exists r, retraction f r) ->
    forall (T: Object) g, exists (t: Morphism B T), compose f t = g.
  Proof.
    intros A B f [r H] T g. exists (compose r g).
    rewrite <- composition_assoc. rewrite H. apply composition_id_left.
  Qed.

  Lemma Proposition2: forall (A B: Object) (f: Morphism A B),
    (exists r, retraction f r) ->
    forall (T: Object) (x1 x2: Morphism T A),
      compose x1 f = compose x2 f -> x1 = x2.
  Proof.
    intros. destruct H as [r H].
    assert (helper: compose (compose x1 f) r = compose (compose x2 f) r).
    { rewrite H0. reflexivity. }
    clear H0. repeat rewrite composition_assoc in helper.
    rewrite H in helper. repeat rewrite composition_id_right in helper.
    apply helper.
  Qed.

  Lemma Proposition2_dual: forall (A B: Object) (f: Morphism A B),
    (exists s, section f s) ->
    forall (T: Object) (t1 t2: Morphism B T),
      compose f t1 = compose f t2 -> t1 = t2.
  Proof.
    intros. destruct H as [s H].
    assert (helper: compose s (compose f t1) = compose s (compose f t2)).
    { rewrite H0. reflexivity. }
    repeat rewrite <- composition_assoc in helper.
    rewrite H in helper. repeat rewrite composition_id_left in helper.
    apply helper.
  Qed.

  Definition injective {A B: Object} (f: Morphism A B) := Proposition2 A B f.
  Definition monomorphism {A B: Object} (f: Morphism A B) := injective f.

  Lemma Proposition3: forall (A B C: Object) (f: Morphism A B) (g: Morphism B C) r1 r2,
    retraction f r1 ->
    retraction g r2 ->
    exists r3, retraction (compose f g) r3.
  Proof.
    intros. exists (compose r2 r1). unfold retraction. rewrite composition_assoc.
    assert (H1: compose g (compose r2 r1) = r1).
    { rewrite <- composition_assoc. rewrite H0. apply composition_id_left. }
    rewrite H1. apply H.
  Qed.

  Definition epimorphism {A B: Object} (f: Morphism A B) := Proposition2_dual A B f.
  
  Lemma Proposition3_dual: forall (A B C: Object) (f: Morphism A B) (g: Morphism B C) s1 s2,
    section f s1 ->
    section g s2 ->
    exists r3, section (compose f g) r3.
  Proof.
    intros. exists (compose s2 s1). unfold section. unfold retraction. rewrite composition_assoc.
    assert (H1: compose s1 (compose f g) = g).
    { rewrite <- composition_assoc. rewrite H. apply composition_id_left. }
    rewrite H1. apply H0.
  Qed.

  Lemma Idempotent_retraction: forall (A B: Object) (f: Morphism A B) r,
    retraction f r ->
    Idempotent (compose f r).
  Proof.
    intros. unfold Idempotent. unfold retraction in H. rewrite H. auto.
  Qed.

  Theorem uniqueness_of_inverses: forall (A B: Object) (f: Morphism A B) r s,
    retraction f r ->
    section f s ->
    r = s.
  Proof.
    intros. unfold section in H0. unfold retraction in H, H0.
    rewrite <- composition_id_right. rewrite <- H.
    rewrite <- composition_assoc. rewrite H0.
    auto.
  Qed.
End RetractionAndSection.

Module Automorphisms.
  Import Isomorphism.
  Import Isomorphic.
  From Coq Require Import Logic.FunctionalExtensionality.

  Definition isAutomorphism {A: Object} := isIsomorphism (A := A) (B := A).

  Definition automorphismSet (A: Object): Object :=
    {f: EndoMorphism A | isAutomorphism f}.
  
  Lemma compose_auto_iso_is_iso: forall A B a (f: Morphism A B),
    isAutomorphism a ->
    isIsomorphism f ->
    isIsomorphism (compose a f).
  Proof.
    unfold isAutomorphism. intros. apply isomorphism_compose; auto.
  Qed.

  (* if there are any isomorphisms A —> B,
     then there are the same number of them as there are automorphisms of A. *)
  Theorem Iso_auto_isomorphic: forall A B,
    isomorphic A B ->
    isomorphic (automorphismSet A) (isomorphismSet A B).
  Proof.
    unfold isomorphic. intros A B [f H].
    exists (fun (ams: automorphismSet A) =>
      let 'exist _ a pa := ams in
      exist _ (compose a f) (compose_auto_iso_is_iso A B a f pa H)).
    destruct H as [f' H].
    assert (H': isIsomorphism f'). { exists f. destruct H. split; auto. }
    exists (fun (ims: isomorphismSet A B) =>
      let 'exist _ g pg := ims in
      exist _ (compose g f') (isomorphism_compose A B A g f' pg  H')).
    split.
    - apply functional_extensionality. intros [a Ha].
      unfold compose. unfold identity.
      assert (H0: isIsomorphism = (fun f0 : EndoMorphism A => isAutomorphism f0)). { auto. }
      assert (H1: (fun x : A => f' (f (a x))) = a).
      {
        assert (H1: (fun x : A => f' (f (a x))) = compose a (compose f f')).
        { unfold compose. auto. }
        rewrite H1. rewrite (proj1 H). apply composition_id_right.
      }
      apply eq_exist_curried with H1. unfold eq_rect.
      (* related to dependent type which I don't know now. *)
      Admitted.
End Automorphisms.
