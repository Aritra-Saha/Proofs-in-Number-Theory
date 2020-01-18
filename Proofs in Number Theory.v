(** Load required packages.  Not all of these packages are needed right away,
    but they may be useful later. **)

Require Export Setoid List Sorted Constructive_sets Utf8_core Wf_nat
        ProofIrrelevance Permutation IndefiniteDescription ChoiceFacts
        Description Classical PropExtensionality.

(** Math symbols for cut and paste: ∀ ∃ → ↔ ∧ ∨ ¬ ≠ ≤ ≥ ∅ ℕ ℤ ∈ ∉ ⊂ ∑ ∏ λ **)

(** Axioms for the integers. **)

(* Parameters *)

Parameter Z : Set.

Parameter add mult : Z → Z → Z.
Parameter neg : Z → Z.
Parameter zero one : Z.
Parameter ℕ : Ensemble Z.

(* Definitions and notations *)

Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mult.
Notation "- x" := (neg x).
Notation "- 0" := (neg 0).
Notation "- 1" := (neg 1).
Definition sub a b := a + -b.
Infix "-" := sub.

Infix "∋" := (In Z) (at level 70).
Notation "x ∈ S" := (S ∋ x) (at level 70).
Notation "x ∉ S" := (¬(x ∈ S)) (at level 70).
Infix "⊂" := (Included Z) (at level 70).
Notation "∅" := (Empty_set Z).
Notation "{ x : A | P }" := (λ x : A, P).
Definition setminus (A B : Ensemble Z) := {x : Z | x ∈ A ∧ x ∉ B}.
Infix "\" := setminus (at level 80).

Definition lt a b := b - a ∈ ℕ.
Definition le (a b : Z) := ((lt a b) ∨ a = b).

Infix "<" := lt.
Notation "a > b" := (b < a) (only parsing).
Infix "≤" := le (at level 70).
Notation "a ≥ b" := (b ≤ a) (at level 70, only parsing).

Notation "x < y < z" := (x < y ∧ y < z).
Notation "x ≤ y < z" :=
  (x ≤ y ∧ y < z) (at level 70, y at next level).

Definition divide (x y : Z) := ∃ z : Z, y = z * x.
Notation "( x | y )" := (divide x y).

Definition pm (a b : Z) := (a = b ∨ a = -b).
Notation "a = ± b" := (pm a b) (at level 60).
Definition assoc (a b : Z) := (a | b) ∧ (b | a).
Infix "~" := assoc (at level 70).
Notation "x ≠ ± y" := (¬ (x = ± y)) (at level 60).

Definition unit (a : Z) := (a | 1).

Definition prime (p : Z) :=
  p ≠ ± 1 ∧ ∀ d : Z, (d | p) → d = ± 1 ∨ d = ± p.

Notation "2" := (1+1)(only parsing).

(* Axioms *)

Axiom A1 : ∀ a b   : Z, a + b = b + a.
Axiom A2 : ∀ a b c : Z, a + (b + c) = (a + b) + c.
Axiom A3 : ∀ a     : Z, a + 0 = a.
Axiom A4 : ∀ a     : Z, a + -a = 0.
Axiom M1 : ∀ a b   : Z, a * b = b * a.
Axiom M2 : ∀ a b c : Z, a * (b * c) = (a * b) * c.
Axiom M3 : ∀ a     : Z, a * 1 = a.
Axiom D1 : ∀ a b c : Z, (a + b) * c = a * c + b * c.

Axiom Natural1 : 1 ∈ ℕ.
Axiom Natural2 : ∀ a b : Z, a ∈ ℕ → b ∈ ℕ → a+b ∈ ℕ.
Axiom Natural3 : ∀ a b : Z, a ∈ ℕ → b ∈ ℕ → a*b ∈ ℕ.

Axiom Trichotomy1 : ∀ a : Z,
    (a ∈ ℕ ∧ a ≠ 0 ∧ -a ∉ ℕ) ∨
    (a ∉ ℕ ∧ a = 0 ∧ -a ∉ ℕ) ∨
    (a ∉ ℕ ∧ a ≠ 0 ∧ -a ∈ ℕ).

Axiom Well_Ordering_Principle : ∀ S : Ensemble Z,
    S ≠ ∅ → S ⊂ ℕ → ∃ a : Z, (a ∈ S) ∧ (∀ n : Z, n ∈ S → a ≤ n).

(* Some useful theorems *)

Lemma S1 : ∀ a b c : Z, a = b → a + c = b + c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Lemma S2 : ∀ a b c : Z, a = b → a * c = b * c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Theorem Well_Ordering_Principle' : ∀ S : Ensemble Z,
    (∃ s : Z, S s) →
    (∀ x : Z, S x → x ∈ ℕ) →
    ∃ a : Z, S a ∧ (∀ n : Z, S n → a ≤ n).
Proof.
  intros S [x H] H0.
  destruct (Well_Ordering_Principle S); eauto.
  intros H1.
  now rewrite H1 in H.
Qed.

Theorem Natural0 : 0 ∉ ℕ.
Proof.
  intros; pose proof Trichotomy1 0; tauto.
Qed.

Theorem NaturalNE : ℕ ≠ ∅.
Proof.
  intros H; pose proof Natural1; now rewrite H in H0.
Qed.

Theorem Mathematical_Induction :
  ∀ S : Ensemble Z, 1 ∈ S → (∀ n : Z, n ∈ S → n + 1 ∈ S) → ℕ ⊂ S.
Proof.
  intros S H H0 x H1.
  apply NNPP.
  intros H2.
  destruct (Well_Ordering_Principle' {x : Z | x ∈ ℕ ∧ x ∉ S}) as [y [[H3 H4] H5]];
    eauto; try tauto.
  contradiction H4.
  rewrite <-(A3 y), <-(A4 1), (A1 1), A2.
  apply H0, NNPP.
  intros H6.
  pose proof Natural1 as H7.
  destruct (classic (y+-1 ∈ ℕ)) as [H8 | H8].
  - destruct (H5 (y+-1)) as [H9 | H9]; auto.
    + unfold lt, sub in H9.
      rewrite A1, A2, (A1 (-y)), A4, A1, A3 in H9.
      pose proof (Trichotomy1 1); tauto.
    + apply (S1 _ _ (-y+1)) in H9.
      rewrite A2, A4, A1, A3, (A1 y), A2, <-(A2 (-1)), A4, A3, A1, A4 in H9.
      contradiction Natural0.
      now rewrite <-H9.
  - destruct (Trichotomy1 (y+-1)) as [[H9 [H10 H11]] | [[H9 [H10 H11]] | [H9 [H10 H11]]]];
      try tauto.
    + now rewrite <-(A3 1), <-H10, A1, <-A2, (A1 (-1)), A4, A3 in H.
    + rewrite <-2 (A3 _), <-(A4 y), <-(A4 1), (A1 1), <-A2, (A2 _ (-1))
      , <-(A2 y), (A1 (-y)), (A2 y), <-(A2 _ (-y)), A2, (A1 _ (y+-1)),
      A4, A1, A3, A1 in H11 at 1.
      destruct (Well_Ordering_Principle' ({z : Z | z ∈ ℕ ∧ (1+-z) ∈ ℕ}))
        as [z [[H12 H13] H14]]; eauto; try tauto.
      pose proof (Natural3 _ _ H12 H13) as H15.
      rewrite M1, D1, (M1 1), M3 in H15.
      assert (-z*z = -(z*z)) as H16.
      { rewrite <-(A3 _), <-(A3 (-(z*z))), <-(A4 (z*z)), ? A2, (A1 (-(z*z))),
        A4, (A1 0), A3, <-D1, (A1 (-z)), A4, <-(A3 (0*z)).
        rewrite <-(A4 z), <-(M3 z) at 2.
        now rewrite A2, (M1 _ 1), <-D1, (A1 0), A3, M1, M3, A4, A1, A3. }
      destruct (H14 (z*z)) as [H17 | H17].
      split.
      * now apply Natural3.
      * rewrite <-H16, <-(A3 1), <-(A4 z), <-(M3 (-z)), <-? A2, ? (M1 (-z)),
        <-D1, A2, <-(M3 (1+z)), ? (M1 (1+z)), <-D1 at 1.
        apply Natural3, Natural2; auto.
      * unfold lt, sub in H17.
        pose proof (Natural2 _ _ H15 H17) as H18.
        rewrite H16, A2, <-(A2 z), (A1 (-(z*z))), A4, A3, A4 in H18.
        contradiction Natural0.
      * rewrite H16, H17, A4 in H15 at 1.
        contradiction Natural0.
Qed.
      
Theorem Mathematical_Induction' : ∀ p : Z → Prop,
    p 1 ∧ (∀ a : Z, a ∈ ℕ → p a → p (a + 1)) → ∀ a : Z, a ∈ ℕ → p a.
Proof.
  intros p [H H0] a H1.
  pose proof Natural1 as H2.
  apply (Mathematical_Induction {x : Z | x ∈ ℕ ∧ p x}); unfold In; auto.
  split; intuition.
  now apply Natural2.
Qed.
    
Theorem Natural4 : ∀ a : Z, a ∈ ℕ → - a ∉ ℕ.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural5 : ∀ a : Z, - a ∉ ℕ → a ∈ ℕ ∨ a = 0.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural6 : ∀ a : Z, a ∉ ℕ → a = 0 ∨ - a ∈ ℕ.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural7 : ∀ a : Z, a ∉ ℕ → a ≠ 0 → - a ∈ ℕ.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.
  
Theorem Natural8 : ∀ a : Z, a ≠ 0 → a ∈ ℕ ∨ - a ∈ ℕ.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural9 : ∀ a : Z, a ≠ 0 → a ∈ ℕ ↔ - a ∉ ℕ.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural10 : ∀ a : Z, a ∈ ℕ ∨ a = 0 ∨ - a ∈ ℕ.
Proof.
  intros a; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural11 : ∀ a : Z, a ∈ ℕ ↔ a ≠ 0 ∧ ¬ - a ∈ ℕ.
Proof.
  intros; pose proof Trichotomy1 a; tauto.
Qed.

Theorem Natural12 : ∀ a : Z, a ∈ ℕ ↔ 0 < a.
Proof.
  split; intros H; unfold lt, sub in *;
    now rewrite <-(A3 (-0)), (A1 (-0)), A4, A3 in *.
Qed.

Theorem Natural13 : ℕ = {x : Z | 0 < x}.
Proof.
  apply Extensionality_Ensembles.
  split; intros x H; now rewrite Natural12 in *.
Qed.

Theorem Ordering0 : ∀ a b : Z, a < b ↔ ∃ c : Z, c ∈ ℕ ∧ b = a+c.
Proof.
  intros a b.
  split; intros H; unfold lt, sub in *.
  - exists (b+-a).
    split; auto.
    now rewrite A1, <-A2, (A1 (-a)), A4, A3.
  - destruct H as [c [H H0]].
    now rewrite H0, A1, A2, (A1 (-a)), A4, A1, A3.
Qed.

Theorem Ordering1 : ∀ a b c : Z, a < b → a + c < b + c.
Proof.
  intros a b c H.
  unfold lt, sub in *.
  now rewrite <-2 (A3 (-(a+c))), <-? A2, <-(A4 a), <-(A4 c), <-(A2 a),
  (A2 (-a)), (A1 (-a)), ? (A2 a), <-(A2 _ (-a)), (A2 _ (a+c)),
  (A1 _ (a+c)), A4, (A1 0), A3, (A1 (-a)), (A2 c), A4, (A1 0), A3 at 1.
Qed.

Theorem Ordering2 : ∀ a b : Z, 0 < a → 0 < b → 0 < a * b.
Proof.
  intros a b H H0.
  unfold lt, sub in *.
  rewrite <-(A3 (-0)), (A1 (-0)), A4, A3 in *.
  now apply Natural3.
Qed.

Theorem Ordering3 : ∀ a b c : Z, a < b → b < c → a < c.
Proof.
  intros a b c H H0.
  unfold lt, sub in *.
  rewrite <-(A3 c), <-(A4 b), (A1 b), A2, <-(A2 _ b).
  now apply Natural2.
Qed.

Theorem Ordering4 : ∀ a : Z, a < a + 1.
Proof.
  intros a.
  unfold lt, sub in *.
  rewrite A1, A2, (A1 (-a)), A4, A1, A3.
  exact Natural1.
Qed.

Theorem Ordering5 : ∀ a b : Z, a ≠ b ↔ a < b ∨ b < a.
Proof.
  intros a b.
  unfold lt, sub in *.
  replace (a ≠ b) with (b + -a ≠ 0).
  - replace (a+-b) with (-(b+-a)).
    + pose proof (Trichotomy1 (b+-a)).
      tauto.
    + now rewrite <-(A3 (a+-b)), <-(A4 (b+-a)), ? A2, <-(A2 a),
      (A1 (-b)), A4, A3, A4, (A1 0), A3.
  - apply propositional_extensionality.
    split; intros H; contradict H.
    + now rewrite H, A4.
    + now rewrite <-(A3 a), <-H, A1, <-A2, (A1 (-a)), A4, A3.
Qed.

Theorem Ordering6 : ∀ a b : Z, ¬ a < b → b ≤ a.
Proof.
  intros a b H.
  pose proof (Ordering5 a b).
  destruct (classic (a = b)).
  - now right.
  - unfold le.
    tauto.
Qed.

Theorem Ordering7 : ∀ a b : Z, a < b → a ≠ b.
Proof.
  intros a b H.
  pose proof (Ordering5 a b).
  tauto.
Qed.

Theorem Ordering8 : ∀ a b : Z, a < b ↔ ¬ b ≤ a.
Proof.
  intros a b.
  pose proof (Ordering5 a b).
  destruct (classic (a = b)) as [H0 | H0]; split; intros H1; try intros H2.
  - tauto.
  - contradiction H1.
    right.
    now symmetry.
  - destruct H2 as [H2 | H2].
    + unfold lt, sub in *.
      pose proof (Natural2 _ _ H1 H2).
      rewrite ? A2, <-(A2 b), (A1 (-a)), A4, A3, A4 in H3.
      contradiction Natural0.
    + now symmetry in H2.
  - unfold le in *.
    tauto.
Qed.

Theorem Ordering9 : ∀ a b : Z, a = b ↔ ¬ (a < b ∨ b < a).
Proof.
  intros a b.
  pose proof (Ordering5 a b).
  tauto.
Qed.

Theorem Ordering10 : ∀ a : Z, a < 0 ∨ a = 0 ∨ 0 < a.
Proof.
  intros a.
  unfold lt, sub.
  rewrite A1, A3, <-(A3 (-0)), (A1 (-0)), A4, A3.
  pose proof Trichotomy1 a.
  tauto.
Qed.

(* The following definitions can be used to rename the above theorems to
   any names that you like. Feel free to change them as you wish. *)

Definition N := ℕ. (* Allows you to use a non-fancy letter N for naturals *)

Definition NE := NaturalNE.
Definition N0 := Natural0.
Definition N1 := Natural1.
Definition N2 := Natural2.
Definition N3 := Natural3.
Definition N4 := Natural4.
Definition N5 := Natural5.
Definition N6 := Natural6.
Definition N7 := Natural7.
Definition N8 := Natural8.
Definition N9 := Natural9.
Definition N10 := Natural10.
Definition N11 := Natural11.
Definition N12 := Natural12.
Definition N_gt_0 := Natural13.

Definition T := Trichotomy1.

Definition O0 := Ordering0.
Definition O1 := Ordering1.
Definition O2 := Ordering2.
Definition O3 := Ordering3.
Definition O4 := Ordering4.
Definition O5 := Ordering5.
Definition O6 := Ordering6.
Definition O7 := Ordering7.
Definition O8 := Ordering8.
Definition O9 := Ordering9.
Definition O10 := Ordering10.

Definition Ind := Mathematical_Induction.
Definition WOP := Well_Ordering_Principle'.

(** Assignment problems **)

Theorem A1P1 : ∀ a : Z, 0 + a = a.
Proof.
intros.
rewrite A1, A3.
trivial.
Qed.

Theorem A1P2 : ∀ a : Z, -a + a = 0.
Proof.
intros.
rewrite A1, A4.
trivial.
Qed.

Theorem A1P3 : ∀ a : Z, 1 * a = a.
Proof.
intros.
rewrite M1, M3.
congruence.
Qed.

Theorem A1P4 : ∀ a b : Z, a + b = 0 → b = -a.
Proof.
intros.
apply (S1 _ _ (-a)) in H.
rewrite <-A2 in H.
rewrite A1 in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite A1, A3 in H.
exact H.
Qed.

Theorem A1P5 : ∀ a : Z, -(-a) = a.
Proof.
intros.
pose proof (A4 (-a)).
apply (S1 _ _ a) in H.
rewrite <-A2, A1 in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A3 in H.
rewrite A1, A3 in H.
exact H.
Qed.

Theorem A1P6 : ∀ a : Z, 0 * a = 0.
Proof.
intros.
pose proof (A3 (0 * a)).
rewrite <-(A4 a) in H at 2.
rewrite A2 in H.
rewrite <-(M3 a)in H at 2.
rewrite (M1 a) in H.
rewrite <-D1 in H.
rewrite (A1 0) in H.
rewrite A3 in H.
rewrite M1 in H.
rewrite M3 in H.
rewrite A4 in H.
symmetry.
exact H.
Qed.

Theorem A1P7 : ∀ a : Z, -1 * a = -a.
Proof.
intros.
rewrite <-(A3 (-1 * a)).
rewrite <-(A4 a).
rewrite A2.
rewrite <-(M3 a) at 2.
rewrite (M1 a).
rewrite <-D1.
rewrite A1P2.
rewrite A1P6.
rewrite A1, A3.
congruence.
Qed.

Theorem A1P8 : ∀ a b : Z, -a * -b = a * b.
Proof.
intros.
rewrite <-A1P7.
rewrite <-(A1P7 b).
rewrite M2, M1.
rewrite <-M2.
rewrite M1.
rewrite (M1 a).
rewrite M2.
rewrite A1P7.
rewrite A1P5.
rewrite M1.
rewrite A1P3.
rewrite M1.
trivial.
Qed.

Theorem A1P9 : ∀ a b : Z, a + b = a → b = 0.
Proof.
intros.
apply (S1 _ _ (-a)) in H.
rewrite A4 in H.
rewrite <-A2 in H.
rewrite A1 in H.
rewrite <-A2, A1P2 in H.
rewrite A3 in H.
exact H.
Qed.

Theorem A1P11 : ∀ a b : Z, a * b = 0 → a = 0 ∨ b = 0.
Proof.
intros.
destruct (classic (a = 0)).
left.
exact H0.
destruct (classic (b = 0)).
right.
exact H1.
apply N8 in H0.
apply N8 in H1.
destruct H0, H1.
pose proof (N3 a b).
apply H2 in H0.
rewrite H in H0.
pose proof N0.
contradiction.
exact H1.
pose proof (N3 a (-b)).
apply H2 in H0.
rewrite <-A1P7 in H0.
rewrite M2 in H0.
rewrite M1 in H0.
rewrite M2 in H0.
rewrite M1 in H.
rewrite H in H0.
rewrite A1P6 in H0.
pose proof N0.
contradiction.
exact H1.
pose proof (N3 (-a) b).
apply H2 in H0.
rewrite <-A1P7 in H0.
rewrite <-M2 in H0.
rewrite H in H0.
rewrite M1, A1P6 in H0.
pose proof N0.
contradiction.
exact H1.
pose proof (N3 (-a) (-b)).
apply H2 in H0.
rewrite A1P8 in H0.
rewrite H in H0.
pose proof N0.
contradiction.
trivial.
Qed.

Lemma S3 : forall a b c : Z, a * c = b * c -> a = b \/ c = 0.
Proof.
intros.
apply (S1 _ _ (- b * c)) in H.
rewrite <-A1P7 in H at 2.
rewrite <-M2 in H.
rewrite A1P7 in H.
rewrite A4 in H.
rewrite <-D1 in H.
apply A1P11 in H.
destruct H.
apply (S1 _ _ b) in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A3, A1P1 in H.
left.
exact H.
right.
exact H.
Qed.

Theorem A1P10 : ∀ a b : Z, a * b = a → b = 1 ∨ a = 0.
Proof.
intros.
apply (S1 _ _ (-a)) in H.
rewrite A4 in H.
rewrite <-A1P7 in H.
rewrite M1 in H.
rewrite <-D1 in H.
apply A1P11 in H.
destruct H.
left.
apply (S1 _ _ 1) in H.
rewrite A1P1 in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
exact H.
right.
exact H.
Qed.

Lemma L2P1 : ∀ a m x : Z, (a | m) → (a | m * x).
Proof.
intros a m x H.
unfold divide in *.
destruct H.
rewrite H.
exists (x0 * x).
rewrite <-M2.
symmetry.
rewrite M2.
rewrite M1.
symmetry.
rewrite M1.
symmetry.
rewrite M2.
rewrite M1.
rewrite M1.
symmetry.
rewrite M1.
apply S2.
rewrite M1.
congruence.
Qed.

Theorem A2P1 : ∀ a m n x y : Z, (a | m) → (a | n) → (a | m * x + n * y).
Proof.
intros.
unfold divide in *.
destruct H, H0.
rewrite H.
rewrite H0.
rewrite M1.
rewrite M2.
rewrite <-(M2 x1).
rewrite (M1 a).
rewrite (M2 x1).
rewrite <-D1.
exists (x * x0 + x1 * y).
congruence.
Qed.

Theorem A2P2: ∀ a b c : Z, (a | b) → (b | c) → (a | c).
Proof.
intros.
unfold divide in *.
destruct H, H0.
rewrite H0.
rewrite H.
rewrite M2.
exists (x0 * x).
congruence.
Qed.

Theorem A2P3 : ∀ a b : Z, a < b ∨ a = b ∨ a > b.
Proof.
intros.
pose proof (T (b + -a)).
unfold lt.
destruct H.
destruct H.
destruct H0.
left.
unfold sub.
exact H.
destruct H.
destruct H.
destruct H0.
apply (S1 _ _ a) in H0.
rewrite <-A2 in H0.
rewrite A1P2 in H0.
rewrite A3, A1P1 in H0.
right.
left.
congruence.
destruct H.
destruct H0.
right.
right.
rewrite <-A1P7 in H1.
rewrite M1, D1 in H1.
rewrite M1, A1P7 in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
unfold sub.
rewrite A1.
exact H1.
Qed.

Theorem A2P4 : ∀ a b c : Z, a < b → c > 0 → a * c < b * c.
Proof.
intros.
unfold lt.
unfold sub.
rewrite <-A1P7.
rewrite M2.
rewrite A1P7.
rewrite <-D1.
unfold lt in *.
unfold sub in *.
rewrite <-A1P7 in H0.
rewrite M1, A1P6 in H0.
rewrite A3 in H0.
pose proof (N3 (b + -a) c).
apply H1 in H.
exact H.
exact H0.
Qed.

Theorem A2P5 : ∀ a b c : Z, a * c = b * c → c ≠ 0 → a = b.
Proof.
intros.
apply S3 in H.
destruct H.
exact H.
contradiction.
Qed.

Theorem A3P1 : 0 ≠ 1.
Proof.
unfold not.
intros.
pose proof (T 1).
destruct H0.
destruct H0.
destruct H1.
symmetry in H.
contradiction.
destruct H0.
destruct H0.
destruct H0.
pose proof N1.
exact H0.
destruct H0.
destruct H1.
destruct H0.
pose proof N1.
exact H0.
Qed.

Lemma T1: forall a : Z, a ∈ ℕ \/ a = 0 \/ -a ∈ ℕ.
intros.
pose proof (T a).
destruct H.
destruct H.
left.
exact H.
destruct H.
destruct H.
destruct H0.
right.
left.
trivial.
destruct H.
destruct H0.
right.
right.
trivial.
Qed.

Theorem A3P2 : ∀ a b : Z, 0 < a → (0 < b ↔ 0 < a * b).
Proof.
intros.
split.
intros.
pose proof (N3 a b).
rewrite N_gt_0 in H1.
unfold In in H1.
apply H1 in H.
exact H.
exact H0.
intros.
unfold lt, sub in *.
rewrite <-A1P7 in *.
rewrite M1, A1P6 in *.
rewrite (M1 (-1)), A1P6 in H0.
rewrite A3 in *.
pose proof (T1 b).
destruct H1.
exact H1.
destruct H1.
rewrite H1 in H0.
rewrite A1P6 in H0.
pose proof N0.
contradiction.
pose proof (N3 a (-b)).
apply H2 in H.
rewrite M1 in H.
apply N4 in H0.
rewrite <-A1P7 in H0.
rewrite M2 in H0.
rewrite A1P7 in H0.
contradiction.
exact H1.
Qed.

Lemma ltoreq_gt : forall a b : Z, a ≤ b -> ¬ a > b.
Proof.
intros.
unfold not.
intros.
apply O8 in H0.
contradiction.
Qed.

Theorem greater_or_less_than : forall a b : Z, a ≠ b -> a > b \/ a < b.
intros.
unfold lt, sub in *.
pose proof (T1 (a + -b)).
destruct H0.
left.
exact H0.
destruct H0.
apply (S1 _ _ b) in H0.
rewrite <-A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0.
rewrite A1, A3 in H0.
contradiction.
rewrite <-A1P7 in H0.
rewrite M1, D1 in H0.
rewrite M1, A1P7 in H0.
rewrite M1, A1P7, A1P5 in H0.
right.
rewrite A1.
exact H0.
Qed.

Theorem A3P3 : ∀ a : Z, 0 < a → a < 1 → False.
Proof.
intros.
destruct (WOP {x : Z | 0 < x < 1}).
exists a.
tauto.
intros.
destruct H1.
rewrite N_gt_0.
unfold In.
exact H1.
destruct H1.
pose proof (H2 (x * x)).
assert (x > x * x).
destruct H1.
apply (A2P4 x 1 x) in H4.
rewrite (M1 1), M3 in H4.
exact H4.
exact H1.
apply ltoreq_gt in H3.
contradiction.
destruct H1.
split.
apply (A2P4 0 x x) in H1.
rewrite A1P6 in H1.
exact H1.
exact H1.
eauto using O3.
Qed.

Lemma negative_zero_equals_zero : -0 = 0.
Proof.
intros.
rewrite <-A1P7.
rewrite M1.
rewrite A1P6.
reflexivity.
Qed.

Lemma zero_not_lt_zero : ¬ 0 < 0.
Proof.
unfold not.
unfold lt.
intros.
unfold sub in H.
rewrite A4 in H.
pose proof N0.
contradiction.
Qed.

Lemma inequality_O2: forall a b c : Z, a ≠ b -> a + c ≠ b + c.
Proof.
intros.
unfold not in *.
contradict H.
apply (S1 _ _ (-c)) in H.
rewrite <-A2, A4 in H.
rewrite <-A2, A4 in H.
rewrite A3 in *.
rewrite A3 in H.
exact H.
Qed.

Theorem multiplication_inequality: forall a b c: Z, a ≠ b -> c ≠ 0 -> a * c ≠  b * c.
Proof.
intros.
unfold not.
intros.
apply S3 in H1.
destruct H1.
contradiction.
contradiction.
Qed.

Theorem a_times_b_not_zero : forall a b : Z, a * b ≠ 0 -> a ≠ 0 /\ b ≠ 0.
Proof.
intros.
split.
contradict H.
apply (S2 _ _ b) in H.
rewrite A1P6 in H.
exact H.
contradict H.
apply (S2 _ _ a) in H.
rewrite A1P6 in H.
rewrite M1.
exact H.
Qed.

Lemma inverse_inequality : forall a b : Z, a ≠ b -> b ≠ a.
Proof.
intros.
unfold not.
intros.
symmetry in H0.
contradiction.
Qed.

Theorem A3P4 : ∀ a b : Z, (a | b) → b > 0 → a ≤ b.
Proof.
intros.
pose proof (A2P3 a 0).
destruct H1.
left.
pose proof (O3 a 0 b).
apply H2 in H0.
exact H0.
exact H1.
destruct H1.
rewrite <-H1 in H0.
left.
exact H0.
destruct H.
pose proof (A2P3 x 0).
destruct H2.
rewrite H in H0.
unfold lt, sub in *.
rewrite negative_zero_equals_zero in *.
rewrite A3 in *.
rewrite A1, A3 in H2.
pose proof (N3 (-x) a).
apply H3 in H2.
apply N4 in H0.
rewrite <-A1P7, M2, A1P7 in H0.
contradiction.
exact H1.
destruct H2.
rewrite H2 in H.
rewrite A1P6 in H.
rewrite H in H0.
pose proof zero_not_lt_zero.
contradiction.
pose proof (A2P3 x 1).
destruct H3.
pose proof (A3P3 x).
tauto.
destruct H3.
rewrite H3 in H.
rewrite M1, M3 in H.
right.
congruence.
rewrite H.
pose proof (A2P4 1 x a).
apply H4 in H3.
rewrite M1, M3 in H3.
left.
exact H3.
congruence.
Qed.

Theorem reverse_N3 : forall a b : Z, a > 0 -> a * b > 0 -> b > 0.
Proof.
intros.
pose proof (T1 (-b)).
destruct H1.
pose proof (N3 (-b) a).
rewrite N_gt_0 in *.
unfold In in *.
apply H2 in H.
rewrite M1 in H.
rewrite <-A1P7 in H.
rewrite M2 in H.
rewrite (M1 a) in H.
rewrite A1P7 in H.
unfold lt, sub in H, H0.
rewrite negative_zero_equals_zero, A3 in H, H0.
apply N4 in H0.
rewrite <-A1P7 in H0.
rewrite M2 in H0.
rewrite A1P7 in H0.
contradiction.
pose proof H2.
exact H1.
unfold lt, sub.
rewrite negative_zero_equals_zero, A3.
unfold lt, sub in *.
rewrite negative_zero_equals_zero, A3 in *.
destruct H1.
apply (S2 _ _ (-1)) in H1.
rewrite A1P8 in H1.
rewrite M3, A1P6 in H1.
rewrite H1 in H0.
rewrite M1, A1P6 in H0.
pose proof N0.
contradiction.
rewrite A1P5 in H1.
exact H1.
Qed.

Lemma a_and_b_nat : forall a b : Z, a * b > 0 -> (a > 0 /\ b > 0) \/ (a < 0 /\ b < 0).
Proof.
intros.
unfold lt, sub in *.
rewrite negative_zero_equals_zero in *.
rewrite A3 in *.
rewrite A3 in *.
rewrite A1, A3 in *.
rewrite A1, A3 in *.
pose proof (T1 (-a)).
destruct H0.
right.
split.
exact H0.
pose proof (reverse_N3 (-a) (-b)).
unfold lt, sub in *.
rewrite negative_zero_equals_zero in *.
rewrite A3 in *.
rewrite A3 in *.
rewrite A3 in *.
rewrite A1P8 in H1.
apply H1 in H0.
exact H0.
exact H.
destruct H0.
apply (S2 _ _ (-1)) in H0.
rewrite A1P8, A1P6 in H0.
rewrite M3 in H0.
rewrite H0 in H.
rewrite A1P6 in *.
pose proof N0.
contradiction.
left.
split.
rewrite A1P5 in H0.
exact H0.
pose proof (reverse_N3 a b).
unfold lt, sub in *.
rewrite negative_zero_equals_zero in *.
rewrite A3 in *.
rewrite A3 in *.
rewrite A3 in *.
rewrite A1P5 in H0.
apply H1 in H0.
exact H0.
exact H.
Qed.

Lemma zero_lt_one : 0 < 1.
Proof.
intros.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
pose proof N1.
exact H.
Qed.


Lemma le_lt_opp : ∀ a b : Z, a ≤ b ↔ ¬ b < a.
Proof.
intros.
unfold le, lt, sub.
split.
intros.
destruct H.
rewrite A1 in H.
apply N4 in H.
rewrite <-A1P7 in H.
rewrite M1, D1 in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite M1, A1P7 in H.
exact H.
rewrite H.
rewrite A4.
pose proof N0.
exact H0.
intros.
pose proof (T1 (a + -b)).
destruct H0.
contradiction.
destruct H0.
apply (S1 _ _ b) in H0.
rewrite <-A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0.
rewrite A1, A3 in H0.
right.
exact H0.
rewrite <-A1P7, M1, D1 in H0.
rewrite M1, A1P7 in H0.
rewrite M1, A1P7, A1P5 in H0.
left.
rewrite A1.
trivial.
Qed.


Theorem a_times_b_equals_1 :
  ∀ a b : Z, a * b = 1 → (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1).
Proof.
intros.
pose proof (a_and_b_nat a b).
destruct H0.
destruct (classic(a=1)).
rewrite H.
pose proof zero_lt_one.
exact H1.
rewrite H.
pose proof zero_lt_one.
exact H1.
destruct H0.
destruct (classic (a=1)).
rewrite H2 in H.
rewrite M1, M3 in H.
left.
split.
exact H2.
exact H.
destruct (classic(b=1)).
rewrite H3 in H.
rewrite M3 in H.
left.
split.
exact H.
exact H3.
pose proof (A2P3 a 1).
destruct H4.
pose proof (A3P3 a).
destruct H5.
exact H0.
exact H4.
destruct H4.
contradiction.
pose proof (A2P3 b 1).
destruct H5.
pose proof (A3P3 b).
destruct H6.
exact H1.
exact H5.
destruct H5.
contradiction.
apply (A2P4 1 a b) in H4.
rewrite M1, M3 in H4.
rewrite H in H4.
pose proof (le_lt_opp b 1).
destruct H6.
unfold le in *.
destruct H6.
left.
exact H4.
exact H5.
exact H1.
destruct H0.
destruct (classic (a=(-1))).
rewrite H2 in H.
apply (S2 _ _ (-1)) in H.
rewrite <-M2 in H.
rewrite M1 in H.
rewrite <-M2 in H.
rewrite M1 in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite M1, M3 in H.
rewrite M1, M3 in H.
right.
split.
exact H2.
exact H.
destruct (classic (b = (-1))).
rewrite H3 in H.
apply (S2 _ _ (-1)) in H.
rewrite <-M2 in H.
rewrite M1 in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite M1, M3 in H.
rewrite M1, M3 in H.
right.
split.
exact H.
exact H3.
pose proof (A2P3 a (-1)).
destruct H4.
pose proof (A2P3 b (-1)).
destruct H5.
apply (A2P4 a (-1) (-b)) in H4.
rewrite M1 in H4.
rewrite <-A1P7 in H4 at 1.
rewrite <-M2 in H4.
rewrite M1 in H.
rewrite H in H4.
rewrite M3 in H4.
rewrite A1P8 in H4.
rewrite M1, M3 in H4.
pose proof (le_lt_opp (-1) b).
destruct H6.
unfold le in *.
destruct H7.
destruct H6.
left.
exact H4.
exact H5.
destruct H6.
left.
exact H7.
exact H5.
right.
split.
rewrite <-H7 in H.
apply (S2 _ _ (-1)) in H.
rewrite <-M2, M1 in H.
rewrite <-M2, M1 in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite M1, M3 in H.
rewrite M1, M3 in H.
exact H.
congruence.
apply (O1 _ _ (-b)) in H1.
rewrite A4 in H1.
rewrite A1, A3 in H1.
exact H1.
destruct H5.
contradiction.
pose proof (A3P3 (b + 1)).
apply (O1 (-1) b 1) in H5.
rewrite A1, A4 in H5.
apply (O1 b 0 1) in H1.
rewrite (A1 0), A3 in H1.
destruct H6.
exact H5.
exact H1.
destruct H4.
contradiction.
pose proof (A3P3 (a + 1)).
apply (O1 (-1) a 1) in H4.
rewrite A1, A4 in H4.
apply (O1 a 0 1) in H0.
rewrite (A1 0), A3 in H0.
destruct H5.
exact H4.
exact H0.
Qed.

Theorem A3P5 : ∀ a b : Z, a ~ b → a = ± b.
Proof.
intros.
unfold assoc, pm in *.
unfold divide in *.
destruct H.
destruct H, H0.
rewrite H0 in H.
rewrite M2 in H.
rewrite <-(M3 b), M1 in H at 1.
apply S3 in H.
destruct H.
symmetry in H.
apply a_times_b_equals_1 in H.
destruct H.
destruct H.
rewrite H1 in H0.
rewrite M1,  M3 in H0.
left.
exact H0.
destruct H.
rewrite H1 in H0.
rewrite A1P7 in H0.
right.
exact H0.
rewrite H in *.
left.
rewrite M1, A1P6 in H0.
exact H0.
Qed.

Theorem A4P1 : ∀ a : Z, a ∈ unit ↔ a = ± 1.
Proof.
intros.
unfold unit, pm.
unfold In.
split.
intros.
unfold divide in H.
destruct H.
symmetry in H.
apply a_times_b_equals_1 in H.
destruct H.
destruct H.
left.
trivial.
destruct H.
right.
trivial.
intros.
unfold divide.
destruct H.
exists 1.
rewrite M1, M3.
congruence.
exists (-1).
apply (S2 _ _ (-1)) in H.
rewrite M1 in H.
rewrite A1P8 in H.
rewrite M3 in H.
congruence.
Qed.

Lemma one_unit : 1 ∈ unit.
Proof.
unfold In, unit.
unfold divide.
exists 1.
rewrite M3.
congruence.
Qed.

Lemma negative_one_unit : -1 ∈ unit.
Proof.
unfold In, unit, divide.
exists (-1).
rewrite A1P8.
rewrite M3.
congruence.
Qed.

Theorem A4P2 : ∀ a b : Z, a ~ b ↔ ∃ u : Z, u ∈ unit ∧ b = a * u.
Proof.
intros.
split.
intros.
unfold In, unit.
apply A3P5 in H.
unfold pm in H.
unfold divide.
destruct H.
exists 1.
split.
exists 1.
rewrite M3.
reflexivity.
rewrite M3.
congruence.
exists (-1).
split.
exists (-1).
rewrite A1P8.
rewrite M3.
congruence.
apply (S2 _ _ (-1)) in H.
rewrite A1P8 in H.
rewrite M3 in H.
congruence.
intros.
destruct H.
destruct H.
unfold In, unit in H.
unfold assoc.
split.
unfold divide.
exists x.
rewrite M1.
congruence.
unfold divide.
unfold divide in H.
destruct H.
symmetry in H.
apply a_times_b_equals_1 in H.
destruct H.
destruct H.
rewrite H1 in H0.
rewrite M3 in H0.
exists 1.
rewrite A1P3.
congruence.
destruct H.
rewrite H1 in H0.
apply (S2 _ _ (-1)) in H0.
rewrite <-M2, A1P8 in H0.
rewrite M3 in H0.
rewrite M3 in H0.
rewrite M1 in H0.
exists (-1).
congruence.
Qed.

Lemma one_ne_zero : 1 ≠ 0.
unfold not.
intros.
pose proof N1.
pose proof N0.
rewrite H in H0.
contradiction.
Qed.


Lemma two_natural : 2 ∈ ℕ.
Proof.
apply N2.
pose proof N1.
trivial.
pose proof N1.
trivial.
Qed.

Lemma A3P3_plus1 : forall a : Z, 1 < a -> a < 2 -> False.
Proof.
intros.
apply (O1 _ _ (-1)) in H.
rewrite A4 in H.
apply (O1 _ _ (-1)) in H0.
rewrite <-A2 in H0.
rewrite A4 in H0.
rewrite A3 in H0.
pose proof (A3P3 (a + -1)).
tauto.
Qed.

Theorem lt_opp : forall a b : Z, a > b -> -b > -a.
Proof.
intros.
unfold lt, sub in *.
rewrite A1P5.
rewrite A1.
trivial.
Qed.

Theorem neg_pos_div : forall a b : Z, (a | b) -> (-a | b).
Proof.
intros.
unfold divide in *.
destruct H.
exists (-x).
rewrite A1P8.
trivial.
Qed.

Theorem pos_neg_div : forall a b :Z,  (a | b) -> (a | -b).
intros.
unfold divide in *.
destruct H.
apply (S2 _ _ (-1)) in H.
rewrite M1, A1P7 in H.
rewrite <-M2 in H.
rewrite (M1 a) in H.
rewrite M2 in H.
rewrite (M1 x) in H.
rewrite A1P7 in H.
exists (-x).
congruence.
Qed.

Theorem A4P3 : 2 ∈ prime.
Proof.
unfold prime, In.
split.
unfold not.
intros.
unfold pm in H.
destruct H.
apply (S1 _ _ (-1)) in H.
rewrite A4 in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A3 in H.
pose proof one_ne_zero.
contradiction.
pose proof (N2 2 1).
pose proof N1.
apply (S1 _ _ 1) in H.
rewrite (A1 (-1)), A4 in H.
apply H0 in H1.
rewrite H in H1.
pose proof N0.
contradiction.
pose proof (N2 1 1).
apply H2 in H1.
exact H1.
exact H1.
assert (forall d : Z, d ∈ ℕ -> (d | 2) -> d = ± 1 ∨ d = ± 2).
intros.
pose proof (A2P3 d 2).
destruct H1.
pose proof (A2P3 d 1).
destruct H2.
rewrite N_gt_0 in H.
unfold In in H.
pose proof (A3P3 d).
tauto.
destruct H2.
left.
unfold pm.
left.
congruence.
pose proof (A3P3_plus1 d).
tauto.
destruct H1.
right.
unfold pm.
left.
trivial.
apply A3P4 in H0.
unfold le in H0.
destruct H0.
apply O8 in H1.
unfold le in H1.
destruct H1.
left.
exact H0.
right.
unfold pm.
left.
exact H0.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
apply N2.
pose proof N1.
trivial.
pose proof N1.
trivial.
intros.
pose proof (A2P3 d 0).
destruct H1.
apply lt_opp in H1.
rewrite negative_zero_equals_zero in H1.
apply H in H1.
apply neg_pos_div in H0.
unfold sub in H1.
rewrite negative_zero_equals_zero in *.
rewrite A3 in H1.
destruct H1.
left.
unfold pm in *.
destruct H1.
right.
rewrite <-A1P7 in H1.
apply (S2 _ _ (-1)) in H1.
rewrite <-M2 in H1.
rewrite M1 in H1.
rewrite <-M2 in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
rewrite M3 in H1.
rewrite M1, A1P7 in H1.
exact H1.
left.
apply (S2 _ _ (-1)) in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
exact H1.
right.
unfold pm in *.
destruct H1.
right.
rewrite <-A1P7 in H1.
apply (S2 _ _ (-1)) in H1.
rewrite <-M2 in H1.
rewrite M1 in H1.
rewrite <-M2 in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
rewrite M3 in H1.
rewrite M1 in H1.
rewrite A1P7 in H1.
exact H1.
left.
apply (S2 _ _ (-1)) in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
rewrite <-A1P7 in H1.
rewrite M1 in H1.
rewrite M2 in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
rewrite M1, M3 in H1.
exact H1.
apply neg_pos_div in H0.
unfold sub.
rewrite negative_zero_equals_zero.
rewrite A3.
exact H0.
destruct H1.
pose proof two_natural.
rewrite H1 in H0.
unfold divide in H0.
destruct H0.
rewrite M1, A1P6 in H0.
pose proof two_natural.
rewrite H0 in H3.
pose proof N0.
contradiction.
apply H in H1.
unfold sub in *.
rewrite negative_zero_equals_zero in *.
rewrite A3 in *.
exact H1.
unfold sub.
rewrite negative_zero_equals_zero in *.
rewrite A3.
exact H0.
Qed.

Lemma not_not : forall a b : Prop,  ¬ (a /\ b) -> ¬ a \/ ¬ b.
Proof.
intros.
tauto.
Qed.

Theorem inequality_minus1 : forall a b : Z,  a > b -> a > b - 1.
Proof.
intros.
unfold sub.
unfold lt, sub in *.
pose proof N1.
rewrite <-A1P7.
rewrite M1, D1.
rewrite A1P7.
rewrite A1P5.
rewrite M1, A1P7.
rewrite A2.
apply N2.
exact H.
exact H0.
Qed.

Theorem negative_inside : forall a b : Z, - (a * b) = -a * b.
Proof.
intros.
rewrite <-A1P7.
rewrite M2.
rewrite A1P7.
reflexivity.
Qed.

Theorem A4P4 :
  ∀ p : Z, 1 < p → p ∉ prime → ∃ n, 1 < n < p ∧ (n | p).
Proof.
intros.
unfold In, prime in H0.
apply not_not in H0.
destruct H0.
apply NNPP in H0.
unfold pm in H0.
destruct H0.
rewrite H0 in H.
unfold lt, sub in H.
rewrite A4 in H.
pose proof N0.
contradiction.
rewrite H0 in H.
unfold lt, sub in H.
rewrite <-A1P7 in H.
rewrite M1 in H.
rewrite <-D1 in H.
rewrite M1 in H.
rewrite A1P7 in H.
pose proof two_natural.
apply N4 in H1.
contradiction.
apply NNPP.
contradict H0.
intros d H1.
apply NNPP.
contradict H0.
assert (d > 1 \/ d < (-1)).
apply not_or_and in H0.
destruct H0.
apply not_or_and in H0.
apply not_or_and in H2.
pose proof (A2P3 d 0).
pose proof (A2P3 d (-1)).
destruct H3, H4.
tauto.
destruct H4.
tauto.
pose proof (A3P3 (d+1)).
apply (O1 _ _ 1) in H3.
apply (O1 _ _ 1) in H4.
rewrite A1, A4 in H4.
rewrite (A1 0), A3 in H3.
tauto.
destruct H3.
rewrite H3 in H1.
unfold divide in H1.
destruct H1.
rewrite M1, A1P6 in H1.
rewrite H1 in H.
unfold lt, sub in H.
rewrite A1, A3 in H.
pose proof N1.
apply N4 in H5.
contradiction.
right.
exact H4.
destruct H3, H4.
tauto.
rewrite H3 in H1.
unfold divide in H1.
destruct H1.
rewrite M1, A1P6 in H1.
rewrite H1 in H.
unfold lt, sub in H.
rewrite A1, A3 in H.
pose proof N1.
apply N4 in H5.
contradiction.
tauto.
pose proof (A2P3 d 1).
destruct H5.
pose proof (A3P3 d).
tauto.
destruct H5.
tauto.
left.
trivial.
destruct H2.
apply not_or_and in H0.
destruct H0.
apply not_or_and in H0.
apply not_or_and in H3.
destruct H0, H3.
exists d.
split.
apply A3P4 in H1.
unfold le in H1.
tauto.
pose proof N1.
pose proof (inequality_minus1 p 1).
unfold sub in H7.
rewrite A4 in H7.
apply H7.
exact H.
exact H1.
exists (-d).
split.
apply neg_pos_div in H1.
apply A3P4 in H1.
unfold le in H1.
apply not_or_and in H0.
destruct H0.
apply not_or_and in H0.
apply not_or_and in H3.
destruct H0, H3.
destruct H1.
apply lt_opp in H2.
rewrite A1P5 in H2.
tauto.
apply (S2 _ _ (-1)) in H1.
rewrite A1P8 in H1.
rewrite M3 in H1.
rewrite M1, A1P7 in H1.
contradiction.
apply lt_opp in H2.
rewrite A1P5 in H2.
pose proof (inequality_minus1 p 1).
unfold sub in H3.
rewrite A4 in H3.
apply H3.
exact H.
apply neg_pos_div.
exact H1.
Qed.

Theorem A4P5 :∀ a b : Z,
    0 < a → 0 < b → (∃ q r : Z, a = b * q + r ∧ 0 ≤ r < b).
intros.
set (S := {r : Z |∃ q : Z, a - b * q = r /\ 0 ≤ r}).
destruct(classic (b|a)).
destruct H1.
exists x, 0.
split.
rewrite A3, M1.
exact H1.
unfold le.
split.
right.
congruence.
exact H0.
assert (S ≠ ∅).
unfold S, not.
intros.
assert (a ∈ ∅).
rewrite <-H2.
unfold In.
exists 0.
rewrite M1, A1P6.
unfold sub.
rewrite negative_zero_equals_zero.
split.
rewrite A3.
congruence.
unfold le.
left.
exact H.
destruct H3.
assert (S ⊂ ℕ).
unfold Included.
intros.
unfold S in H3.
destruct H3.
destruct H3.
unfold le in H4.
destruct H4.
unfold lt, sub in H4.
rewrite negative_zero_equals_zero, A3 in H4.
exact H4.
rewrite <-H4 in H3.
unfold sub in H3.
apply (S1 _ _ (b*x0)) in H3.
rewrite <-A2, (A1 (-(b*x0))), A4, A3, A1, A3 in H3.
destruct H1.
rewrite M1 in H3.
exists x0.
exact H3.
pose proof Well_Ordering_Principle S H2 H3.
destruct H4.
destruct H4.
assert (a ∈ S).
unfold S.
exists 0.
rewrite M1, A1P6.
unfold sub.
rewrite negative_zero_equals_zero.
rewrite A3.
split.
congruence.
unfold le.
left.
exact H.
destruct (classic (b ≤ x)).
unfold In, S in H4.
destruct H4.
destruct H4.
pose proof (H5 (x-b)).
assert ((x-b)∈ S).
unfold In, S.
exists (x0+1).
split.
rewrite M1, D1.
unfold sub.
rewrite M1, <-A1P7, M1, D1, (M1 (b*x0)), A1P7, (M1 1), M3, (M1 b (-1)),A1P7, A2.
unfold sub in H4.
rewrite H4.
congruence.
unfold le in *.
destruct H7.
apply (O1 _ _ (-b)) in H7.
rewrite A4 in H7.
unfold sub.
left.
exact H7.
apply (S1 _ _ (-b)) in H7.
rewrite A4 in H7.
unfold sub.
right.
exact H7.
apply H9 in H10.
unfold le in *.
destruct H7, H10.
apply lt_opp in H0.
rewrite negative_zero_equals_zero in H0.
apply (O1 _ _ x) in H0.
rewrite A1, A1P1 in H0.
unfold sub in H10.
apply (O3 (x+-b) x (x+-b)) in H0.
apply O7 in H0.
contradiction.
exact H10.
apply lt_opp in H0.
rewrite negative_zero_equals_zero in H0.
apply (O1 _ _ x) in H0.
rewrite A1P1, A1 in H0.
apply O7 in H0.
unfold sub in H10.
symmetry in H10.
contradiction.
rewrite H7 in H10.
unfold sub in H10.
rewrite A4 in H10.
unfold le in H8.
destruct H8.
pose proof (O3 0 x 0).
apply H11 in H8.
apply O7 in H8.
contradiction.
exact H10.
apply O7 in H8.
contradiction.
apply O7 in H10.
symmetry in H8.
contradiction.
apply lt_opp in H0.
rewrite negative_zero_equals_zero in H0.
apply (O1 _ _ x) in H0.
rewrite A1P1, A1 in H0.
apply O7 in H0.
unfold sub in H10.
symmetry in H10.
contradiction.
unfold In,S in H4.
destruct H4.
exists x0, x.
split.
destruct H4.
unfold sub in H4.
apply (S1 _ _ (b * x0)) in H4.
rewrite <-A2, (A1 (-(b * x0))), A4, A3, A1 in H4.
exact H4.
unfold le.
split.
destruct H4.
unfold le in H8.
destruct H8.
left.
trivial.
right.
trivial.
pose proof (A2P3 x b).
destruct H8.
trivial.
destruct H8.
unfold le, not in H7.
destruct H7.
right.
symmetry.
trivial.
unfold not, le in H7.
destruct H7.
left.
trivial.
Qed.

(** Midterm problems. **)

Theorem P1 : ∀ a b : Z, -(a-b) = b-a.
Proof.
intros.
rewrite <-A1P7.
unfold sub.
rewrite M1, D1.
rewrite M1, A1P7.
rewrite A1P8.
rewrite M3.
rewrite A1.
reflexivity.
Qed.

Theorem P2 : ∀ a : Z, -(-a) = a.
Proof.
intros.
rewrite A1P5.
reflexivity.
Qed.

Theorem P3 : ∀ a b : Z, (-a) * b = -(a * b).
Proof.
intros.
rewrite negative_inside.
reflexivity.
Qed.


Theorem P4 : ∀ a b : Z, a < b ∨ a = b ∨ a > b.
Proof.
intros.
pose proof (A2P3 a b).
exact H.
Qed.

Theorem P5 : ∀ a b c : Z, a < b → c < 0 → a * c > b * c.
Proof.
intros.
unfold lt in *.
unfold sub in *.
rewrite A1, A3 in H0.
pose proof (N3 (b + -a) (-c)).
apply H1 in H.
rewrite D1 in H.
rewrite A1P8 in H.
rewrite (M1 b).
rewrite M1 in H.
rewrite negative_inside.
rewrite A1.
exact H.
exact H0.
Qed.

Theorem P6 : ∀ a b c : Z, a < b → c > 0 ↔ a * c < b * c.
Proof.
intros.
split.
intros.
unfold lt, sub in *.
rewrite negative_zero_equals_zero in H0.
rewrite A3 in H0.
pose proof (N3 (b + -a) c).
apply H1 in H.
rewrite D1 in H.
rewrite negative_inside.
exact H.
trivial.
intros.
pose proof (A2P3 c 0).
destruct H1.
pose proof (P5 a b c).
apply H2 in H.
apply O8 in H0.
destruct H0.
unfold le.
left.
exact H.
exact H1.
destruct H1.
rewrite H1 in H0.
rewrite M1, A1P6 in H0.
rewrite M1, A1P6 in H0.
pose proof zero_not_lt_zero.
contradiction.
exact H1.
Qed.

Theorem P7 : ∀ a b c : Z, a ≠ 0 → a * b = a * c → b = c.
Proof.
intros.
pose proof (A2P5 b c a).
rewrite M1 in H0.
rewrite (M1 a) in H0.
apply H1 in H0.
exact H0.
trivial.
Qed.

Theorem P8 : ∀ a b : Z, 0 < a → 0 < a*b → 0 < b.
Proof.
pose proof reverse_N3.
exact H.
Qed.

Theorem P9 : ∀ n : Z, -n < 0 ↔ 0 < n.
Proof.
intros.
split.
intros.
pose proof (lt_opp 0 (-n)).
apply H0 in H.
rewrite negative_zero_equals_zero in H.
rewrite A1P5 in H.
exact H.
intros.
apply lt_opp in H.
rewrite negative_zero_equals_zero in H.
exact H.
Qed.

Theorem P10 : ∀ a : Z, ¬ (0 < a < 1).
Proof.
intros.
unfold not.
intros.
pose proof (A3P3 a).
tauto.
Qed.

Theorem P11 : ∀ a b : Z, ¬ (a < b < a+1).
Proof.
intros.
unfold not.
intros.
pose proof (P10 (b - a)).
destruct H.
apply (O1 _ _ (-a)) in H.
rewrite A4 in H.
apply (O1 _ _ (-a)) in H1.
rewrite <-A2 in H1.
rewrite (A1 1) in H1.
rewrite A2 in H1.
rewrite A4 in H1.
rewrite (A1 0) ,A3 in H1.
unfold sub in H0.
tauto.
Qed.

Theorem P12 : ∀ n m : Z, n < m+1 ↔ n ≤ m.
Proof.
intros.
split.
intros.
pose proof (A2P3 n m).
destruct H0. 
unfold le.
left.
trivial.
destruct H0.
unfold le.
right.
trivial.
pose proof (P11 m n).
tauto.
intros.
unfold le in H.
destruct H.
apply inequality_minus1 in H.
apply (O1 _ _ 1) in H.
unfold sub in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
exact H.
rewrite H.
pose proof (O4 m).
exact H0.
Qed. 

Theorem P13 : ∀ a b : Z, b > 0 → (a | b) → a ≤ b.
Proof.
intros.
apply A3P4.
exact H0.
exact H.
Qed.

Theorem P14 : ∀ a b c : Z, a ~ b → b ~ c → a ~ c.
Proof.
intros.
unfold assoc in *.
split.
destruct H, H0.
destruct H, H1, H0, H2.
unfold divide.
rewrite H in H0.
rewrite M2 in H0.
exists (x1 * x).
trivial.
destruct H, H0.
destruct H, H1, H0, H2.
unfold divide.
rewrite H2 in H1.
rewrite M2 in H1.
exists (x0 * x2).
exact H1.
Qed.

Theorem P15 : ∀ u : Z, u ∈ unit → u = ± 1.
Proof.
intros.
apply A4P1 in H.
exact H.
Qed.

Theorem P16 : 0 ∉ prime.
Proof.
unfold not.
unfold prime.
unfold In.
intros.
destruct H.
pose proof (H0 2).
destruct H1.
contradict H.
Admitted.

Theorem P17 : ∀ p : Z, p ∈ prime → ∀ d : Z, (d | p) → d ~ 1 ∨ d ~ p.
Proof.
intros.
unfold prime, In in H.
destruct H.
apply H1 in H0.
unfold assoc.
destruct H0.
left.
split.
unfold divide.
unfold pm in H0.
destruct H0.
exists 1.
rewrite M1, M3.
congruence.
exists (-1).
apply (S2 _ _ (-1)) in H0.
rewrite M1, A1P7 in H0.
rewrite A1P8 in H0.
rewrite M3 in H0.
rewrite A1P7.
congruence.
unfold divide.
unfold pm in H0.
destruct H0.
exists 1.
rewrite M3.
trivial.
exists (-1).
rewrite A1P7.
trivial.
right.
split.
unfold divide.
unfold pm in H0.
destruct H0.
exists 1.
rewrite M1, M3.
congruence.
exists (-1).
apply (S2 _ _ (-1)) in H0.
rewrite A1P8 in H0.
rewrite M1 in H0.
rewrite M3 in H0.
congruence.
unfold divide.
unfold pm in H0.
destruct H0.
exists 1.
rewrite M1, M3.
trivial.
exists (-1).
rewrite A1P7.
trivial.
Qed.

Theorem P18 : ∀ p x : Z,
    0 < p → 0 < x → p ∈ prime → (p | x) → ∃ k : Z, k*p = x ∧ 0 < k < x.
Proof.
intros.
unfold In, prime in H1.
destruct H1.
unfold divide in H2.
destruct H2.
exists x0.
split.
congruence.
split.
rewrite H2 in H0.
Admitted.

Theorem P19 : ∀ p : Z, p ∈ prime → -p ∈ prime.
Proof.
intros.
unfold In, prime in *.
destruct H.
split.
unfold not.
intros.
unfold pm in H, H1.
destruct H.
destruct H1.
right.
apply (S2 _ _ (-1)) in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite M1, M3 in H.
exact H.
apply (S2 _ _ (-1)) in H.
rewrite A1P8 in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite M3 in H.
left.
trivial.
intros.
apply pos_neg_div in H1.
rewrite A1P5 in H1.
apply H0 in H1.
destruct H1.
left.
trivial.
right.
unfold pm in H1.
unfold pm.
destruct H1.
right.
rewrite A1P5.
exact H1.
left.
exact H1.
Qed.

Theorem P20 : ∀ a b : Z, b > 0 → ∃ q r : Z, a = b*q + r ∧ 0 ≤ r < b.
Proof.
intros.
pose proof (A2P3 a 0).
destruct H0.
pose proof (A4P5 (-a) b).
apply H1 in H.
destruct H.
destruct H.
destruct H.
destruct (classic (not (x0 = 0))).
exists (-x - 1), (b + -x0).
rewrite M1.
unfold sub.
rewrite D1.
rewrite A1P7.
apply (S2 _ _ (-1)) in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite D1 in H.
rewrite (M1 x0), A1P7 in H.
rewrite <-M2 in H.
rewrite (M1 x), A1P7 in H.
rewrite M1 in H.
rewrite <-A2.
rewrite (A2 (-b)).
rewrite A1P2.
rewrite (A1 0), A3.
split.
trivial.
split.
unfold le.
destruct H2.
apply (O1 _ _ (-x0)) in H4.
rewrite A4 in H4.
left.
trivial.
destruct H2.
unfold lt.
unfold le in H2.
destruct H2.
unfold sub.
rewrite <-A1P7.
rewrite M1.
rewrite D1.
rewrite (M1 b), A1P7.
rewrite A1P8.
rewrite M3.
rewrite A2.
rewrite A4.
rewrite A1, A3.
rewrite N_gt_0.
unfold In.
trivial.
symmetry in H2.
contradiction.
apply NNPP in H3.
exists (-x).
exists 0.
rewrite H3 in H.
rewrite A3 in H.
apply (S2 _ _ (-1)) in H.
rewrite A1P8 in H.
rewrite M3 in H.
rewrite A3.
rewrite <-M2 in H.
rewrite (M1 x), A1P7 in H.
split.
trivial.
split.
unfold le.
right.
congruence.
destruct H2.
rewrite H3 in H4.
trivial.
apply lt_opp in H0.
rewrite negative_zero_equals_zero in H0.
trivial.
destruct H0.
exists 0, 0.
rewrite H0.
rewrite M1, A1P6.
rewrite A3.
split.
congruence.
split.
unfold le.
right.
congruence.
trivial.
pose proof (A4P5 a b).
apply H1 in H.
trivial.
trivial.
Qed.

Theorem P21 : ∀ S : Ensemble Z,
    (∀ x : Z, (∀ y : Z, 0 < y < x → S y) → S x) → ∀ a : Z, S a.
Proof.
intros.
pose proof classic (¬ ({n : Z | (¬ (S n)) /\ n > 0} = ∅)).
destruct H0.
destruct (Well_Ordering_Principle {n : Z | (¬ (S n))/\n>0}).
trivial.
unfold Included.
intros.
unfold In in H1.
destruct H1.
unfold lt, sub in H2.
rewrite negative_zero_equals_zero in H2.
rewrite A3 in H2.
trivial.
destruct H1.
unfold In in H1, H2.
assert (∀ y : Z, 0 < y < x → S y).
intros.
pose proof classic (S y).
destruct H4.
trivial.
destruct H3.
destruct (H2 y).
split.
trivial.
trivial.
unfold lt, sub in H5, H6.
apply N4 in H5.
rewrite <-A1P7 in H5.
rewrite M1, D1 in H5.
rewrite M1, A1P7 in H5.
rewrite M1, A1P7, A1P5 in H5.
rewrite A1 in H5.
contradiction.
unfold lt, sub in H5.
apply (S1 x y (-y)) in H6.
rewrite A4 in H6.
rewrite H6 in H5.
pose proof N0.
contradiction.
apply H in H3.
destruct H1.
contradiction.
apply NNPP in H0.
pose proof classic (N a).
destruct H1.
apply NNPP.
unfold not at 1.
intros.
assert (a ∈ {n : Z | ¬ S n ∧ 0 < n}).
unfold In, lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
split.
trivial.
trivial.
rewrite H0 in H3.
contradiction.
pose proof H(a).
apply H.
intros.
destruct H3.
apply (O3 0 y a) in H3.
unfold lt, sub in H3.
rewrite negative_zero_equals_zero, A3 in H3.
contradiction.
trivial.
Qed.

Definition gcd (a b d : Z) :=
  (d | a) ∧ (d | b) ∧ ∀ x : Z, (x | a) → (x | b) → (x | d).

Notation "'gcd' ( a , b )  = d" := (gcd a b d) (at level 80).

Definition lcm (a b m : Z) := (a|m) ∧ (b|m) ∧ ∀ n : Z, (a|n) → (b|n) → (m|n).
Notation "'lcm' ( a , b )  = m" := (lcm a b m) (at level 80).

Theorem P22 : ∀ a b d m : Z, gcd (a,b) = d → lcm (a,b) = m → a * b = ± d * m.
Proof.
intros.
destruct H.
destruct H0.
destruct H1, H2.
pose proof (H3 d).
unfold pm.
pose proof (A2P2 d a m).
pose proof H.
pose proof (A2P2 d b m).
apply H6 in H.
unfold divide in H.
unfold divide in H2.
destruct H, H2.
left.
rewrite H2.
unfold divide in H7.
destruct H7.
rewrite H7.
apply H5 in H1.
unfold divide in H1.
destruct H1.
pose proof H1.
symmetry in H1.
rewrite M1 in H1.
apply A1P10 in H1.
destruct H1.
Admitted.

(** ASSIGNMENT 5 BEGINS HERE -- due Fri. October 11 **)

Lemma gcd_0 : forall a b : Z, a = 0 -> gcd (a , b) = b.
Proof.
intros.
rewrite H.
split.
unfold divide.
exists 0.
rewrite A1P6.
congruence.
split.
unfold divide.
exists 1.
rewrite M1, M3.
congruence.
intros.
trivial.
Qed.

Lemma gcd_1 : forall a b c: Z, gcd (a, b) = c -> gcd (b, a) = c.
Proof.
intros.
destruct H.
split.
destruct H0.
trivial.
split.
destruct H0.
trivial.
destruct H0.
intros.
pose proof (H1 x).
apply H4 in H3.
trivial.
trivial.
Qed.

Lemma equiv_gcd : ∀ a b c d: Z, gcd (a , b) = c -> gcd (a , b) = d -> c > 0 -> d > 0 -> c = d.
Proof.
intros.
destruct H, H0.
destruct H3, H4.
pose proof (H5 d).
apply H7 in H0.
pose proof (H6 c).
apply H8 in H.
pose proof (A3P5 c d).
unfold assoc in H9.
destruct H9.
split.
trivial.
trivial.
trivial.
rewrite H9 in H1.
apply lt_opp in H2.
rewrite negative_zero_equals_zero in H2.
unfold lt in H1, H2.
unfold sub in H2.
rewrite A1P5 in H2.
rewrite A1, A3 in H2.
unfold sub in H1.
rewrite negative_zero_equals_zero in H1.
rewrite A3 in H1.
apply N4 in H2.
contradiction.
trivial.
trivial. 
Qed.

Theorem A5P1 : ∀ a b : Z, gcd (a , b) = 1 → ∃ x y : Z, 1 = a * x + b * y.
Proof.
intros.
set (S:={c : Z | ∃ x y : Z, c = a * x + b * y /\ c > 0}).
destruct (classic (a | b)).
pose proof H.
destruct H.
destruct H2.
pose proof (H3 a).
destruct H4.
unfold divide.
exists 1.
rewrite M1, M3.
congruence.
exact H0.
exists x, 0.
rewrite (M1 b), A1P6.
rewrite A3.
rewrite M1.
congruence.
destruct (classic (b | a)).
pose proof H.
destruct H.
destruct H3.
pose proof (H4 b).
destruct H5.
trivial.
unfold divide.
exists 1.
rewrite M1, M3.
congruence.
exists 0, x.
rewrite M1, A1P6.
rewrite A1, A3.
rewrite M1.
congruence.
assert (S ≠ ∅).
unfold not.
intros.
pose proof (A2P3 a b).
destruct H3.
unfold lt in H3.
unfold S in H2.
assert (b - a ∈ ∅).
rewrite <-H2.
unfold In.
exists (-1), 1.
split.
rewrite M1, A1P7.
rewrite M3.
unfold sub.
rewrite A1.
congruence.
rewrite N_gt_0 in H3.
unfold In in H3.
trivial.
contradiction.
destruct H3.
destruct H0.
unfold divide.
exists 1.
rewrite M1, M3.
congruence.
assert (a - b ∈ ∅).
rewrite <-H2.
unfold S.
unfold In.
exists 1, (-1).
split.
rewrite M3.
rewrite M1, A1P7.
unfold sub.
congruence.
apply (O1 _ _ (-b)) in H3.
rewrite A4 in H3.
unfold sub.
trivial.
contradiction.
assert (S ⊂ ℕ).
unfold S.
unfold Included.
intros.
unfold In in H3.
destruct H3.
destruct H3.
destruct H3.
rewrite N_gt_0.
unfold In.
trivial.
pose proof (Well_Ordering_Principle S H2 H3).
destruct H4.
unfold S in H4.
destruct H4.
unfold In in H4.
unfold In in H5.
destruct H4.
destruct H4.
destruct H4.
pose proof (P20 a x).
apply H7 in H6.
destruct H6.
destruct H6.
destruct H6.
destruct H8.
destruct H8.
apply (S1 _ _ (- x * x2)) in H6.
rewrite <-A2 in H6.
rewrite (A1 x3) in H6.
rewrite A2 in H6.
rewrite <-A1P7 in H6 at 2.
rewrite <-M2 in H6.
rewrite A1P7 in H6.
rewrite A4 in H6.
rewrite (A1 0), A3 in H6.
rewrite H4 in H6.
rewrite (M1 a) in H6.
rewrite <-A1P7 in H6.
rewrite <-M2 in H6.
rewrite D1 in H6.
rewrite <-(M2 x0) in H6.
rewrite (M1 a) in H6.
rewrite M1 in H6.
rewrite D1 in H6.
rewrite <-(M2 x0) in H6.
rewrite <-(M2 x2) in H6.
rewrite (M1 a) in H6.
rewrite M2 in H6.
rewrite M2 in H6.
rewrite A2 in H6.
rewrite <-(M3 a) in H6 at 1.
rewrite M1 in H6.
rewrite <-D1 in H6.
rewrite M1 in H6.
rewrite (M1 a) in H6.
rewrite M1 in H6.
pose proof (H5 x3).
destruct H10.
exists (1 + x0 * x2 * -1).
exists (x1 * x2 * -1).
rewrite M2.
rewrite <-(M2 b) in H6.
split.
symmetry in H6.
trivial.
trivial.
unfold lt in H9, H10.
apply N4 in H10.
rewrite <-A1P7 in H10.
rewrite M1 in H10.
unfold sub in H10.
rewrite D1 in H10.
rewrite A1P8 in H10.
rewrite M3 in H10.
rewrite M1, A1P7 in H10.
unfold sub in H9.
rewrite A1 in H9.
contradiction.
rewrite H10 in H9.
unfold lt in H9.
unfold sub in H9.
rewrite A4 in H9.
pose proof N0.
contradiction.
pose proof (P20 b x).
rewrite <-H8 in H9.
apply H10 in H9.
destruct H9.
destruct H9.
destruct H9.
destruct H11.
destruct H11.
apply (S1 _ _ (- x * x4)) in H9.
rewrite <-A2 in H9.
rewrite (A1 x5) in H9.
rewrite A2 in H9.
rewrite <-A1P7 in H9 at 2.
rewrite <-M2 in H9.
rewrite A1P7 in H9.
rewrite A4 in H9.
rewrite (A1 0), A3 in H9.
rewrite H4 in H9.
rewrite (M1 b) in H9.
rewrite <-A1P7 in H9.
rewrite <-M2 in H9.
rewrite D1 in H9.
rewrite <-(M2 x1) in H9.
rewrite (M1 b) in H9.
rewrite M1 in H9.
rewrite D1 in H9.
rewrite <-(M2 x1) in H9.
rewrite <-(M2 x4) in H9.
rewrite (M1 b) in H9.
rewrite M2 in H9.
rewrite M2 in H9.
rewrite (A1 (a * x0 * x4 * -1)) in H9.
rewrite A2 in H9.
rewrite <-(M3 b) in H9 at 1.
rewrite M1 in H9.
rewrite <-D1 in H9.
rewrite M1 in H9.
pose proof (H5 x5).
destruct H13.
exists (x0 * x4 * -1).
exists(1 + x1 * x4 * -1).
rewrite M2.
rewrite <-(M2 a) in H9.
split.
symmetry in H9.
rewrite A1 in H9.
trivial.
trivial.
unfold lt in H12, H13.
apply N4 in H12.
unfold sub in H12, H13.
rewrite <-A1P7 in H12.
rewrite M1, D1 in H12.
rewrite A1P8 in H12.
rewrite M1, A1P7 in H12.
rewrite M3 in H12.
rewrite A1 in H12.
contradiction.
rewrite H13 in H12.
unfold lt, sub in H12.
rewrite A4 in H12.
pose proof N0.
contradiction.
rewrite <-H11 in H9.
rewrite A3 in H9.
rewrite <-H8 in H6.
rewrite A3 in H6.
assert (gcd(a,b)=x).
split.
unfold divide.
exists x2.
rewrite M1.
trivial.
split.
unfold divide.
exists x4.
rewrite M1.
trivial.
intros.
unfold divide in H13, H14.
destruct H14, H13.
rewrite H13 in H4.
rewrite H14 in H4.
unfold divide.
rewrite M1 in H4.
rewrite <-(M2 x7) in H4.
rewrite (M1 x6) in H4.
rewrite M2 in H4.
rewrite M2 in H4.
rewrite <-D1 in H4.
exists (x0 * x8 + x7 * x1).
trivial.
pose proof (equiv_gcd a b x 1).
apply H14 in H13.
exists x0.
exists x1.
rewrite <-H13.
trivial.
trivial.
rewrite <-H11 in H12.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
pose proof N1.
trivial.
Qed.

Theorem A5P2 : ∀ a b c : Z, gcd (a,b) = 1 → (a | b * c) → (a | c).
Proof.
intros.
apply A5P1 in H.
destruct H.
destruct H0.
destruct H.
apply (S2 _ _ c) in H.
rewrite M1, M3 in H.
rewrite D1 in H.
rewrite <-(M2 b) in H.
rewrite (M1 x1) in H.
rewrite (M2 b) in H.
rewrite H0 in H.
unfold divide.
rewrite M1 in H.
rewrite (M1 a) in H.
rewrite M2 in H.
rewrite <-(M2 x0) in H.
rewrite (M1 a) in H.
rewrite M2 in H.
rewrite <-D1 in H.
exists (c * x + x0 * x1).
exact H.
Qed.

(** ASSIGNMENT 6 BEGINS HERE -- due Wed. October 23 **)

Theorem A6P1 : ∀ p a : Z, p ∈ prime → ¬ (p | a) → gcd (a , p) = 1.
Proof.
intros.
split.
unfold divide.
exists a.
rewrite M3.
congruence.
split.
unfold divide.
exists p.
rewrite M3.
congruence.
intros.
unfold divide.
destruct H.
pose proof (H3 x).
apply H4 in H2.
destruct H2.
unfold pm in H2.
destruct H2.
rewrite H2.
exists 1.
rewrite M3.
congruence.
rewrite H2.
exists (-1).
rewrite A1P8.
rewrite M3.
congruence.
destruct H1.
destruct H2.
destruct H0.
unfold divide.
rewrite H2 in H1.
exists x0.
trivial.
destruct H0.
unfold divide.
rewrite H2 in H1.
exists (-x0).
rewrite M1 in H1.
rewrite <-A1P7 in H1.
rewrite <-M2 in H1.
rewrite (M1 p) in H1.
rewrite M2 in H1.
rewrite A1P7 in H1.
trivial.
Qed.

Theorem A6P1_ : ∀ p a : Z, p ∈ prime → ¬ (p | a) → gcd (a , p) = 1 \/ gcd (a , p) = -1.
Proof.
intros.
left.
split.
unfold divide.
exists a.
rewrite M3.
congruence.
split.
unfold divide.
exists p.
rewrite M3.
congruence.
intros.
unfold divide.
destruct H.
pose proof (H3 x).
apply H4 in H2.
destruct H2.
unfold pm in H2.
destruct H2.
rewrite H2.
exists 1.
rewrite M3.
congruence.
rewrite H2.
exists (-1).
rewrite A1P8.
rewrite M3.
congruence.
destruct H1.
destruct H2.
destruct H0.
unfold divide.
rewrite H2 in H1.
exists x0.
trivial.
destruct H0.
unfold divide.
rewrite H2 in H1.
exists (-x0).
rewrite M1 in H1.
rewrite <-A1P7 in H1.
rewrite <-M2 in H1.
rewrite (M1 p) in H1.
rewrite M2 in H1.
rewrite A1P7 in H1.
trivial.
Qed.

Theorem A6P2 : ∀ a b p : Z, p ∈ prime → (p | a * b) → (p | a) ∨ (p | b).
Proof.
intros.
destruct (classic (p | a)).
left.
trivial.
pose proof (A6P1 p a).
pose proof (A5P2 p a b).
apply H2 in H.
apply gcd_1 in H.
pose proof H.
apply H3 in H.
right.
trivial.
trivial.
trivial.
Qed.

(** ASSIGNMENT 7 BEGINS HERE -- due Wed. October 30 **)

(* In this assignment we show how to use Coq to define the integers mod n.
   We will only develop a small part of the theory of integers mod n in Coq.
   In principle, it is possible to prove much more -- Chinese Remainder
   Theorem, Fermat's Little Theorem, etc. *)

Section Z_mod_n.

  Variable n : Z. (* n is the modulus *)

  Definition eq_mod n a b := (n | b-a).

  Notation "a ≡ b (mod  n )" := (eq_mod n a b) (at level 70).

  (* Proof that equivalence mod n is an equivalence relation. *)

  Theorem eq_mod_refl : ∀ a : Z, a ≡ a (mod n).
  Proof.
    intros a.
unfold eq_mod.
unfold divide.
    exists 0.
    unfold sub.
    now rewrite A4, A1P6.
  Qed.

  Theorem eq_mod_sym : ∀ a b : Z, a ≡ b (mod n) → b ≡ a (mod n).
  Proof.
    intros a b [x H].
    exists (-x).
    unfold sub in *.
    now rewrite <-(A1P7 x), <-M2, <-H, M1, D1, ? (M1 _ (-1)), ? A1P7, A1, A1P5.
  Qed.

  Theorem eq_mod_trans :
    ∀ a b c : Z, a ≡ b (mod n) → b ≡ c (mod n) → a ≡ c (mod n).
  Proof.
    intros a b c [x H] [y H0].
    exists (x+y).
    unfold sub in *.
    now rewrite D1, <-H, <-H0, (A1 (b+-a)), ? A2, <-(A2 c), A1P2, A3.
  Qed.

  Add Parametric Relation : Z (eq_mod n)
      reflexivity proved by (eq_mod_refl)
      symmetry proved by (eq_mod_sym)
      transitivity proved by (eq_mod_trans) as Z_mod_n.

  Theorem S1_mod : ∀ a b c : Z, a ≡ b (mod n) → a+c ≡ b+c (mod n).
  Proof.
    intros a b c H.
    (* Fails because we haven't proved that addition is well-defined mod n. *)
    Fail rewrite H.
  Abort.

  (* So ... let's prove that addition is well-defined mod n.
     For reference: Chapter II Proposition 2.1 in the course notes. *)

  Add Morphism add with signature (eq_mod n) ==> (eq_mod n) ==> (eq_mod n)
        as A7P1a.
  Proof.
    intros a b [x H] c d [y H0].
    exists (x+y).
    unfold sub in *.
    now rewrite D1, <-H, <-H0, <-(A1P7 (a+c)), (M1 (-1)), D1, ? (M1 _ (-1)),
    ? A1P7, ? A2, <-(A2 b), (A1 d), ? A2.
  Qed.

  Theorem S1_mod : ∀ a b c : Z, a ≡ b (mod n) → a+c ≡ b+c (mod n).
  Proof.
    intros a b c H.
    (* Now the same proof works, and no longer fails. *)
    now rewrite H.
  Qed.

  (* A7P1b, A7P1c, and A7P1d are exercises for you to complete. *)

  Add Morphism mult with signature (eq_mod n) ==> (eq_mod n) ==> (eq_mod n)
        as A7P1b.
  Proof.
intros.
unfold eq_mod in *.
unfold divide in *.
destruct H, H0.
unfold sub in *.
apply (S1 _ _ x) in H.
rewrite <-A2, A1P2 in H.
rewrite negative_inside.
rewrite A3 in H.
apply (S1 _ _ x0) in H0.
rewrite <-A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0.
exists (x1*n*x2 + x*x2 + x1 * x0).
rewrite H.
rewrite H0.
rewrite D1.
rewrite M1.
rewrite D1.
rewrite (M1 x).
rewrite D1.
rewrite M1.
rewrite M2.
rewrite M2.
rewrite (M1 x0).
rewrite <-A2.
rewrite <-(A2 (x2*n*x)).
rewrite (M1 x0).
rewrite <-A1P7.
rewrite <-(M2 (-1)).
rewrite A1P7.
rewrite A4.
rewrite A3.
rewrite <-(M2 x2).
rewrite (M1 n).
rewrite M2.
rewrite <-D1.
rewrite <-D1.
rewrite <-A2.
rewrite (A1 (x1 * x0)).
rewrite A2.
rewrite (M1 x2).
congruence.
Qed.

  Add Morphism neg with signature (eq_mod n) ==> (eq_mod n) as A7P1c.
  Proof.
intros.
unfold eq_mod in *.
unfold sub.
rewrite A1P5.
unfold sub in H.
apply pos_neg_div in H.
rewrite <-A1P7 in H.
rewrite M1 in H.
rewrite D1 in H.
rewrite M1, A1P7 in H.
rewrite A1P8 in H.
rewrite M3 in H.
trivial.
Qed.

  Add Morphism sub with signature (eq_mod n) ==> (eq_mod n) ==> (eq_mod n)
        as A7P1d.
  Proof.
intros.
unfold eq_mod in *.
unfold divide in *.
destruct H, H0.
exists (x1 - x2).
unfold sub.
rewrite <-(A1P7 (x + -x0)).
rewrite M1.
rewrite D1.
rewrite A1P8.
rewrite M3.
rewrite M1, A1P7.
rewrite A2.
rewrite A1.
rewrite <-A2.
rewrite (A1 (-y0)).
rewrite (A2 (y)).
unfold sub in H.
rewrite H.
rewrite (A1 (x1*n)).
rewrite A2.
rewrite <-A1P7.
unfold sub in H0.
apply (S1 _ _ x0) in H0.
rewrite <-A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0.
rewrite H0.
rewrite M1.
rewrite D1.
rewrite M1, A1P7.
rewrite negative_inside.
rewrite (M1 x0), A1P7.
rewrite (A1 (-x2 * n)).
rewrite A2.
rewrite A4.
rewrite A1.
rewrite (A1 0).
rewrite A3.
rewrite <-D1.
congruence.
Qed.

  Theorem S2_mod : ∀ a b c : Z, a ≡ b (mod n) → a*c ≡ b*c (mod n).
  Proof.
    intros a b c H.
    now rewrite H.
  Qed.

  Definition mod_unit := {a : Z | ∃ x : Z, a * x ≡ 1 (mod n)}.

  Theorem A7P2a : ∀ a b : Z, a ∈ mod_unit → b ∈ mod_unit → a*b ∈ mod_unit.
  Proof.
intros.
unfold In, mod_unit in *.
unfold eq_mod in *.
destruct H0.
destruct H.
unfold divide in *.
destruct H, H0.
exists (x * x0).
rewrite M2.
rewrite M1.
rewrite <-M2.
apply (S1 _ _ (-1)) in H0.
unfold sub in H0.
rewrite A1 in H0.
rewrite A2 in H0.
rewrite A1P2 in H0.
rewrite A1, A3 in H0.
rewrite <-A1P7 in H0.
apply (S2 _ _ (-1)) in H0.
rewrite M1 in H0.
rewrite M2 in H0.
rewrite A1P8 in H0.
rewrite M3 in H0.
rewrite M1, M3 in H0.
rewrite D1 in H0.
rewrite A1P8 in H0.
rewrite M3 in H0.
rewrite (M1 (x2 * n)) in H0.
rewrite A1P7 in H0.
rewrite H0.
rewrite M2.
unfold sub.
rewrite M1.
rewrite (M1 x0).
apply (S1 _ _ (-1)) in H.
unfold sub in H.
rewrite A1 in H.
rewrite A2 in H.
rewrite A1P2 in H.
rewrite A1, A3 in H.
apply (S2 _ _ (-1)) in H.
rewrite M1, A1P7, A1P5 in H.
rewrite D1 in H.
rewrite A1P8, M3 in H.
rewrite <-M2 in H.
rewrite (M1 n) in H.
rewrite (M1 x1) in H.
rewrite A1P7 in H.
rewrite H.
rewrite D1.
rewrite negative_inside.
rewrite M1, D1.
rewrite <-A1P7.
rewrite (M1 (-1)).
rewrite D1.
rewrite D1.
rewrite M1.
rewrite A1P7.
rewrite negative_inside.
rewrite M1.
rewrite negative_inside.
rewrite A1P5.
rewrite (M1 n).
rewrite M2.
rewrite (M1 1).
rewrite M3.
rewrite (M1 1).
rewrite M3.
rewrite (M1 (-x2 * n) (-1)).
rewrite A1P7.
rewrite negative_inside.
rewrite A1P5.
rewrite D1.
rewrite (M1 (- n * x1)).
rewrite A1P7.
rewrite negative_inside.
rewrite A1P5.
rewrite (M1 1).
rewrite M3.
rewrite A1.
rewrite <-A2.
rewrite A1.
rewrite <-A2.
rewrite <-A2.
rewrite A1.
rewrite A2.
rewrite A1P2.
rewrite (A1 0).
rewrite A3.
rewrite (M1 n).
rewrite <-D1.
rewrite <-D1.
exists (-x2 * n * x1 + x2 + x1).
congruence.
Qed.

  Theorem A7P2b : ∀ a b c : Z, a ∈ mod_unit → a*b ≡ a*c (mod n) → b ≡ c (mod n).
  Proof.
intros.
unfold mod_unit in H.
unfold In in H.
destruct H.
unfold eq_mod in *.
destruct H, H0.
unfold divide.
rewrite M1 in H0.
rewrite (M1 a) in H0.
unfold sub in H0.
rewrite negative_inside in H0.
rewrite <-D1 in H0.
apply (S2 _ _ x) in H0.
apply (S1 _ _ (a * x + (- x0 * n))) in H.
unfold sub in H.
rewrite A2 in H.
rewrite A1 in H.
rewrite <-(A2 1) in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite (A1 (a * x)) in H.
rewrite A2 in H.
rewrite <-A1P7 in H at 2.
rewrite <-M2 in H.
rewrite A1P7 in H.
rewrite A4 in H.
rewrite (A1 0), A3 in H.
rewrite <-M2 in H0.
rewrite <-H in H0.
rewrite D1 in H0.
rewrite M1, D1 in H0.
rewrite (M1 (-b)), D1 in H0.
rewrite (M1 1), M3 in H0.
rewrite (M1 1), M3 in H0.
rewrite A1 in H0.
rewrite A2 in H0.
unfold sub.
apply (S1 _ _ (- (x1 * n * x))) in H0.
rewrite A4 in H0.
apply (S1 _ _ (-c)) in H0.
rewrite (A1 0), A3 in H0.
rewrite <-A2 in H0.
rewrite (A1 (- (x1 * n * x))) in H0.
rewrite A2 in H0.
rewrite A1 in H0.
rewrite <-A2 in H0.
rewrite A4 in H0.
rewrite A3 in H0.
rewrite A2 in H0.
rewrite A1 in H0.
rewrite A2 in H0.
apply (S1 _ _ b) in H0.
rewrite A2 in H0.
rewrite <-A2 in H0.
rewrite A1P2 in H0.
rewrite A3 in H0.
apply (S2 _ _ (-1)) in H0.
rewrite D1 in H0.
rewrite D1 in H0.
rewrite D1 in H0.
rewrite A1P8 in H0.
rewrite A1P8 in H0.
rewrite M3 in H0.
rewrite M3 in H0.
rewrite (M1 b), A1P7 in H0.
symmetry in H0.
rewrite <-M2 in H0.
rewrite M1 in H0.
rewrite M2 in H0.
rewrite <-A2 in H0.
rewrite (A1 (c * -1 * - x0 * n)) in H0.
rewrite <-M2 in H0.
rewrite (M1 n) in H0.
rewrite M2 in H0.
rewrite <-A2 in H0.
rewrite (A1 (x1 * x * n)) in H0.
rewrite <-M2 in H0.
rewrite M1 in H0.
rewrite M2 in H0.
rewrite <-D1 in H0.
rewrite <-D1 in H0.
exists (- b * -1 * - x0 + c * -1 * - x0 + x1 * x).
trivial.
Qed.

Theorem A7P2c : ∀ a b : Z, a ∈ mod_unit → ∃ c : Z, b ≡ a * c (mod n).
Proof.
intros.
unfold mod_unit in H.
unfold In in H.
destruct H.
destruct H.
unfold eq_mod.
unfold divide.
apply (S2 _  _ (-b)) in H.
unfold sub in H.
rewrite D1 in H.
rewrite M1, M3 in H.
unfold sub.
rewrite A1P8 in H.
rewrite A1 in H.
exists (x * b).
rewrite M2.
rewrite (M1 (x0 * n)) in H.
rewrite M2 in H.
exists (-b * x0).
trivial.
Qed.


  Theorem A7P3 : ∀ a : Z, a ∈ mod_unit ↔ gcd (a,n) = 1.
  Proof.
intros.
split.
intros.
destruct H.
split.
unfold divide.
exists a.
rewrite M3.
trivial.
split.
unfold divide.
exists n.
rewrite M3.
trivial.
intros.
unfold divide.
destruct H0, H1.
destruct H.
apply (S1 _ _ (a * x)) in H.
unfold sub in H.
rewrite <-A2 in H.
rewrite A1P2 in H.
rewrite A3 in H.
rewrite (M1 a) in H.
rewrite H0 in H.
rewrite H1 in H.
rewrite M2 in H.
rewrite M2 in H.
rewrite <-D1 in H.
exists (x3 * x2 + x * x1).
trivial.
intros.
unfold mod_unit, In.
unfold eq_mod.
unfold divide.
apply A5P1 in H.
destruct H.
destruct H.
rewrite A1 in H.
apply (S1 _ _ (- (a * x))) in H.
rewrite <-A2 in H.
rewrite A4 in H.
rewrite A3 in H.
exists x.
unfold sub.
exists x0.
rewrite (M1 n) in H.
trivial.
Qed.

End Z_mod_n.

(** ASSIGNMENT 8 BEGINS HERE -- due Wed. November 6 **)

Fixpoint product (L : list Z) :=
  match L with
    | nil => 1
    | p :: L => p * product L
  end.

Notation "∏ L" := (product L) (at level 50).

Definition prime_factorization (n : Z) (L : list Z) :=
  n = ∏ L ∧ (∀ p : Z, List.In p L → 0 < p ∧ p ∈ prime).

Notation "n = ∏' L" := (prime_factorization n L) (at level 50).

Lemma A8L1 : ∀ L L' : list Z, (∏ L) * (∏ L') = ∏ (L ++ L').
Proof.
  intros L.
  induction L as [| a L IHL]; simpl; intros L'.
  - now rewrite M1, M3.
  - now rewrite <-IHL, M2.
Qed.

Lemma A8L2 : ∀ (L L' : list Z) (p : Z), ∏ (L ++ p :: L') = p * (∏ (L ++ L')).
Proof.
  intros L.
  induction L as [| a L IHL]; auto.
  intros L' p.
  simpl.
  now rewrite M2, (M1 p), <-M2, IHL.
Qed.

Lemma A8L3: forall a b c : Z, a < b -> b < c -> a < b < c.
Proof.
intros.
split.
trivial.
trivial.
Qed.

Lemma A8L4: ∀ a b n :Z, 1 < a → 0 < n → n = a * b → 0 < b < n.
Proof.
intros.
pose proof H.
apply (O3 0 1 a) in H.
unfold lt, sub in *.
rewrite H1 in H0.
apply (reverse_N3 a b) in H.
split.
trivial.
apply (S1 _ _ (-b)) in H1.
rewrite <-A1P7 in H1 at 2.
rewrite <-D1 in H1.
rewrite H1.
unfold lt, sub in H.
rewrite negative_zero_equals_zero in H.
rewrite A3 in H.
pose proof (N3 (a + -1) b).
apply H3.
trivial.
trivial.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
exact N1.
Qed.

Lemma A8L5: ∀ a b n : Z, 1 < a < n → 1 < n → n = a * b → 1 < b < n.
intros.
destruct H.
pose proof H.
apply (A8L4 a b n) in H.
intuition.
rewrite H1 in H2.
unfold lt in H2.
unfold sub in H2.
rewrite <-A1P7 in H2.
rewrite M1 in H2.
rewrite <-D1 in H2.
pose proof (reverse_N3 a (b + -1)).
unfold lt in H.
unfold lt.
unfold sub in *.
rewrite negative_zero_equals_zero in *.
rewrite A3 in H.
rewrite A3 in H.
rewrite A3 in H.
apply H.
pose proof (O3 0 1 a).
apply H6 in H3.
unfold In.
rewrite N_gt_0.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero, A3.
exact N1.
rewrite M1 in H2.
trivial.
apply (O3 0 1 n) in H0.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero, A3.
exact N1.
trivial.
Qed.

Theorem A8P1 : ∀ n : Z, 1 < n → ∃ p : Z, p ∈ prime ∧ (p | n).
Proof.
intros.
induction n using P21.
destruct (classic (n ∈ prime)).
exists n.
split.
trivial.
unfold divide.
exists 1.
rewrite M1, M3.
trivial.
apply A4P4 in H1.
destruct H1.
destruct H1.
destruct H1.
pose proof (H0 x).
pose proof H1.
apply H4 in H1.
destruct H1.
destruct H1.
exists x0.
split.
trivial.
unfold divide.
destruct H2, H6.
rewrite H6 in H2.
rewrite M2 in H2.
exists (x1 * x2).
trivial.
split.
pose proof (O3 0 1 x).
apply H6 in H5.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
exact N1.
trivial.
trivial.
Qed.

Theorem A8P2_1 : ∀ n : Z, 1 < n → ∃ L : list Z, n = ∏' L.
Proof.
intros.
induction n using P21.
destruct (classic (n ∈ prime)).
assert (n = ∏ (n::nil)).
simpl.
rewrite M3.
trivial.
exists (n :: nil).
split.
trivial.
intros.
simpl in H2.
destruct H3.
split.
symmetry in H3.
rewrite H3.
apply (O3 0 1 n) in H.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
exact N1.
rewrite H3 in H1.
trivial.
contradiction.
apply A4P4 in H1.
destruct H1.
destruct H1.
destruct H2.
destruct H1.
apply (A8L3 1 x n) in H1.
pose proof H1.
apply (A8L5 x x0 n) in H1.
destruct H1.
pose proof H1.
apply H0 in H1.
apply (A8L3 0 x n) in H3.
apply H0 in H3.
destruct H1.
destruct H3.
destruct H1, H3.
rewrite H3,H1 in H2.
rewrite A8L1 in H2.
exists (x1 ++ x2).
split.
trivial.
intros.
rewrite in_app_iff in H9.
destruct H9.
apply H7 in H9.
trivial.
apply H8 in H9.
trivial.
destruct H3.
destruct H4.
trivial.
destruct H4.
apply (O3 0 1 x) in H4.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero.
rewrite A3.
exact N1.
intuition.
apply (O3 0 1 x0) in H6.
trivial.
unfold lt, sub.
rewrite negative_zero_equals_zero, A3.
exact N1.
trivial.
rewrite M1.
trivial.
trivial.
trivial.
Qed.

Lemma A8P2_helper : forall n : Z, 0 < n -> n = 1 \/ n > 1.
Proof.
intros.
pose proof (A2P3 n 1).
destruct H0.
pose proof (A3P3 n).
apply H1 in H.
contradiction.
trivial.
trivial.
Qed.

Theorem A8P2 : ∀ n : Z, 0 < n → ∃ L : list Z, n = ∏' L.
Proof.
intros.
pose proof (A8P2_1 n).
apply A8P2_helper in H.
destruct H.
exists nil.
rewrite H.
split.
simpl.
trivial.
intros.
contradiction.
apply H0 in H.
destruct H.
exists x.
trivial.
Qed.


(** ASSIGNMENT 10 BEGINS HERE -- due Wed. November 20 **)

Theorem A10P1 : ∀ a b c : Z, a ≤ b → b ≤ c → a ≤ c.
Proof.
intros.
destruct H.
destruct H0.
apply (O3 a b c) in H.
left.
trivial.
trivial.
rewrite H0 in H.
left.
trivial.
rewrite <-H in H0.
trivial.
Qed.

Theorem A10P2 : ∀ a b : Z, a ≤ b → b ≤ a → a = b.
Proof.
intros.
destruct H.
destruct H0.
unfold lt, sub in *.
apply N4 in H.
rewrite <-A1P7 in H.
rewrite M1, D1 in H.
rewrite M1, A1P7 in H.
rewrite M1, A1P7, A1P5 in H.
rewrite A1 in H.
contradiction.
congruence.
trivial.
Qed.

Definition le_trans := A10P1.
Definition le_antisymm := A10P2.

(** ASSIGNMENT 11 BEGINS HERE -- due Wed. November 27 **)

(* If you have an older version of Coq that cannot load the
   PropExtensionality package, see Piazza @589 for a solution. *)

Require Export Sorting Orders FunctionalExtensionality
        PropExtensionality ClassicalEpsilon.

(* Implementation of merge sort, used in the proof of A11L3, taken
   from https://coq.inria.fr/library/Coq.Sorting.Mergesort.html *)

Definition leb a b :=
  if (excluded_middle_informative (a ≤ b)) then true else false.

Module ZOrder <: TotalLeBool.
  Definition t := Z.
  Theorem leb_total : ∀ a b : Z, (leb a b) = true ∨ (leb b a) = true.
  Proof.
    intros a b.
    unfold leb, le.
    repeat destruct excluded_middle_informative;
      destruct (A2P3 a b) as [H | [H | H]]; auto.
  Qed.
  Definition leb := leb.
End ZOrder.

Module Export ZSort := Sort ZOrder.

(* Permuting a list preserves its product. *)
Lemma A11L1 : ∀ L1 L2 : list Z, Permutation L1 L2 → ∏ L1 = ∏ L2.
Proof.
  intros L1 L2 H.
  induction H; simpl; try congruence.
  eauto using M1, M2, eq_trans, f_equal.
Qed.

(* Permutations of prime factorizations are prime factorizations. *)
Lemma A11L2 : ∀ (n : Z) (L1 L2 : list Z),
    n = ∏' L1 → Permutation L1 L2 → n = ∏' L2.
Proof.
  intros n L1 L2 [H H0] H1.
  split; eauto using eq_trans, A11L1, Permutation_in, Permutation_sym.
Qed.

(* Every list can be permuted into a sorted list. *)
Lemma A11L3 : ∀ L : list Z,
    ∃ L' : list Z, Permutation L L' ∧ StronglySorted le L'.
Proof.
  intros L.
  exists (sort L).
  split; auto using Permuted_sort.
  replace le with (λ a b, is_true (leb a b)); unfold leb in *.
  - apply (StronglySorted_sort L); unfold leb in *; intros x y z H H0.
    repeat destruct excluded_middle_informative; eauto using le_trans.
  - repeat (apply functional_extensionality; intros).
    now destruct excluded_middle_informative;
      apply propositional_extensionality.
Qed.

(* Every list can be permuted into a unique sorted list. *)
Lemma A11L4 : ∀ L : list Z, exists ! L' : list Z,
      Permutation L L' ∧ StronglySorted le L'.
Proof.
  intros L.
  destruct (A11L3 L) as [L0 [H H0]].
  exists L0; split; auto; intros L1 [H1 H2].
  assert (Permutation L0 L1) as H3
      by eauto using Permutation_trans, Permutation_sym.
  generalize L0, L1, H3, H0, H2; clear.
  (* Induction on length of a list: https://github.com/tchajed/coq-tricks *)
  induction L0 as [L0 IHL0] using (induction_ltof1 _ (@length _));
    unfold ltof in IHL0.
  intros L1 H H0 H1.
  destruct L0 as [| a L0], L1 as [| b L1];
    auto using eq_sym, Permutation_nil, Permutation_sym.
  apply StronglySorted_inv in H0 as [H0 H2].
  apply StronglySorted_inv in H1 as [H1 H3].
  rewrite Forall_forall in *.
  replace a with b in *; eauto using Permutation_cons_inv, f_equal.
  destruct (Permutation_in a H), (Permutation_in b (Permutation_sym H));
    eauto using in_eq, le_antisymm.
Qed.

Lemma A11L5 : ∀ L p n,
   n = ∏' L → p ∈ prime → (p | n) → ∃ q, (p | q) ∧ List.In q L.
Proof.
induction L as [L IHL] using (induction_ltof1 _ (@length _)).
unfold ltof in IHL.
intros p n H H0 H1.
destruct L, H; simpl in *; subst.
apply A4P1 in H1.
firstorder.
apply A6P2 in H1 as [H1 | H1]; auto;
[exists z | eapply IHL in H1 as [q [H1]]];
eauto; split; auto.
Qed.

Lemma A11L6: ∀ L1 :list Z,1=∏' L1→L1=nil.
Proof.
intros.
destruct H.
induction L1;auto.
pose proof in_eq.
apply (H0 a) in H1.
destruct H1.
destruct H2.
symmetry in H.
apply a_times_b_equals_1 in H.
destruct H .
destruct H.
unfold not , pm in H2.
assert ( a = 1 ∨ a = -1).
left.
trivial.
apply H2 in H5.
contradiction.
unfold not,pm in H2.
assert ( a = 1 ∨ a = -1).
destruct H.
auto.
apply H2 in H4.
intuition.
Qed.


Lemma A11L7 : ∀ a : Z,0<a→a=∏'nil→∀ L1: list Z, a=∏' L1→L1=nil.
Proof.
intros.
destruct H0.
simpl in H0.
rewrite H0 in H1.
apply A11L6 in H1.
auto.
Qed.

Lemma A11L8:∀ (x p : Z) (l2 l1 : list Z), List.In x (l2 ++ l1) → List.In x (l2 ++ p :: l1).
Proof.
intros.
rewrite in_app_iff in *.
simpl in *.
tauto.
Qed.

Lemma A11L9:∀ a b : Z , (a | b) → 0 < a ∧ a ∈ prime → 0 < b ∧ b ∈ prime → a =b.
Proof.
intros.
destruct H1,H2.
apply H3 in H.
destruct H0.
firstorder.
unfold lt, sub in *.
rewrite  negative_zero_equals_zero, A3 in H0,H1.
rewrite H in H0.
apply N4 in H1.
contradiction.
Qed.

Lemma Natural_P8:  ∀ a b : Z,a∈N→a*b∈N→b∈N.
Proof.
intros.
pose proof (P8 a b).
unfold lt, sub in *.
rewrite negative_zero_equals_zero, A3 in *.
apply H1 in H.
rewrite A3 in *.
rewrite A3 in *.
trivial.
rewrite A3.
trivial.
Qed.

Theorem S3_new : ∀ a b c : Z, a ≠ 0 →a*b=a*c → b=c.
Proof.
intros.
pose proof (S3 b c a).
rewrite M1 in H0.
symmetry in H0.
rewrite M1 in H0.
symmetry in H0.
apply H1 in H0.
destruct H0.
trivial.
contradiction.
Qed.


(* Any two prime factorizations of n are permutations of each other. *)
Theorem A11P1 : ∀ n : Z,
   0 < n → ∀ L1 L2 : list Z, n = ∏' L1 → n = ∏' L2 → Permutation L1 L2.
Proof.
intros n.
induction n using P21.
intros.
destruct L1.
apply A11L7 in H2.
rewrite H2.
trivial.
trivial.
trivial.
destruct H1.
assert (List.In z (z :: L1)).
intuition.
apply H3 in H4.
assert (z | n).
exists (∏ L1).
rewrite M1.
trivial.
pose proof H2.
apply (A11L5 _ z _) in H2.
destruct H2.
destruct H2.
destruct H6.
pose proof H7.
apply H8 in H7.
apply A11L9 in H2.
rewrite <-H2 in H9.
apply in_split in H9.
destruct H9.
destruct H9.
rewrite H9, A8L2 in H6.
assert (z ≠ 0).
unfold not.
intros.
destruct H4.
apply (O7 0 z) in H4.
symmetry in H10.
contradiction.
destruct H5.
destruct H7.
pose proof H5.
assert (x2 | n).
exists z.
rewrite M1.
trivial.
apply P13 in H13.
assert (0 < x2).
unfold lt, sub in *.
rewrite negative_zero_equals_zero, A3 in *.
eapply Natural_P8 in H7.
exact H7.
rewrite M1.
rewrite H2 in H12.
rewrite H12 in H0.
auto.
destruct H13.
assert (0 < x2 < n).
intuition.
rewrite M1 in H12.
pose proof H10.
apply (S3_new z x2 (∏ L1)) in H10.
apply (S3_new z x2 (∏ (x0 ++ x1))) in H16.
pose proof (H x2).
pose proof (H17 H15 H14 (x0 ++ x1) L1).
assert (x2 = ∏' (x0 ++ x1)).
split.
auto.
intros.
rewrite H9 in H8.
apply (A11L8 p z) in H19.
apply H8 in H19.
auto.
assert (x2 = ∏' L1).
split.
auto.
intros.
apply (in_cons z) in H20.
apply H3 in H20.
auto.
pose proof (H18 H19 H20).
apply Permutation_sym in H21.
apply (Permutation_cons_app _ _ z) in H21.
rewrite <-H9 in H21.
auto.
rewrite <-H12.
auto.
rewrite <-H12.
auto.
rewrite H13 in H12.
symmetry in H12.
apply A1P10 in H12.
destruct H12.
destruct H11.
unfold not , pm in H11.
assert (z = 1 ∨ z = -1).
auto.
destruct H11.
rewrite H2 in H12.
left.
trivial.
rewrite H12 in H13.
apply (O7 0 x2) in H14.
symmetry in H13.
contradiction.
trivial.
trivial.
trivial.
trivial.
destruct H4.
trivial.
trivial.
Qed.

(* Every positive integer has a unique sorted prime factorization. *)
Theorem A11P2 : ∀ n : Z,
    0 < n → exists ! L : list Z, n = ∏' L ∧ StronglySorted le L.
Proof.
intros n H.
destruct (A8P2 n) as [L H0]; auto.
destruct (A11L4 L) as [L1 [[H1 H2] H3]]; auto.
exists L1.
split; eauto using A11L2.
intros L2 [H4 H5].
destruct (A11L4 L1) as [L3 [H6 H7]].
assert (L3 = L2); eauto 6 using A11P1, Permutation_sym, Permutation_trans.
Qed.

(* A11P2 implies A11P1. Hence if you prove A11P2 then A11P1 follows. *) 
Theorem proof_of_A11P1_using_A11P2 : ∀ n : Z,
    0 < n → ∀ L1 L2 : list Z, n = ∏' L1 → n = ∏' L2 → Permutation L1 L2.
Proof.
  intros n H L1 L2 H0 H1.
  destruct (A11L4 L1) as [L1' [[H2 H3] H4]], (A11L4 L2)
      as [L2' [[H5 H6] H7]], (A11P2 n) as [L [[H8 H9] H10]]; auto.
  assert (L = L1'); assert (L = L2'); subst;
    eauto using A11L2, Permutation_sym, Permutation_trans.
Qed.

(* A11P1 implies A11P2. Hence if you prove A11P1 then A11P2 follows. *) 
Theorem proof_of_A11P2_using_A11P1 : ∀ n : Z,
    0 < n → exists ! L : list Z, n = ∏' L ∧ StronglySorted le L.
Proof.
  intros n H.
  destruct (A8P2 n) as [L H0]; auto.
  destruct (A11L4 L) as [L1 [[H1 H2] H3]]; auto.
  exists L1.
  split; eauto using A11L2.
  intros L2 [H4 H5].
  destruct (A11L4 L1) as [L3 [H6 H7]].
  assert (L3 = L2); eauto 6 using A11P1, Permutation_sym, Permutation_trans.
Qed.