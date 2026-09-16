/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import BrowningSawin.Attr
public import BrowningSawin.External
public import BrowningSawin.Cited
public import BrowningSawin.Defs.Definitions
public import BrowningSawin.Notation
public import BrowningSawin.ReductionModuloAPrime
public import BrowningSawin.ConcentrationOfSignSums
public import BrowningSawin.SingularityAtAPrescribedClosedPoint
public import BrowningSawin.ClosedPointsOfLargeDegree
public import BrowningSawin.TheFiniteFieldEstimate

/-!
# The main results

The four theorems the source states about the random sign form `f` of degree `d` in `n + 1`
variables: two bounds on the probability that `f` is badly behaved over `ℂ` — that its singular
locus is positive-dimensional, and that it is reducible — the resulting `O_n(d^{-1/2})` bound on
the probability that `f` is singular, and the Browning–Sawin conjecture on the proportion of
nonsingular forms in `𝓑_{d,n}`. All four are conditional on `CitedResults`, the results the source
defers to the literature.

The geometry those bounds run on is developed here as well: factors of a homogeneous polynomial are
homogeneous, two forms vanishing at the origin cut out a set of codimension at most two, a
projective set with finitely many points has dimension at most zero, and a positive-dimensional
singular locus is seen on one of the standard affine charts.

## Main results

* `MvPolynomial.IsHomogeneous.isHomogeneous_left_of_mul` and
  `MvPolynomial.IsHomogeneous.isHomogeneous_right_of_mul` (`lem_homogeneous_factors`): over a
  domain, a nonzero factor of a homogeneous polynomial is homogeneous, of its own total degree.

* `BrowningSawin.one_le_projDim_singularLocus_of_not_irreducible` (`lem_reducible_sing`): for
  `n ≥ 3` a nonzero reducible form `F ∈ ℂ[x₀, …, x_n]` of positive degree has `dim Sing X_F ≥ 1`.

* `BrowningSawin.signMeasure_one_le_projDim_singularLocus_le` (`thm_positive`): for `n ≥ 1` and
  `d ≥ 3`, `P(dim Sing X_f ≥ 1) ≤ n(n+1) d^{n-1} 2^{-⌊(d-1)/3⌋-1}` over `ℂ`.

* `BrowningSawin.signMeasure_not_irreducible_complex_le` (`thm_absolute_irred`): for `n ≥ 3` and
  `d ≥ 3`, the same bound for the probability that `f` is reducible over `ℂ`.

* `BrowningSawin.exists_measure_isSingularForm_complex_le` (`thm_main`): for `n ≥ 1` there is a
  `C_n > 0` with `P(f is singular over ℂ) ≤ C_n d^{-1/2}` for every `d ≥ 3`.

* `BrowningSawin.exists_forall_abs_card_notSingular_div_sub_one_le` (`thm_bs_conjecture`): for
  `n ≥ 2`, `#{F ∈ 𝓑_{d,n} : F is not singular}/2^{N_{d,n}} = 1 + O_n(d^{-1/2})` over `ℂ`.
-/

@[expose] public section

open MvPolynomial

/-! ## Factors of a homogeneous polynomial

The argument runs the top-degree and the bottom-degree part of a product against each other: both
are multiplicative over a domain, and for a homogeneous product they must agree, which pins the two
extremes of each factor together.

Mathlib has the top half already (`MvPolynomial.totalDegree_mul_of_isDomain`); the bottom half is
`MvPolynomial.homogeneousComponent_add_mul_of_forall_le` below. The bottom degree of a polynomial
carries no name of its own: it is the `Finset.inf'` of `Finsupp.degree` over the support. -/

namespace MvPolynomial

variable {σ : Type*} {R : Type*}

section MinTotalDegree

variable [CommSemiring R]

/-- **The bottom homogeneous components multiply.** If every tuple in the support of `p` has degree
at least `a` and every tuple in the support of `q` has degree at least `b`, then the homogeneous
component of `p * q` in degree `a + b` is the product of the degree-`a` component of `p` and the
degree-`b` component of `q`.

Applied to the bottom degrees of `p` and of `q` this is the multiplicativity of the bottom degree,
the counterpart of `MvPolynomial.totalDegree_mul_of_isDomain`: every way of writing a tuple of
degree `a + b` as a sum uses a tuple of degree at least `a` and one of degree at least `b`, so both
degrees are forced to be exactly `a` and `b`. -/
theorem homogeneousComponent_add_mul_of_forall_le {p q : MvPolynomial σ R} {a b : ℕ}
    (hp : ∀ d ∈ p.support, a ≤ d.degree) (hq : ∀ d ∈ q.support, b ≤ d.degree) :
    homogeneousComponent (a + b) (p * q) =
      homogeneousComponent a p * homogeneousComponent b q := by
  classical
  have hhom : (homogeneousComponent a p * homogeneousComponent b q).IsHomogeneous (a + b) :=
    (homogeneousComponent_isHomogeneous a p).mul (homogeneousComponent_isHomogeneous b q)
  ext d
  rw [coeff_homogeneousComponent]
  split
  · rename_i hd
    rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxd : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hsum : x.1.degree + x.2.degree = a + b := by
      rw [← map_add Finsupp.degree, hxd, hd]
    rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
    by_cases h1 : x.1.degree = a
    · rw [ite_eq_left h1, ite_eq_left (by omega : x.2.degree = b)]
    · rw [ite_eq_right h1]
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · have hz : coeff x.1 p = 0 := by
          by_contra hc
          exact absurd (hp _ (mem_support_iff.2 hc)) (by omega)
        rw [hz, zero_mul, zero_mul]
      · have hz : coeff x.2 q = 0 := by
          by_contra hc
          exact absurd (hq _ (mem_support_iff.2 hc)) (by omega)
        rw [ite_eq_right (by omega : ¬x.2.degree = b), hz, mul_zero, mul_zero]
  · rename_i hd
    exact (hhom.coeff_eq_zero hd).symm

end MinTotalDegree

section HomogeneousFactors

variable [CommRing R] [IsDomain R] {A B : MvPolynomial σ R} {m : ℕ}

/-- `Finsupp.weight 1`, the shape `MvPolynomial.IsHomogeneous` unfolds to, is `Finsupp.degree`. -/
private theorem weight_one_apply (d : σ →₀ ℕ) : Finsupp.weight (1 : σ → ℕ) d = d.degree := by
  simp [Finsupp.degree_eq_weight_one, Pi.one_def]

/-- **Factors of a homogeneous polynomial are homogeneous** (`lem_homogeneous_factors`), left
factor. Over a domain, if `A * B` is homogeneous and `A` and `B` are nonzero then `A` is
homogeneous, necessarily of its own total degree.

Writing `μ` and `ν` for the smallest and the largest degree occurring in a nonzero polynomial, both
are additive over products because the ring is a domain: `ν` by
`MvPolynomial.totalDegree_mul_of_isDomain` and `μ` by
`MvPolynomial.homogeneousComponent_add_mul_of_forall_le`. A homogeneous `A * B` has `μ = ν`, so
`μ(A) + μ(B) = ν(A) + ν(B)`, and `μ ≤ ν` for each factor separately forces equality in each.

No nonconstancy hypothesis on the factors is needed: a nonzero constant is homogeneous of degree
`0`. -/
@[browning_sawin "lem_homogeneous_factors"]
theorem IsHomogeneous.isHomogeneous_left_of_mul (h : (A * B).IsHomogeneous m) (hA : A ≠ 0)
    (hB : B ≠ 0) : A.IsHomogeneous A.totalDegree := by
  obtain ⟨dA, hdA, hdAeq⟩ := Finset.exists_mem_eq_inf' (support_nonempty.2 hA) Finsupp.degree
  obtain ⟨dB, hdB, hdBeq⟩ := Finset.exists_mem_eq_inf' (support_nonempty.2 hB) Finsupp.degree
  have hlowA : ∀ d ∈ A.support, dA.degree ≤ d.degree := by
    intro d hd; rw [← hdAeq]; exact Finset.inf'_le _ hd
  have hlowB : ∀ d ∈ B.support, dB.degree ≤ d.degree := by
    intro d hd; rw [← hdBeq]; exact Finset.inf'_le _ hd
  have hcA : homogeneousComponent dA.degree A ≠ 0 := fun hc => by
    have hco := coeff_homogeneousComponent dA.degree A dA
    rw [hc, coeff_zero, ite_eq_left rfl] at hco
    exact (mem_support_iff.1 hdA) hco.symm
  have hcB : homogeneousComponent dB.degree B ≠ 0 := fun hc => by
    have hco := coeff_homogeneousComponent dB.degree B dB
    rw [hc, coeff_zero, ite_eq_left rfl] at hco
    exact (mem_support_iff.1 hdB) hco.symm
  have hne : homogeneousComponent (dA.degree + dB.degree) (A * B) ≠ 0 := by
    rw [homogeneousComponent_add_mul_of_forall_le hlowA hlowB]
    exact mul_ne_zero hcA hcB
  have hab : dA.degree + dB.degree = m := by
    by_contra hcon
    refine hne ?_
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h), ite_eq_right hcon]
  have htop : A.totalDegree + B.totalDegree = m := by
    rw [← totalDegree_mul_of_isDomain hA hB]
    exact h.totalDegree (mul_ne_zero hA hB)
  have haA : dA.degree ≤ A.totalDegree := le_totalDegree hdA
  have hbB : dB.degree ≤ B.totalDegree := le_totalDegree hdB
  intro d hd
  have h1 : dA.degree ≤ d.degree := hlowA _ (mem_support_iff.2 hd)
  have h2 : d.degree ≤ A.totalDegree := le_totalDegree (mem_support_iff.2 hd)
  rw [weight_one_apply]
  omega

/-- **Factors of a homogeneous polynomial are homogeneous** (`lem_homogeneous_factors`), right
factor; the left case with the product commuted. -/
@[browning_sawin "lem_homogeneous_factors"]
theorem IsHomogeneous.isHomogeneous_right_of_mul (h : (A * B).IsHomogeneous m) (hA : A ≠ 0)
    (hB : B ≠ 0) : B.IsHomogeneous B.totalDegree :=
  IsHomogeneous.isHomogeneous_left_of_mul (by rwa [mul_comm] at h) hB hA

end HomogeneousFactors

/-! ## Two consequences of homogeneity -/

/-- A homogeneous polynomial of positive degree vanishes at the origin. -/
theorem eval_zero_of_isHomogeneous {σ : Type*} [Finite σ] [CommRing R] {e : ℕ}
    {G : MvPolynomial σ R} (hG : G.IsHomogeneous e) (he : 0 < e) : eval 0 G = 0 := by
  have h := eval_smul_of_isHomogeneous hG (0 : R) (0 : σ → R)
  rw [zero_smul, zero_pow (by omega), zero_mul] at h
  exact h

/-- A nonzero homogeneous polynomial of positive degree over a field is not a unit. -/
theorem not_isUnit_of_isHomogeneous {σ : Type*} {K : Type*} [Field K] {e : ℕ}
    {G : MvPolynomial σ K} (hG : G.IsHomogeneous e) (hG0 : G ≠ 0) (he : 0 < e) : ¬IsUnit G := by
  intro hu
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.1 hu
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hdeg := totalDegree_mul_of_isDomain hG0 hv0
  rw [hv, totalDegree_one, hG.totalDegree hG0] at hdeg
  omega

/-- A nonzero polynomial of total degree zero over a field is a unit. -/
theorem isUnit_of_totalDegree_eq_zero {σ : Type*} {K : Type*} [Field K] {G : MvPolynomial σ K}
    (hG0 : G ≠ 0) (h : G.totalDegree = 0) : IsUnit G := by
  obtain ⟨c, rfl⟩ : ∃ c, G = C c := ⟨G.coeff 0, totalDegree_eq_zero_iff_eq_C.1 h⟩
  have hc : c ≠ 0 := by rintro rfl; rw [map_zero] at hG0; exact hG0 rfl
  exact isUnit_iff_exists_inv.2 ⟨C c⁻¹, by rw [← C_mul, mul_inv_cancel₀ hc, C_1]⟩

end MvPolynomial

namespace BrowningSawin

open MvPolynomial

universe u

/-! ## Dimension of an affine algebraic set

`affineDim` reads the Krull dimension of the reduced coordinate ring off `WithBot ℕ∞`, and the
translation is faithful because a polynomial ring over a field has finite dimension: for a nonempty
algebraic set the dimension is an honest natural number
(`exists_ringKrullDim_quotient_affineVanishingIdeal`), and everything else follows. -/

section Dimension

variable {K : Type*} [Field K] {n : ℕ}

/-- The reduced coordinate ring of a set of points of `𝔸ⁿ` has Krull dimension at most `n`; in
particular the dimension is finite. -/
theorem ringKrullDim_quotient_affineVanishingIdeal_le (V : Set (Fin n → K)) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
  have hpoly : ringKrullDim (MvPolynomial (Fin n) K) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  exact hpoly ▸ ringKrullDim_quotient_le _

/-- For a nonempty affine algebraic set the Krull dimension of the reduced coordinate ring is a
natural number, and it is `affineDim`. -/
theorem exists_ringKrullDim_quotient_affineVanishingIdeal {V : Set (Fin n → K)} (hV : V.Nonempty) :
    ∃ k : ℕ, ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)
        = ((k : ℕ∞) : WithBot ℕ∞) ∧ affineDim V = (k : ℤ) := by
  have hnt : Nontrivial (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff,
      affineVanishingIdeal_eq_top_iff]
    exact Set.nonempty_iff_ne_empty.1 hV
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle := ringKrullDim_quotient_affineVanishingIdeal_le V
  obtain ⟨r, hr⟩ : ∃ r : ℕ∞, ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)
      = ((r : ℕ∞) : WithBot ℕ∞) := by
    cases hcase : ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) with
    | bot => rw [hcase] at h0; simp at h0
    | coe r => exact ⟨r, rfl⟩
  rw [hr] at hle
  have hrn : r ≤ (n : ℕ∞) := by exact_mod_cast hle
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top n) hrn)
  refine ⟨k, hr, ?_⟩
  rw [affineDim, hr, WithBot.recBotCoe_coe]
  simp

/-- A lower bound for the Krull dimension of the reduced coordinate ring is a lower bound for
`affineDim`. -/
theorem le_affineDim_of_le_ringKrullDim {V : Set (Fin n → K)} {c : ℕ}
    (h : ((c : ℕ∞) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)) :
    (c : ℤ) ≤ affineDim V := by
  have hV : V.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    rw [← affineVanishingIdeal_eq_top_iff] at he
    rw [he] at h
    have : Subsingleton (MvPolynomial (Fin n) K ⧸ (⊤ : Ideal (MvPolynomial (Fin n) K))) :=
      Ideal.Quotient.subsingleton_iff.2 rfl
    rw [ringKrullDim_eq_bot_of_subsingleton] at h
    simp at h
  obtain ⟨k, hk, hdim⟩ := exists_ringKrullDim_quotient_affineVanishingIdeal hV
  rw [hk] at h
  rw [hdim]
  exact_mod_cast (by exact_mod_cast h : (c : ℕ∞) ≤ (k : ℕ∞))

/-- The dimension of an affine algebraic set is monotone: a subset has the larger vanishing ideal,
hence the quotient with fewer primes. -/
theorem affineDim_mono {V W : Set (Fin n → K)} (h : V ⊆ W) : affineDim V ≤ affineDim W := by
  rcases Set.eq_empty_or_nonempty V with rfl | hV
  · rw [affineDim_empty]; exact neg_one_le_affineDim W
  · obtain ⟨k, hk, hdim⟩ := exists_ringKrullDim_quotient_affineVanishingIdeal hV
    have hideal : affineVanishingIdeal W ≤ affineVanishingIdeal V := by
      intro F hF
      rw [mem_affineVanishingIdeal] at hF ⊢
      exact fun a ha => hF a (h ha)
    rw [hdim]
    refine le_affineDim_of_le_ringKrullDim ?_
    rw [← hk, ringKrullDim_quotient, ringKrullDim_quotient]
    exact Order.krullDim_le_of_strictMono
      (fun p => ⟨p.1, (PrimeSpectrum.mem_zeroLocus _ _).2
        (hideal.trans ((PrimeSpectrum.mem_zeroLocus _ _).1 p.2))⟩)
      fun _ _ hab => hab

/-- A single point has dimension `0`: the functions vanishing at it form a maximal ideal, so the
coordinate ring is a field. -/
theorem affineDim_singleton_le (a : Fin n → K) : affineDim ({a} : Set (Fin n → K)) ≤ 0 := by
  have hker : affineVanishingIdeal ({a} : Set (Fin n → K)) = RingHom.ker (eval a) := by
    ext F
    rw [mem_affineVanishingIdeal, RingHom.mem_ker]
    simp
  have : (affineVanishingIdeal ({a} : Set (Fin n → K))).IsMaximal := by
    rw [hker]
    exact RingHom.ker_isMaximal_of_surjective (eval a) fun r => ⟨C r, by simp⟩
  obtain ⟨k, hk, hdim⟩ :=
    exists_ringKrullDim_quotient_affineVanishingIdeal (Set.singleton_nonempty a)
  have hzero : ringKrullDim (MvPolynomial (Fin n) K ⧸
      affineVanishingIdeal ({a} : Set (Fin n → K))) = 0 :=
    ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 ‹_›)
  have hk0 : k = 0 := by
    have hz := hzero.symm.trans hk
    exact_mod_cast hz.symm
  omega

end Dimension

/-! ## The zero set of two forms vanishing at the origin

`dim Z(A,B)` is bounded from below by `n + 1 - 2` through Krull's height theorem: every minimal
prime over `(A,B)` has height at most `2`, and for a polynomial ring the dimension of the quotient
by a prime is the dimension of the ring minus its height. Mathlib carries Krull's height theorem in
the equivalent *dimension* form `Ideal.height_le_ringKrullDim_quotient_add_encard` — for a prime
`p` containing a set `s`, `height p ≤ dim (R / (s)) + #s` — which is the form used here; it needs
no separate statement about the dimension of `R / P`, only that the maximal ideal of the origin has
height `n + 1`. -/

section ZeroSetOfPair

variable {K : Type*} [Field K] {m : ℕ}

/-- **The ideal of the origin has height at least the number of variables.** Killing the variables
one at a time exhibits a strictly increasing chain of `m + 1` primes of `K[x₀, …, x_{m-1}]` ending
at the ideal of functions vanishing at the origin: the `k`-th is the kernel of the substitution
sending `x₀, …, x_{k-1}` to `0`, a prime because the target is a domain. -/
theorem le_height_ker_eval_zero (K : Type*) [Field K] (m : ℕ) :
    (m : ℕ∞) ≤ (RingHom.ker (eval (0 : Fin m → K))).height := by
  classical
  let φ : ℕ → (MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :=
    fun k => aeval fun i => if (i : ℕ) < k then 0 else X i
  have hφX : ∀ (k : ℕ) (i : Fin m), φ k (X i) = if (i : ℕ) < k then 0 else X i := by
    intro k i; simp [φ]
  have hprime : ∀ k, (RingHom.ker (φ k)).IsPrime := fun k => RingHom.ker_isPrime _
  have hstep : ∀ k : ℕ, (φ (k + 1)) =
      (aeval fun i : Fin m => if (i : ℕ) = k then 0 else X i).comp (φ k) := by
    intro k
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, hφX, hφX]
    by_cases h1 : (i : ℕ) < k
    · rw [ite_eq_left h1, ite_eq_left (by omega), map_zero]
    · by_cases h2 : (i : ℕ) = k
      · rw [ite_eq_right h1, ite_eq_left (by omega), aeval_X, ite_eq_left h2]
      · rw [ite_eq_right h1, ite_eq_right (by omega), aeval_X, ite_eq_right h2]
  have hsub : ∀ k : ℕ, RingHom.ker (φ k) ≤ RingHom.ker (φ (k + 1)) := by
    intro k F hF
    rw [RingHom.mem_ker] at hF ⊢
    rw [hstep k, AlgHom.comp_apply, hF, map_zero]
  have hlt : ∀ k : ℕ, k < m → RingHom.ker (φ k) < RingHom.ker (φ (k + 1)) := by
    intro k hk
    refine lt_of_le_of_ne (hsub k) fun heq => ?_
    have h1 : (X (⟨k, hk⟩ : Fin m) : MvPolynomial (Fin m) K) ∈ RingHom.ker (φ (k + 1)) := by
      rw [RingHom.mem_ker, hφX, ite_eq_left (by simp)]
    rw [← heq, RingHom.mem_ker, hφX, ite_eq_right (by simp)] at h1
    exact X_ne_zero _ h1
  have hheight : ∀ k : ℕ, k ≤ m → (k : ℕ∞) ≤ (RingHom.ker (φ k)).height := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ j hj =>
        intro hjm
        have := hprime j
        have := hprime (j + 1)
        have h1 : (RingHom.ker (φ j)).height + 1 ≤ (RingHom.ker (φ (j + 1))).height :=
          Ideal.height_add_one_le_of_lt_of_isPrime (hlt j (by omega))
        have h2 := hj (by omega)
        calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; ring
          _ ≤ (RingHom.ker (φ j)).height + 1 := by gcongr
          _ ≤ _ := h1
  have hlast : RingHom.ker (φ m) = RingHom.ker (eval (0 : Fin m → K)) := by
    have hcomp : ((φ m : MvPolynomial (Fin m) K →+* MvPolynomial (Fin m) K)) =
        (C : K →+* MvPolynomial (Fin m) K).comp (eval (0 : Fin m → K)) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
      · simp [φ]
      · rw [RingHom.comp_apply, eval_X]
        simpa using hφX m i
    ext F
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change (φ m : MvPolynomial (Fin m) K →+* MvPolynomial (Fin m) K) F = 0 ↔ _
    rw [hcomp, RingHom.comp_apply]
    exact C_eq_zero
  rw [← hlast]
  exact hheight m le_rfl

/-- **Two polynomials vanishing at the origin cut out a set of codimension at most two.** Over an
algebraically closed field the affine zero set of `(A, B) ⊆ K[x₀, …, x_{m-1}]` has dimension at
least `c` whenever `c + 2 ≤ m`.

Krull's height theorem bounds the height of the ideal of the origin — which is at least `m` — by
the dimension of `K[x]/(A,B)` plus two, and the Nullstellensatz identifies the vanishing ideal of
the zero set with the radical of `(A, B)`, which has the same primes. -/
theorem le_affineDim_affineZeroLocus_span_pair [IsAlgClosed K] {A B : MvPolynomial (Fin m) K}
    (hA : eval 0 A = 0) (hB : eval 0 B = 0) {c : ℕ} (hc : c + 2 ≤ m) :
    (c : ℤ) ≤ affineDim (affineZeroLocus (Ideal.span {A, B})) := by
  classical
  have hpp : (RingHom.ker (eval (0 : Fin m → K))).IsPrime := RingHom.ker_isPrime _
  have hsubset : ({A, B} : Set (MvPolynomial (Fin m) K)) ⊆ RingHom.ker (eval (0 : Fin m → K)) := by
    intro G hG
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    refine RingHom.mem_ker.2 ?_
    rcases hG with h | h
    · rw [h]; exact hA
    · rw [h]; exact hB
  have hkrull := Ideal.height_le_ringKrullDim_quotient_add_encard
    (p := RingHom.ker (eval (0 : Fin m → K))) ({A, B} : Set (MvPolynomial (Fin m) K)) hsubset
  have hcard : ({A, B} : Set (MvPolynomial (Fin m) K)).encard ≤ 2 := by
    refine (Set.encard_insert_le _ _).trans ?_
    rw [Set.encard_singleton]
    norm_num
  have hm := le_height_ker_eval_zero K m
  have hrad : ringKrullDim (MvPolynomial (Fin m) K ⧸
        (Ideal.span ({A, B} : Set (MvPolynomial (Fin m) K))).radical)
      = ringKrullDim (MvPolynomial (Fin m) K ⧸
        Ideal.span ({A, B} : Set (MvPolynomial (Fin m) K))) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  refine le_affineDim_of_le_ringKrullDim ?_
  rw [affineVanishingIdeal_affineZeroLocus_eq_radical, hrad]
  set d := ringKrullDim (MvPolynomial (Fin m) K ⧸
    Ideal.span ({A, B} : Set (MvPolynomial (Fin m) K))) with hd
  have hmd : ((m : ℕ∞) : WithBot ℕ∞) ≤ d + 2 := by
    refine le_trans (by exact_mod_cast hm) (le_trans hkrull ?_)
    have h2 : ((({A, B} : Set (MvPolynomial (Fin m) K)).encard : ℕ∞) : WithBot ℕ∞)
        ≤ ((2 : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.2 hcard
    simpa using add_le_add (le_refl d) h2
  cases hcase : d with
  | bot => rw [hcase] at hmd; simp at hmd
  | coe e =>
      rw [hcase] at hmd
      have hme : (m : ℕ∞) ≤ e + 2 := by
        have h2 : ((e + 2 : ℕ∞) : WithBot ℕ∞) = (e : WithBot ℕ∞) + 2 := by
          rw [WithBot.coe_add]; norm_num
        rw [← h2] at hmd
        exact_mod_cast hmd
      have hce : (c : ℕ∞) ≤ e := by
        cases e with
        | top => exact le_top
        | coe j =>
            have hmj : m ≤ j + 2 := by exact_mod_cast hme
            exact_mod_cast (by omega : c ≤ j)
      exact_mod_cast hce

end ZeroSetOfPair

/-! ## Reducible forms are singular in dimension at least one -/

variable {n : ℕ}

/-- **Reducible forms are singular in dimension at least one** (`lem_reducible_sing`). For `n ≥ 3`,
a nonzero reducible form `F ∈ ℂ[x₀, …, x_n]` of positive degree satisfies `dim Sing X_F ≥ 1`.

Write `F = A B` with both factors non-units; by `lem_homogeneous_factors` each is homogeneous, and
being a non-unit each has positive degree, so each vanishes at the origin. The affine zero set
`Z ⊆ 𝔸ⁿ⁺¹` of `(A, B)` therefore has dimension at least `n + 1 - 2 ≥ 2` by
`le_affineDim_affineZeroLocus_span_pair`; in particular `Z` is not just the origin. At a nonzero
point of `Z` both `A` and `B` vanish, hence so do `F = A B` and, by the product rule, every
`∂ᵢF = A ∂ᵢB + B ∂ᵢA`, so by `lem_proj_sing_equations` the corresponding point of `ℙⁿ` lies in
`Sing X_F`. Since `A` and `B` are homogeneous, `Z` is stable under scaling, so `Z` is contained in
the affine cone over `Sing X_F`, whose dimension is therefore at least `2`; and `dim Sing X_F` is
one less than that. No coprimality of `A` and `B` is used, so a repeated factor is covered. -/
@[browning_sawin "lem_reducible_sing"]
theorem one_le_projDim_singularLocus_of_not_irreducible (hjac : AffineJacobianCriterion.{0})
    (hn : 3 ≤ n) {d : ℕ}
    {F : MvPolynomial (Fin (n + 1)) ℂ} (hF : F.IsHomogeneous d) (hd : 0 < d) (hF0 : F ≠ 0)
    (hirr : ¬Irreducible F) : 1 ≤ projDim (singularLocus F) := by
  classical
  obtain ⟨A, B, hAB, hAu, hBu⟩ : ∃ A B, F = A * B ∧ ¬IsUnit A ∧ ¬IsUnit B := by
    rw [irreducible_iff] at hirr
    push Not at hirr
    exact hirr (not_isUnit_of_isHomogeneous hF hF0 hd)
  have hA0 : A ≠ 0 := by rintro rfl; rw [zero_mul] at hAB; exact hF0 hAB
  have hB0 : B ≠ 0 := by rintro rfl; rw [mul_zero] at hAB; exact hF0 hAB
  have hprod : (A * B).IsHomogeneous d := hAB ▸ hF
  have hAh : A.IsHomogeneous A.totalDegree := hprod.isHomogeneous_left_of_mul hA0 hB0
  have hBh : B.IsHomogeneous B.totalDegree := hprod.isHomogeneous_right_of_mul hA0 hB0
  have hApos : 0 < A.totalDegree := by
    rcases Nat.eq_zero_or_pos A.totalDegree with h | h
    · exact absurd (isUnit_of_totalDegree_eq_zero hA0 h) hAu
    · exact h
  have hBpos : 0 < B.totalDegree := by
    rcases Nat.eq_zero_or_pos B.totalDegree with h | h
    · exact absurd (isUnit_of_totalDegree_eq_zero hB0 h) hBu
    · exact h
  set K := AlgebraicClosure ℂ
  set φ := algebraMap ℂ K with hφ
  set A' : MvPolynomial (Fin (n + 1)) K := A.map φ with hA'
  set B' : MvPolynomial (Fin (n + 1)) K := B.map φ with hB'
  have hA'h : A'.IsHomogeneous A.totalDegree := hAh.map _
  have hB'h : B'.IsHomogeneous B.totalDegree := hBh.map _
  have hA'0 : eval 0 A' = 0 := eval_zero_of_isHomogeneous hA'h hApos
  have hB'0 : eval 0 B' = 0 := eval_zero_of_isHomogeneous hB'h hBpos
  set Z := affineZeroLocus (Ideal.span ({A', B'} : Set (MvPolynomial (Fin (n + 1)) K))) with hZ
  have hZ2 : (2 : ℤ) ≤ affineDim Z :=
    le_affineDim_affineZeroLocus_span_pair hA'0 hB'0 (c := 2) (by omega)
  have hmemA : ∀ z ∈ Z, eval z A' = 0 := fun z hz => hz A' (Ideal.subset_span (by simp))
  have hmemB : ∀ z ∈ Z, eval z B' = 0 := fun z hz => hz B' (Ideal.subset_span (by simp))
  have hzero : (0 : Fin (n + 1) → K) ∈ Z := by
    intro G hG
    refine (Ideal.span_le.2 ?_ : Ideal.span ({A', B'} : Set (MvPolynomial (Fin (n + 1)) K))
      ≤ RingHom.ker (eval (0 : Fin (n + 1) → K))) hG
    intro G' hG'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG'
    refine RingHom.mem_ker.2 ?_
    rcases hG' with h | h
    · rw [h]; exact hA'0
    · rw [h]; exact hB'0
  have hsing : ∀ z ∈ Z, ∀ hz : z ≠ 0,
      Projectivization.mk K z hz ∈ singularLocus F ∧
        ∃ c : K, z = c • (Projectivization.mk K z hz).rep := by
    intro z hzZ hz
    set P := Projectivization.mk K z hz with hP
    obtain ⟨u, hu⟩ : ∃ u : Kˣ, u • z = P.rep := by
      rw [← Projectivization.mk_eq_mk_iff K P.rep z P.rep_nonzero hz, hP,
        Projectivization.mk_rep]
    have hAP : eval P.rep A' = 0 := by
      rw [← hu, Units.smul_def, eval_smul_of_isHomogeneous hA'h, hmemA z hzZ, mul_zero]
    have hBP : eval P.rep B' = 0 := by
      rw [← hu, Units.smul_def, eval_smul_of_isHomogeneous hB'h, hmemB z hzZ, mul_zero]
    refine ⟨(mem_singularLocus_iff hjac hF0 P).2 ⟨?_, fun i => ?_⟩, (u⁻¹ : Kˣ), ?_⟩
    · rw [hAB, toClosure, map_mul, eval_mul, hAP, zero_mul]
    · rw [hAB, pderiv_mul, toClosure, map_add, map_mul, map_mul, eval_add, eval_mul, eval_mul,
        hAP, hBP, zero_mul, mul_zero, add_zero]
    · rw [← hu]
      simp [Units.smul_def, smul_smul]
  have hne : ∃ z ∈ Z, z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hZeq : Z = {(0 : Fin (n + 1) → K)} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨hzero, fun z hz => hcon z hz⟩
    rw [hZeq] at hZ2
    have hs := affineDim_singleton_le (0 : Fin (n + 1) → K)
    omega
  obtain ⟨z₀, hz₀Z, hz₀⟩ := hne
  have hsubcone : Z ⊆ affineCone (singularLocus F) := by
    intro z hzZ
    by_cases hz : z = 0
    · obtain ⟨hP₀, -⟩ := hsing z₀ hz₀Z hz₀
      exact ⟨_, hP₀, 0, by rw [hz, zero_smul]⟩
    · obtain ⟨hP, c, hc⟩ := hsing z hzZ hz
      exact ⟨_, hP, c, hc⟩
  have hcone := affineDim_mono hsubcone
  rw [projDim]
  refine le_trans ?_ (le_max_right (-1 : ℤ) _)
  omega

/-! ## Projective sets with finitely many points

A positive-dimensional `Sing X_F` is read off one of the `n + 1` standard affine charts. Mathlib
carries no Zariski topology on classical projective space, so "the chart meets a component of
dimension at least one in a dense open subset" is taken in the contrapositive form that needs no
topology: if every chart meets `Sing X_F` in a *finite* set then `Sing X_F` is finite, and a finite
projective set has dimension at most `0`, its cone being a finite union of lines. -/

section FiniteProjective

variable {K : Type*} [Field K] {n : ℕ}

/-- Replacing an affine algebraic set by the zero locus of its vanishing ideal — its Zariski
closure — does not change its dimension: the vanishing ideal is radical, so the Nullstellensatz
returns it unchanged. -/
theorem affineDim_affineZeroLocus_affineVanishingIdeal [IsAlgClosed K] (V : Set (Fin n → K)) :
    affineDim (affineZeroLocus (affineVanishingIdeal V)) = affineDim V := by
  rw [affineDim, affineDim, affineVanishingIdeal_affineZeroLocus_eq_radical,
    (isRadical_affineVanishingIdeal V).radical]

/-- **A line through the origin has dimension at most one.** The affine cone over a single
projective point is the image of `𝔸¹` under the linear parametrization `c ↦ c v`, and that
parametrization is a bijection onto the cone, so the coordinate ring of the cone is a polynomial
ring in one variable. -/
theorem affineDim_affineCone_singleton_le_one [Infinite K]
    (P : Projectivization K (Fin (n + 1) → K)) : affineDim (affineCone {P}) ≤ 1 := by
  classical
  set v : Fin (n + 1) → K := P.rep with hv
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact P.rep_nonzero (funext hcon)
  set ψ : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin 1) K :=
    aeval (fun l : Fin (n + 1) => C (v l) * X 0) with hψ
  have hev : ∀ (F : MvPolynomial (Fin (n + 1)) K) (c : K),
      eval (fun _ : Fin 1 => c) (ψ F) = eval (c • v) F := by
    intro F c
    have h := MvPolynomial.comp_aeval
      (f := fun l : Fin (n + 1) => (C (v l) * X 0 : MvPolynomial (Fin 1) K))
      (φ := (aeval (fun _ : Fin 1 => c) : MvPolynomial (Fin 1) K →ₐ[K] K))
    have h2 := congrArg (fun τ => τ F) h
    simp only [AlgHom.coe_comp, Function.comp_apply] at h2
    have hfun : (fun l => v l * c) = c • v := by
      funext l; simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    simpa [hψ, hfun] using h2
  have hker : affineVanishingIdeal (affineCone ({P} : Set (Projectivization K (Fin (n + 1) → K))))
      = RingHom.ker ψ := by
    ext F
    rw [mem_affineVanishingIdeal, RingHom.mem_ker]
    constructor
    · intro h
      refine MvPolynomial.funext fun x => ?_
      rw [map_zero]
      have hx : x = fun _ : Fin 1 => x 0 := by funext l; rw [Subsingleton.elim l 0]
      rw [hx, hev]
      exact h _ ⟨P, rfl, x 0, rfl⟩
    · rintro h a ⟨Q, hQ, c, rfl⟩
      rw [Set.mem_singleton_iff] at hQ
      subst hQ
      rw [← hv, ← hev F c, h, map_zero]
  have hsurj : Function.Surjective ψ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← MvPolynomial.adjoin_range_X (σ := Fin 1) (R := K)]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨l, rfl⟩
    refine ⟨C ((v j)⁻¹) * X j, ?_⟩
    have hl : l = 0 := Subsingleton.elim _ _
    subst hl
    change ψ (C ((v j)⁻¹) * X j) = X 0
    have hcomp : ψ (C ((v j)⁻¹) * X j) = C ((v j)⁻¹) * (C (v j) * X 0) := by simp [hψ]
    rw [hcomp, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hj, C_1, one_mul]
  have hone : ((1 : ℕ) : ℤ) = 1 := by norm_num
  rw [← hone, affineDim_le_iff, hker,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- **A projective set with finitely many points has dimension at most zero.** Its affine cone is a
finite union of lines through the origin, and a prime over an intersection of finitely many ideals
contains one of them, so every irreducible component of the cone sits inside a single line. -/
theorem projDim_le_zero_of_finite [IsAlgClosed K] [Infinite K]
    {T : Set (Projectivization K (Fin (n + 1) → K))} (hT : T.Finite) : projDim T ≤ 0 := by
  classical
  set fam : Projectivization K (Fin (n + 1) → K) → Ideal (MvPolynomial (Fin (n + 1)) K) :=
    fun P => affineVanishingIdeal (affineCone ({P} : Set (Projectivization K (Fin (n + 1) → K))))
    with hfam
  set s := hT.toFinset with hs
  have hone : ((1 : ℕ) : ℤ) = 1 := by norm_num
  have hcone : affineDim (affineCone T) ≤ 1 := by
    rw [← hone]
    refine affineDim_le_of_forall_minimalPrimes fun Q hQ => ?_
    have hQp : Q.IsPrime := hQ.1.1
    have hinf : s.inf fam ≤ Q := by
      refine le_trans ?_ hQ.1.2
      intro F hF
      rw [mem_affineVanishingIdeal]
      rintro a ⟨P, hPT, c, rfl⟩
      have hPs : P ∈ s := by rw [hs, Set.Finite.mem_toFinset]; exact hPT
      have hmem : F ∈ fam P := (Finset.inf_le hPs : s.inf fam ≤ fam P) hF
      rw [hfam, mem_affineVanishingIdeal] at hmem
      exact hmem _ ⟨P, rfl, c, rfl⟩
    obtain ⟨P, -, hPQ⟩ := hQp.inf_le'.1 hinf
    calc affineDim (affineZeroLocus Q)
        ≤ affineDim (affineZeroLocus (fam P)) := affineDim_mono fun a ha G hG => ha G (hPQ hG)
      _ = affineDim (affineCone ({P} : Set (Projectivization K (Fin (n + 1) → K)))) :=
          affineDim_affineZeroLocus_affineVanishingIdeal _
      _ ≤ ((1 : ℕ) : ℤ) := by rw [hone]; exact affineDim_affineCone_singleton_le_one P
  rw [projDim]
  omega

end FiniteProjective

/-! ## A positive-dimensional singular locus is seen on a chart -/

section Charts

variable {k : Type u} [Field k] {n : ℕ}

/-- The trace on the `i`-th standard affine chart of the affine cone over a projective set: the
points `a` of `𝔸ⁿ` whose lift with `i`-th coordinate `1` lies on the cone. -/
def chartTrace (i : Fin (n + 1))
    (T : Set (Projectivization (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k))) :
    Set (Fin n → AlgebraicClosure k) :=
  {a | (Fin.insertNth i 1 a : Fin (n + 1) → AlgebraicClosure k) ∈ affineCone T}

/-- A vector with a coordinate equal to `1` is nonzero. -/
theorem insertNth_one_ne_zero (i : Fin (n + 1)) (a : Fin n → AlgebraicClosure k) :
    (Fin.insertNth i 1 a : Fin (n + 1) → AlgebraicClosure k) ≠ 0 := by
  intro h
  have h1 := congrFun h i
  rw [Fin.insertNth_apply_same] at h1
  exact one_ne_zero h1

/-- **A projective set whose every chart trace is finite is finite.** Every projective point has a
nonzero coordinate, and scaling that coordinate to `1` presents the point on the corresponding
chart. -/
theorem finite_of_forall_finite_chartTrace
    {T : Set (Projectivization (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k))}
    (h : ∀ i : Fin (n + 1), (chartTrace i T).Finite) : T.Finite := by
  classical
  refine Set.Finite.subset (Set.finite_iUnion (fun i : Fin (n + 1) =>
    (h i).image (fun a => Projectivization.mk (AlgebraicClosure k)
      (Fin.insertNth i 1 a : Fin (n + 1) → AlgebraicClosure k)
      (insertNth_one_ne_zero i a)))) ?_
  intro P hP
  obtain ⟨i, hi⟩ : ∃ i, P.rep i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact P.rep_nonzero (funext hcon)
  set v : Fin (n + 1) → AlgebraicClosure k := (P.rep i)⁻¹ • P.rep with hvdef
  have hvi : v i = 1 := by rw [hvdef]; simpa using inv_mul_cancel₀ hi
  have hins : (Fin.insertNth i 1 (Fin.removeNth i v) : Fin (n + 1) → AlgebraicClosure k) = v := by
    rw [← hvi]; exact Fin.insertNth_self_removeNth i v
  refine Set.mem_iUnion.2 ⟨i, Fin.removeNth i v, ?_, ?_⟩
  · rw [chartTrace, Set.mem_ofPred_eq, hins]
    exact ⟨P, hP, (P.rep i)⁻¹, rfl⟩
  · conv_rhs => rw [← Projectivization.mk_rep P]
    exact (Projectivization.mk_eq_mk_iff _ _ _ _ _).2
      ⟨Units.mk0 ((P.rep i)⁻¹) (inv_ne_zero hi), by rw [hins, hvdef]; rfl⟩

/-- **The chart trace of a singular locus is critical for the dehomogenization.** At a point of the
cone over `Sing X_F` whose `i`-th coordinate is `1` every partial derivative of `F` vanishes, by
`lem_proj_sing_equations` and the homogeneity of `∂F`, and dehomogenizing along the `i`-th chart
turns those equations into the vanishing of the partial derivatives of the dehomogenization. -/
theorem chartTrace_singularLocus_subset_criticalLocus (hjac : AffineJacobianCriterion.{u})
    [PerfectField k] {d : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF0 : F ≠ 0) (hF : F.IsHomogeneous d)
    (i : Fin (n + 1)) :
    chartTrace i (singularLocus F) ⊆ criticalLocus (dehomogenize k i F) n := by
  intro a ha
  obtain ⟨P, hP, c, hc⟩ := ha
  obtain ⟨-, hpd⟩ := (mem_singularLocus_iff hjac hF0 P).1 hP
  intro j _
  rw [← dehomogenize_pderiv, eval_map_dehomogenize, hc]
  have hhom : ((pderiv (i.succAbove j) F).map
      (algebraMap k (AlgebraicClosure k))).IsHomogeneous (d - 1) := hF.pderiv.map _
  rw [eval_smul_of_isHomogeneous hhom]
  have hz := hpd (i.succAbove j)
  rw [toClosure] at hz
  rw [hz, mul_zero]

/-- **A positive-dimensional singular locus is seen on some chart.** If `dim Sing X_F ≥ 1` then on
one of the `n + 1` standard affine charts the critical locus `W_n` of the dehomogenization has
positive dimension.

Contrapositively: if every `W_n` has dimension at most `0` then it is finite, hence so is each
chart trace of `Sing X_F`, hence `Sing X_F` itself is finite and `dim Sing X_F ≤ 0`. -/
theorem exists_zero_lt_affineDim_criticalLocus_dehomogenize (hjac : AffineJacobianCriterion.{u})
    [PerfectField k] {d : ℕ}
    {F : MvPolynomial (Fin (n + 1)) k} (hF0 : F ≠ 0) (hF : F.IsHomogeneous d)
    (hdim : 1 ≤ projDim (singularLocus F)) :
    ∃ i : Fin (n + 1), 0 < affineDim (criticalLocus (dehomogenize k i F) n) := by
  by_contra hcon
  push Not at hcon
  have hfin : ∀ i : Fin (n + 1), (chartTrace i (singularLocus F)).Finite := fun i =>
    Set.Finite.subset (finite_of_affineDim_nonpos (V := criticalLocus (dehomogenize k i F) n)
      (by have := hcon i; omega)) (chartTrace_singularLocus_subset_criticalLocus hjac hF0 hF i)
  have hle := projDim_le_zero_of_finite (finite_of_forall_finite_chartTrace hfin)
  omega

end Charts

/-! ## Positive-dimensional singular loci -/

section Positive

open MeasureTheory
open scoped ENNReal

variable {n d : ℕ}

/-- The random sign form is homogeneous of degree `d`. -/
theorem isHomogeneous_signForm (ε : SignFamily (monomialsEq (n + 1) d)) :
    (signForm n d ε).IsHomogeneous d := by
  rw [signForm]
  refine (mem_homogeneousSubmodule _ _).1 (Submodule.sum_mem _ fun α hα => ?_)
  exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (mem_monomialsEq.1 hα))

/-- Every value of the random sign form lies in `𝓑_{d,n}`. -/
theorem mem_signFormSet_signForm (ε : SignFamily (monomialsEq (n + 1) d)) :
    signForm n d ε ∈ signFormSet n d := by
  refine ⟨fun α hα => ?_, fun α hα => ?_⟩
  · rw [signForm, coeff_sum]
    refine Finset.sum_eq_zero fun β hβ => ?_
    rw [coeff_monomial, ite_eq_right]
    rintro rfl
    exact hα (mem_monomialsEq.1 hβ)
  · rw [coeff_signForm _ hα]
    rcases Int.units_eq_one_or (signOf ε α) with h | h <;> simp [h]

/-- `∑_{i<n} D^i ≤ n d^{n-1}`, a crude bound on the Bézout sum: there are `n` terms and each is at
most `d^{n-1}`, since `D = d - 1 ≤ d`. -/
theorem sum_pow_pderivDegBound_le (hd : 1 ≤ d) (n : ℕ) :
    (∑ j ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ j) ≤ (n : ℝ≥0∞) * (d : ℝ≥0∞) ^ (n - 1) := by
  have hDd : ((pderivDegBound d : ℕ) : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by
    exact_mod_cast Nat.sub_le d 1
  have h1d : (1 : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by exact_mod_cast hd
  refine le_trans (Finset.sum_le_card_nsmul _ _ ((d : ℝ≥0∞) ^ (n - 1)) fun j hj => ?_) ?_
  · have hjn : j ≤ n - 1 := by rw [Finset.mem_range] at hj; omega
    calc ((pderivDegBound d : ℕ) : ℝ≥0∞) ^ j ≤ (d : ℝ≥0∞) ^ j := by gcongr
      _ ≤ (d : ℝ≥0∞) ^ (n - 1) := pow_le_pow_right₀ h1d hjn
  · rw [Finset.card_range, nsmul_eq_mul]

/-- **Positive-dimensional singular loci** (`thm_positive`). For `n ≥ 1` and `d ≥ 3`,
`P(dim Sing X_f ≥ 1) ≤ n(n+1) d^{n-1} 2^{-⌊(d-1)/3⌋-1}` over `ℂ`, conditional on `CitedResults`,
the results the source defers to the literature.

Work first over `𝔽̄₃`. Every value of `f` is primitive (`lem_sign_form_primitive`), so
`lem_sing_specialization` bounds the complex singular dimension by the one modulo `3`; if the
latter is at least `1` then by `exists_zero_lt_affineDim_criticalLocus_dehomogenize` one of the
`n + 1` standard affine charts sees a critical locus `W_n` of positive dimension. On each chart
`lem_dehomog_model` identifies the dehomogenization with the affine sign polynomial `g` — the
identification is a measure-preserving relabelling of the signs — so `prop_critical` charges that
chart `(∑_{i<n} D^i) 2^{-(s+1)}`, and a union bound over the `n + 1` charts costs a factor `n + 1`.
Finally `∑_{i<n} D^i ≤ n d^{n-1}` and `s = ⌊(d-1)/3⌋`. -/
@[browning_sawin "thm_positive"]
theorem signMeasure_one_le_projDim_singularLocus_le (hcited : CitedResults.{0}) (hn : 1 ≤ n)
    (hd : 3 ≤ d) :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | 1 ≤ projDim (singularLocus ((signForm n d ε).map (Int.castRingHom ℂ)))}
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ (n - 1)
          * ((2 : ℝ≥0∞) ^ ((d - 1) / 3 + 1))⁻¹ := by
  classical
  obtain ⟨hbez, hdrop, hsemi, hjac, hhs⟩ := hcited
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set A : Fin (n + 1) → Set (SignFamily (monomialsEq (n + 1) d)) := fun i =>
    {ε | 0 < affineDim (criticalLocus
      (dehomogenize (ZMod 3) i ((signForm n d ε).map (Int.castRingHom (ZMod 3)))) n)} with hA
  have hsub : {ε : SignFamily (monomialsEq (n + 1) d) |
      1 ≤ projDim (singularLocus ((signForm n d ε).map (Int.castRingHom ℂ)))} ⊆ ⋃ i, A i := by
    intro ε hε
    have hmem := mem_signFormSet_signForm (n := n) (d := d) ε
    have hhom := isHomogeneous_signForm (n := n) (d := d) ε
    have hzmod : 1 ≤ projDim (singularLocus ((signForm n d ε).map (Int.castRingHom (ZMod 3)))) :=
      le_trans hε (projDim_singularLocus_complex_le_zmod hsemi hjac hhom
        (gcd_coeff_eq_one_of_mem_signFormSet hmem) 3)
    obtain ⟨i, hi⟩ := exists_zero_lt_affineDim_criticalLocus_dehomogenize hjac
      (map_intCast_ne_zero_of_mem_signFormSet hmem (by norm_num))
      (hhom.map (Int.castRingHom (ZMod 3))) hzmod
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  have hchart : ∀ i : Fin (n + 1), signMeasure ↥(monomialsEq (n + 1) d) (A i)
      ≤ (∑ j ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ j) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength 3 d + 1))⁻¹ := by
    intro i
    set Φ := (chartTupleEquiv d i).arrowCongr (Equiv.refl ℤˣ) with hΦdef
    have hΦ : MeasurePreserving Φ (signMeasure ↥(monomialsEq (n + 1) d))
        (signMeasure ↥(monomialsLE n d)) := measurePreserving_signFamilyCongr _
    have hpre : A i ⊆ Φ ⁻¹' {δ : SignFamily (monomialsLE n d) |
        0 < affineDim (criticalLocus (affineSignPoly 3 n d δ) n)} := by
      intro ε hε
      rw [Set.mem_preimage, Set.mem_ofPred_eq, ← dehomogenize_map_signForm i ε]
      exact hε
    refine le_trans (measure_mono hpre) ?_
    rw [hΦ.measure_preimage (MeasurableSet.of_discrete).nullMeasurableSet]
    exact signMeasure_zero_lt_affineDim_criticalLocus_le hbez hdrop hhs (by decide) hn hd
  calc signMeasure ↥(monomialsEq (n + 1) d)
          {ε | 1 ≤ projDim (singularLocus ((signForm n d ε).map (Int.castRingHom ℂ)))}
      ≤ signMeasure ↥(monomialsEq (n + 1) d) (⋃ i, A i) := measure_mono hsub
    _ ≤ ∑ i : Fin (n + 1), signMeasure ↥(monomialsEq (n + 1) d) (A i) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (n + 1), (∑ j ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ j) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength 3 d + 1))⁻¹ := Finset.sum_le_sum fun i _ => hchart i
    _ = ((n : ℝ≥0∞) + 1) * ((∑ j ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ j) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength 3 d + 1))⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ((n : ℝ≥0∞) + 1) * ((n : ℝ≥0∞) * (d : ℝ≥0∞) ^ (n - 1) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength 3 d + 1))⁻¹) := by
        gcongr
        exact sum_pow_pderivDegBound_le (by omega) n
    _ = (n : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ (n - 1)
          * ((2 : ℝ≥0∞) ^ ((d - 1) / 3 + 1))⁻¹ := by
        rw [lowerBlockLength]
        ring

/-- **Absolute irreducibility** (`thm_absolute_irred`). For `n ≥ 3` and `d ≥ 3`,
`P(f is reducible over ℂ) ≤ n(n+1) d^{n-1} 2^{-⌊(d-1)/3⌋-1}`, conditional on `CitedResults`, the
results the source defers to the literature.

Every value of `f` is a nonzero form of degree `d ≥ 3`, so `lem_reducible_sing` puts every
reducible value inside the event `dim Sing X_f ≥ 1`, which `thm_positive` bounds. Since `f` has
integer coefficients, reducibility over `ℂ` is exactly the failure of absolute irreducibility. -/
@[browning_sawin "thm_absolute_irred"]
theorem signMeasure_not_irreducible_complex_le (hcited : CitedResults.{0}) (hn : 3 ≤ n)
    (hd : 3 ≤ d) :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | ¬ Irreducible ((signForm n d ε).map (Int.castRingHom ℂ))}
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ (n - 1)
          * ((2 : ℝ≥0∞) ^ ((d - 1) / 3 + 1))⁻¹ := by
  have hjac : AffineJacobianCriterion.{0} := hcited.2.2.2.1
  refine le_trans (measure_mono fun ε hε => ?_)
    (signMeasure_one_le_projDim_singularLocus_le hcited (by omega) hd)
  have hmem := mem_signFormSet_signForm (n := n) (d := d) ε
  have hhom := (isHomogeneous_signForm (n := n) (d := d) ε).map (Int.castRingHom ℂ)
  have hne : (signForm n d ε).map (Int.castRingHom ℂ) ≠ 0 := by
    intro h
    have h0 : signForm n d ε = 0 :=
      map_injective (Int.castRingHom ℂ) Int.cast_injective (by simpa using h)
    have h1 : (signForm n d ε).coeff (Finsupp.single 0 d) = 1 ∨
        (signForm n d ε).coeff (Finsupp.single 0 d) = -1 :=
      hmem.2 _ (by rw [Finsupp.degree_single])
    rw [h0] at h1
    rcases h1 with h | h <;> simp at h
  exact one_le_projDim_singularLocus_of_not_irreducible hjac hn hhom (by omega) hne hε

end Positive

/-! ## The quantitative smoothness bound

`thm_main` feeds `thm_finite` a prime `p ≍ √d`, produced by Bertrand's postulate, and the cut-off
`R = (n+2)(⌊log₂ d⌋ + 1)`, an arithmetic stand-in for `⌈(n+2) log₂ d⌉` with the same two
properties: `2^R ≥ d^{n+2}`, which kills both high-degree terms, and `R = O_n(log d)`, which keeps
the low-degree sum geometric.

The constants `A_n` and `B_n` of the source are `thetaConst` and `lowSumConst`. -/

section MainBound

open Filter Asymptotics MeasureTheory
open scoped ENNReal

/-- `A_n = 1 + √(2(n+1))`, the constant in the bound `Θ_{K_e}(p) ≤ A_n √(e/d)`. -/
private noncomputable def thetaConst (n : ℕ) : ℝ := 1 + Real.sqrt (2 * (n + 1))

/-- `B_n = 2^n A_n^{n+1}`, the base of the geometric bound for the `e`-th low-degree term. -/
private noncomputable def lowSumConst (n : ℕ) : ℝ := 2 ^ n * thetaConst n ^ (n + 1)

private theorem one_le_thetaConst (n : ℕ) : 1 ≤ thetaConst n := by
  have := Real.sqrt_nonneg (2 * ((n : ℝ) + 1))
  rw [thetaConst]
  linarith

private theorem one_le_lowSumConst (n : ℕ) : 1 ≤ lowSumConst n := by
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ thetaConst n ^ (n + 1) := one_le_pow₀ (one_le_thetaConst n)
  rw [lowSumConst]
  nlinarith

/-- **A power of the binary logarithm is eventually dominated by the square root.** For every
constant `c` and exponent `k` there is a threshold beyond which `c (⌊log₂ d⌋ + 1)^k ≤ √d`. -/
private theorem exists_forall_mul_pow_natLog_le_sqrt (c : ℝ) (k : ℕ) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → c * ((Nat.log 2 d : ℝ) + 1) ^ k ≤ Real.sqrt d := by
  have hc' : (0 : ℝ) < max c 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hio : (fun x : ℝ => Real.log x ^ k) =o[atTop] fun x : ℝ => Real.sqrt x := by
    have h := isLittleO_log_rpow_rpow_atTop (s := (1 / 2 : ℝ)) (k : ℝ) (by norm_num)
    simp only [Real.rpow_natCast] at h
    exact h.congr' (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun x => (Real.sqrt_eq_rpow x).symm)
  have h7 : (0 : ℝ) < max c 1 * 4 ^ k := by positivity
  obtain ⟨X, hX⟩ := eventually_atTop.1 (hio.def (c := (max c 1 * 4 ^ k)⁻¹) (by positivity))
  refine ⟨max 2 ⌈X⌉₊, fun d hd => ?_⟩
  have hd2 : 2 ≤ d := le_trans (le_max_left _ _) hd
  have hdX : X ≤ (d : ℝ) :=
    le_trans (Nat.le_ceil X) (by exact_mod_cast le_trans (le_max_right 2 _) hd)
  have hL1 : 1 ≤ Nat.log 2 d := Nat.log_pos (by norm_num) hd2
  have hdpos : (0 : ℝ) < d := by positivity
  have hpow : (2 : ℝ) ^ Nat.log 2 d ≤ (d : ℝ) := by
    have h := Nat.pow_log_le_self 2 (x := d) (by omega)
    exact_mod_cast h
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hLlog : (Nat.log 2 d : ℝ) * Real.log 2 ≤ Real.log d := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 d : ℝ) := Nat.cast_nonneg _
  have hLle : (Nat.log 2 d : ℝ) ≤ 2 * Real.log d := by nlinarith
  have h1le : (1 : ℝ) ≤ 2 * Real.log d := le_trans (by exact_mod_cast hL1) hLle
  have hbound : (Nat.log 2 d : ℝ) + 1 ≤ 4 * Real.log d := by linarith
  have hlogpos : (0 : ℝ) ≤ Real.log d := by linarith
  have hX0 : (0 : ℝ) ≤ (Nat.log 2 d : ℝ) + 1 := by positivity
  have hkey := hX (d : ℝ) hdX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlogpos k),
    abs_of_nonneg (Real.sqrt_nonneg _)] at hkey
  calc c * ((Nat.log 2 d : ℝ) + 1) ^ k
      ≤ max c 1 * ((Nat.log 2 d : ℝ) + 1) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hX0 k)
    _ ≤ max c 1 * (4 * Real.log d) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hbound k) hc'.le
    _ = max c 1 * 4 ^ k * Real.log d ^ k := by rw [mul_pow]; ring
    _ ≤ max c 1 * 4 ^ k * ((max c 1 * 4 ^ k)⁻¹ * Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hkey h7.le
    _ = Real.sqrt d := by field_simp

/-- The cosine average is a nonnegative quantity: it is an average of absolute values. -/
private theorem theta_nonneg (p K : ℕ) [NeZero p] : 0 ≤ theta p K :=
  div_nonneg (Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) K) (Nat.cast_nonneg p)

/-- **The cosine average at a closed point of degree `e`.** For `p > √d` and `(n+1)e ≤ d + 1`,
`Θ_{K_e}(p) ≤ A_n √(e/d)`.

`K_e = ⌊(d+1)/((n+1)e)⌋` is at least `1`, so it is at least half of `(d+1)/((n+1)e)`; feeding that
into `lem_theta_bound` and using `2/π ≤ 1` bounds the second term by `√(2(n+1)e/d)`, while `p > √d`
bounds the first by `1/√d ≤ √e/√d`. -/
private theorem theta_basisCount_le {n d e p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (hp1 : Real.sqrt d < p) (hd : 1 ≤ d) (he : 1 ≤ e) (hKe : (n + 1) * e ≤ d + 1) :
    theta p (basisCount n d e) ≤ thetaConst n * Real.sqrt e / Real.sqrt d := by
  have hm : 0 < (n + 1) * e := Nat.mul_pos (Nat.succ_pos n) he
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hKpos : 0 < basisCount n d e := (Nat.one_le_div_iff hm).2 hKe
  have hkey : d + 1 ≤ 2 * ((n + 1) * e * basisCount n d e) := by
    have h1 : (n + 1) * e * basisCount n d e + (d + 1) % ((n + 1) * e) = d + 1 :=
      Nat.div_add_mod _ _
    have h2 : (d + 1) % ((n + 1) * e) < (n + 1) * e := Nat.mod_lt _ hm
    have h3 : (n + 1) * e ≤ (n + 1) * e * basisCount n d e := Nat.le_mul_of_pos_right _ hKpos
    obtain ⟨P, hP⟩ : ∃ P, (n + 1) * e * basisCount n d e = P := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, (d + 1) % ((n + 1) * e) = r := ⟨_, rfl⟩
    rw [hP, hr] at h1
    rw [hr] at h2
    rw [hP] at h3
    rw [hP]
    omega
  have hKR : (0 : ℝ) < (basisCount n d e : ℝ) := by exact_mod_cast hKpos
  have heR : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have hpR : (0 : ℝ) < (p : ℝ) := lt_trans hsd hp1
  have hdle : (d : ℝ) ≤ 2 * (((n : ℝ) + 1) * e) * (basisCount n d e : ℝ) := by
    have h : ((d : ℝ) + 1) ≤ 2 * ((((n : ℝ) + 1) * e) * (basisCount n d e : ℝ)) := by
      have h0 : ((d + 1 : ℕ) : ℝ) ≤ ((2 * ((n + 1) * e * basisCount n d e) : ℕ) : ℝ) :=
        Nat.cast_le.2 hkey
      push_cast at h0
      linarith
    linarith
  have hA : 1 / (p : ℝ) ≤ Real.sqrt e / Real.sqrt d := by
    refine le_trans (one_div_le_one_div_of_le hsd hp1.le) ?_
    rw [div_le_div_iff_of_pos_right hsd]
    exact Real.one_le_sqrt.2 heR
  have hpi : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have harg : 2 / (Real.pi * (basisCount n d e : ℝ)) ≤ 2 * (((n : ℝ) + 1) * e) / d := by
    rw [div_le_div_iff₀ (by positivity) hdR]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ ((n:ℝ) + 1) * e) hKR.le)
      (by linarith : (0:ℝ) ≤ Real.pi - 2), hdle]
  have hsplit : Real.sqrt (2 * (((n : ℝ) + 1) * e) / d)
      = Real.sqrt (2 * ((n : ℝ) + 1)) * Real.sqrt e / Real.sqrt d := by
    rw [show 2 * (((n : ℝ) + 1) * e) / (d : ℝ) = 2 * ((n : ℝ) + 1) * (e : ℝ) / (d : ℝ) by ring,
      Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  have hB : Real.sqrt (2 / (Real.pi * (basisCount n d e : ℝ)))
      ≤ Real.sqrt (2 * ((n : ℝ) + 1)) * Real.sqrt e / Real.sqrt d := by
    rw [← hsplit]
    exact Real.sqrt_le_sqrt harg
  have hthm := theta_le_inv_add_sqrt (p := p) (K := basisCount n d e) hpodd hKpos
  have hpush : Real.sqrt (2 / (Real.pi * (basisCount n d e : ℕ)))
      = Real.sqrt (2 / (Real.pi * (basisCount n d e : ℝ))) := by norm_num
  rw [hpush] at hthm
  rw [thetaConst]
  calc theta p (basisCount n d e) ≤ 1 / (p : ℝ) + Real.sqrt (2 / (Real.pi * (basisCount n d e : ℝ)))
      := hthm
    _ ≤ Real.sqrt e / Real.sqrt d + Real.sqrt (2 * ((n : ℝ) + 1)) * Real.sqrt e / Real.sqrt d :=
        add_le_add hA hB
    _ = (1 + Real.sqrt (2 * ((n : ℝ) + 1))) * Real.sqrt e / Real.sqrt d := by ring

/-- **The low-degree sum of `thm_finite` is `O_n(d^{-1/2})`.** For `√d < p ≤ 2√d` and a cut-off `R`
small enough that `B_n² R^{n+1} ≤ √d`, the contribution of the closed points of degree at most `R`
is at most `(3/2)(B_n + 2) d^{-1/2}`.

`theta_basisCount_le` together with `p ≤ 2√d` makes the `e`-th term at most
`e⁻¹ (B_n (√e)^{n+1} d^{-1/2})^e`. The term `e = 1` is `B_n d^{-1/2}`; for `2 ≤ e ≤ R` the base is
at most `ρ = B_n (√R)^{n+1} d^{-1/2}`, which is at most `1/2`, so those terms are dominated by
`∑_{e ≥ 2} ρ^e ≤ 2ρ² ≤ 2 d^{-1/2}`. The prefactor `p/(p-1)` is at most `3/2` because `p ≥ 3`. -/
private theorem lowSum_le {n d R p : ℕ} [Fact p.Prime] (hd : 16 ≤ d) (hp1 : Real.sqrt d < p)
    (hp2 : (p : ℝ) ≤ 2 * Real.sqrt d) (hpodd : Odd p) (hp3 : 3 ≤ p) (hR2 : 2 ≤ R)
    (hRd : (n + 1) * R ≤ d + 1) (hρ : lowSumConst n ^ 2 * (R : ℝ) ^ (n + 1) ≤ Real.sqrt d) :
    (p : ℝ) / (p - 1) * ∑ e ∈ Finset.Icc 1 R,
        (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e)
      ≤ 3 / 2 * (lowSumConst n + 2) / Real.sqrt d := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsdne : Real.sqrt d ≠ 0 := ne_of_gt hsd
  have hsqd : Real.sqrt d ^ 2 = (d : ℝ) := Real.sq_sqrt hdR.le
  have hsqd' : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt hdR.le
  have hB1 := one_le_lowSumConst n
  have hB0 : (0 : ℝ) < lowSumConst n := lt_of_lt_of_le zero_lt_one hB1
  have hd16 : (16 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsd4 : (4 : ℝ) ≤ Real.sqrt d := by
    have h : Real.sqrt 16 ≤ Real.sqrt d := Real.sqrt_le_sqrt hd16
    rwa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hbase : ∀ e : ℕ, 0 ≤ lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d := fun e =>
    div_nonneg (mul_nonneg hB0.le (pow_nonneg (Real.sqrt_nonneg _) _)) hsd.le
  have hρ0 : (0 : ℝ) ≤ lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d := hbase R
  have hρsq : (lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d) ^ 2 ≤ 1 / Real.sqrt d := by
    have h1 : (Real.sqrt R ^ (n + 1)) ^ 2 = (R : ℝ) ^ (n + 1) := by
      rw [← pow_mul, mul_comm (n + 1) 2, pow_mul, Real.sq_sqrt (by positivity)]
    rw [div_pow, mul_pow, h1, hsqd, div_le_div_iff₀ hdR hsd]
    linarith [mul_le_mul_of_nonneg_right hρ hsd.le]
  have hρhalf : lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d ≤ 1 / 2 := by
    have h1 : (1 : ℝ) / Real.sqrt d ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hsd (by norm_num)]; linarith
    nlinarith [hρsq, hρ0]
  have hterm : ∀ e ∈ Finset.Icc 1 R,
      (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e)
        ≤ 1 / (e : ℝ) * (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e := by
    intro e he
    rw [Finset.mem_Icc] at he
    have hKe : (n + 1) * e ≤ d + 1 := le_trans (Nat.mul_le_mul_left _ he.2) hRd
    have hθ := theta_basisCount_le (n := n) (d := d) (e := e) (p := p) hpodd hp1 hd1 he.1 hKe
    have hθ0 : 0 ≤ theta p (basisCount n d e) := theta_nonneg _ _
    have h1 : (p : ℝ) ^ (n * e) ≤ ((2 * Real.sqrt d) ^ n) ^ e := by
      rw [← pow_mul]; exact pow_le_pow_left₀ (Nat.cast_nonneg p) hp2 (n * e)
    have h2 : theta p (basisCount n d e) ^ ((n + 1) * e)
        ≤ ((thetaConst n * Real.sqrt e / Real.sqrt d) ^ (n + 1)) ^ e := by
      rw [← pow_mul]; exact pow_le_pow_left₀ hθ0 hθ ((n + 1) * e)
    have h3 : ((2 * Real.sqrt d) ^ n) ^ e
          * ((thetaConst n * Real.sqrt e / Real.sqrt d) ^ (n + 1)) ^ e
        = (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e := by
      rw [← mul_pow]
      congr 1
      calc (2 * Real.sqrt d) ^ n * (thetaConst n * Real.sqrt e / Real.sqrt d) ^ (n + 1)
          = 2 ^ n * Real.sqrt d ^ n * (thetaConst n ^ (n + 1) * Real.sqrt e ^ (n + 1)
              / (Real.sqrt d ^ n * Real.sqrt d)) := by
            rw [mul_pow, div_pow, mul_pow, pow_succ (Real.sqrt (d : ℝ)) n]
        _ = Real.sqrt d ^ n * (2 ^ n * (thetaConst n ^ (n + 1) * Real.sqrt e ^ (n + 1)))
              / (Real.sqrt d ^ n * Real.sqrt d) := by ring
        _ = 2 ^ n * (thetaConst n ^ (n + 1) * Real.sqrt e ^ (n + 1)) / Real.sqrt d :=
            mul_div_mul_left _ _ (pow_ne_zero n hsdne)
        _ = lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d := by rw [lowSumConst]; ring
    calc (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e)
        = 1 / (e : ℝ) * ((p : ℝ) ^ (n * e) * theta p (basisCount n d e) ^ ((n + 1) * e)) := by
          ring
      _ ≤ 1 / (e : ℝ) * (((2 * Real.sqrt d) ^ n) ^ e
            * ((thetaConst n * Real.sqrt e / Real.sqrt d) ^ (n + 1)) ^ e) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul h1 h2 (pow_nonneg hθ0 _) (pow_nonneg (by positivity) _)
      _ = 1 / (e : ℝ) * (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e := by rw [h3]
  have hstep : ∀ e ∈ Finset.Ico 2 (R + 1),
      1 / (e : ℝ) * (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e
        ≤ (lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d) ^ e := by
    intro e he
    rw [Finset.mem_Ico] at he
    have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast (by omega : 1 ≤ e)
    have hmono : lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d
        ≤ lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d := by
      have hsq : Real.sqrt e ≤ Real.sqrt R :=
        Real.sqrt_le_sqrt (by exact_mod_cast (by omega : e ≤ R))
      have h6 := pow_le_pow_left₀ (Real.sqrt_nonneg (e : ℝ)) hsq (n + 1)
      exact (div_le_div_iff_of_pos_right hsd).2 (mul_le_mul_of_nonneg_left h6 hB0.le)
    have h4 := pow_le_pow_left₀ (hbase e) hmono e
    have h5 : 1 / (e : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    calc 1 / (e : ℝ) * (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e
        ≤ 1 * (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e :=
          mul_le_mul_of_nonneg_right h5 (pow_nonneg (hbase e) e)
      _ = (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e := one_mul _
      _ ≤ _ := h4
  have hgeom : ∑ e ∈ Finset.Ico 2 (R + 1),
        (lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d) ^ e ≤ 2 / Real.sqrt d := by
    set ρ := lowSumConst n * Real.sqrt R ^ (n + 1) / Real.sqrt d with hρd
    have hreindex : ∑ e ∈ Finset.Ico 2 (R + 1), ρ ^ e
        = ρ ^ 2 * ∑ j ∈ Finset.range (R - 1), ρ ^ j := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum, show R + 1 - 2 = R - 1 by omega]
      exact Finset.sum_congr rfl fun j _ => by rw [pow_add]
    have hlt1 : ρ < 1 := by linarith
    have hgs : ∑ j ∈ Finset.range (R - 1), ρ ^ j ≤ 2 := by
      refine le_trans (Summable.sum_le_tsum _ (fun j _ => pow_nonneg hρ0 j)
        (summable_geometric_of_lt_one hρ0 hlt1)) ?_
      rw [tsum_geometric_of_lt_one hρ0 hlt1, inv_eq_one_div,
        div_le_iff₀ (by linarith : (0 : ℝ) < 1 - ρ)]
      linarith
    rw [hreindex]
    calc ρ ^ 2 * ∑ j ∈ Finset.range (R - 1), ρ ^ j ≤ ρ ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left hgs (by positivity)
      _ ≤ 1 / Real.sqrt d * 2 := mul_le_mul_of_nonneg_right hρsq (by norm_num)
      _ = 2 / Real.sqrt d := by ring
  have hsumle : ∑ e ∈ Finset.Icc 1 R,
        (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e)
      ≤ (lowSumConst n + 2) / Real.sqrt d := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.Ico_add_one_right_eq_Icc 1 R,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < R + 1)]
    have hfirst : 1 / ((1 : ℕ) : ℝ)
        * (lowSumConst n * Real.sqrt ((1 : ℕ) : ℝ) ^ (n + 1) / Real.sqrt d) ^ 1
        = lowSumConst n / Real.sqrt d := by norm_num
    rw [show (1 : ℕ) + 1 = 2 from rfl, hfirst]
    have htail := le_trans (Finset.sum_le_sum hstep) hgeom
    calc lowSumConst n / Real.sqrt d
          + ∑ e ∈ Finset.Ico 2 (R + 1),
              1 / (e : ℝ) * (lowSumConst n * Real.sqrt e ^ (n + 1) / Real.sqrt d) ^ e
        ≤ lowSumConst n / Real.sqrt d + 2 / Real.sqrt d := by linarith
      _ = (lowSumConst n + 2) / Real.sqrt d := by ring
  have hsum0 : (0 : ℝ) ≤ ∑ e ∈ Finset.Icc 1 R,
      (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e) :=
    Finset.sum_nonneg fun e _ =>
      mul_nonneg (div_nonneg (by positivity) (by positivity)) (pow_nonneg (theta_nonneg _ _) _)
  have hpfrac : (p : ℝ) / ((p : ℝ) - 1) ≤ 3 / 2 := by
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  calc (p : ℝ) / ((p : ℝ) - 1) * ∑ e ∈ Finset.Icc 1 R,
          (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e)
      ≤ 3 / 2 * ∑ e ∈ Finset.Icc 1 R,
          (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e) :=
        mul_le_mul_of_nonneg_right hpfrac hsum0
    _ ≤ 3 / 2 * ((lowSumConst n + 2) / Real.sqrt d) :=
        mul_le_mul_of_nonneg_left hsumle (by norm_num)
    _ = 3 / 2 * (lowSumConst n + 2) / Real.sqrt d := by ring

/-- **The two high-degree terms of `thm_finite` are `O_n(d^{-2})`.** If `R ≤ s`, `R ≤ t` and
`d^{n+2} ≤ 2^R` then the bracketed expression, with its factor `n + 1`, is at most
`(n+1)² d^{-2} ≤ (n+1)² d^{-1/2}`.

`R ≤ s` and `R ≤ t` replace both `2^{-(s+1)}` and `2^{-min(t+1,R+1)}` by `2^{-R} ≤ d^{-(n+2)}`,
while the two numerators are at most `n d^{n-1}` and `d^n`. -/
private theorem highTerms_le {n d R s t : ℕ} (hd : 1 ≤ d) (hRs : R ≤ s) (hRt : R ≤ t)
    (h2R : d ^ (n + 2) ≤ 2 ^ R) :
    ((n : ℝ≥0∞) + 1) * ((∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
          * ((2 : ℝ≥0∞) ^ (s + 1))⁻¹
        + (pderivDegBound d : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ min (t + 1) (R + 1))⁻¹)
      ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / Real.sqrt d) := by
  have hd0 : (d : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hdtop : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hd1e : (1 : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by exact_mod_cast hd
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hkey : (d : ℝ≥0∞) ^ (n + 2) ≤ (2 : ℝ≥0∞) ^ R := by
    have h : ((d ^ (n + 2) : ℕ) : ℝ≥0∞) ≤ ((2 ^ R : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h2R
    push_cast at h
    exact h
  have hs : ((2 : ℝ≥0∞) ^ (s + 1))⁻¹ ≤ ((d : ℝ≥0∞) ^ (n + 2))⁻¹ :=
    ENNReal.inv_le_inv.2 (le_trans hkey (pow_le_pow_right₀ h2 (by omega)))
  have ht : ((2 : ℝ≥0∞) ^ min (t + 1) (R + 1))⁻¹ ≤ ((d : ℝ≥0∞) ^ (n + 2))⁻¹ :=
    ENNReal.inv_le_inv.2 (le_trans hkey (pow_le_pow_right₀ h2 (by omega)))
  have hnum2 : (pderivDegBound d : ℝ≥0∞) ^ n ≤ (d : ℝ≥0∞) ^ n := by
    gcongr
    exact_mod_cast Nat.sub_le d 1
  have hcancel : (d : ℝ≥0∞) ^ n * ((d : ℝ≥0∞) ^ (n + 2))⁻¹ = ((d : ℝ≥0∞) ^ 2)⁻¹ := by
    have hne1 : (d : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n hd0
    have hne2 : (d : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top hdtop
    rw [pow_add, ENNReal.mul_inv (Or.inl hne1) (Or.inl hne2), ← mul_assoc,
      ENNReal.mul_inv_cancel hne1 hne2, one_mul]
  have hbracket : (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
        * ((2 : ℝ≥0∞) ^ (s + 1))⁻¹
      + (pderivDegBound d : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ min (t + 1) (R + 1))⁻¹
      ≤ ((n : ℝ≥0∞) + 1) * ((d : ℝ≥0∞) ^ 2)⁻¹ := by
    have hdn : (d : ℝ≥0∞) ^ (n - 1) ≤ (d : ℝ≥0∞) ^ n := pow_le_pow_right₀ hd1e (by omega)
    calc (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i) * ((2 : ℝ≥0∞) ^ (s + 1))⁻¹
          + (pderivDegBound d : ℝ≥0∞) ^ n * ((2 : ℝ≥0∞) ^ min (t + 1) (R + 1))⁻¹
        ≤ (n : ℝ≥0∞) * (d : ℝ≥0∞) ^ (n - 1) * ((d : ℝ≥0∞) ^ (n + 2))⁻¹
            + (d : ℝ≥0∞) ^ n * ((d : ℝ≥0∞) ^ (n + 2))⁻¹ :=
          add_le_add (mul_le_mul' (sum_pow_pderivDegBound_le hd n) hs) (mul_le_mul' hnum2 ht)
      _ = (n : ℝ≥0∞) * ((d : ℝ≥0∞) ^ (n - 1) * ((d : ℝ≥0∞) ^ (n + 2))⁻¹)
            + (d : ℝ≥0∞) ^ n * ((d : ℝ≥0∞) ^ (n + 2))⁻¹ := by ring
      _ ≤ (n : ℝ≥0∞) * ((d : ℝ≥0∞) ^ n * ((d : ℝ≥0∞) ^ (n + 2))⁻¹)
            + (d : ℝ≥0∞) ^ n * ((d : ℝ≥0∞) ^ (n + 2))⁻¹ :=
          add_le_add (mul_le_mul' (le_refl _) (mul_le_mul' hdn (le_refl _))) (le_refl _)
      _ = ((n : ℝ≥0∞) + 1) * ((d : ℝ≥0∞) ^ 2)⁻¹ := by rw [hcancel]; ring
  refine le_trans (mul_le_mul' (le_refl _) hbracket) ?_
  have heq : ((n : ℝ≥0∞) + 1) * (((n : ℝ≥0∞) + 1) * ((d : ℝ≥0∞) ^ 2)⁻¹)
      = ENNReal.ofReal (((n : ℝ) + 1) ^ 2 / (d : ℝ) ^ 2) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hc1 : ((n : ℝ) + 1) ^ 2 = (((n + 1) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    have hc2 : ((d : ℝ)) ^ 2 = ((d ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hc1, hc2, ENNReal.ofReal_div_of_pos (by rw [← hc2]; positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]
    push_cast
    ring
  rw [heq]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsq : Real.sqrt d ≤ (d : ℝ) ^ 2 := by
    nlinarith [Real.sq_sqrt hdR.le, Real.one_le_sqrt.2 hd1R, Real.sqrt_nonneg (d : ℝ)]
  rw [div_le_div_iff₀ (pow_pos hdR 2) hsd]
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg ((n : ℝ) + 1))]

/-- **Quantitative smoothness bound** (`thm_main`). For every `n ≥ 1` there is a constant
`C_n > 0` such that `P(f is singular over ℂ) ≤ C_n d^{-1/2}` for every `d ≥ 3`, conditional on
`CitedResults`, the results the source defers to the literature.

Only large `d` needs an argument: a probability is at most `1`, so the finitely many remaining
degrees are absorbed by taking `C_n` at least `√d₀`. For large `d`, Bertrand's postulate applied to
`⌊√d⌋` supplies a prime `p` with `√d < p ≤ 2√d`, necessarily odd; `R = (n+2)(⌊log₂ d⌋ + 1)` then
satisfies `R ≤ s ≤ t`, `(n+1)R ≤ d + 1` and `d^{n+2} ≤ 2^R`, all three because a power of `log d`
is eventually dominated by `√d` (`exists_forall_mul_pow_natLog_le_sqrt`). `thm_finite` applies, its
low-degree sum is `O_n(d^{-1/2})` by `lowSum_le` and its high-degree terms are `O_n(d^{-2})` by
`highTerms_le`; `lem_prob_specialization` transfers the resulting bound on `σ_{n,d}(p)` to the
complex singularity probability. -/
@[browning_sawin "thm_main"]
theorem exists_measure_isSingularForm_complex_le (hcited : CitedResults.{0}) {n : ℕ}
    (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
          {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
        ≤ ENNReal.ofReal (C / Real.sqrt d) := by
  classical
  obtain ⟨hbez, hdrop, hsemi, hjac, hhs⟩ := hcited
  have hB1 := one_le_lowSumConst n
  set c₀ : ℝ := max (lowSumConst n ^ 2 * ((n : ℝ) + 2) ^ (n + 1))
    (max (2 * (n : ℝ) + 6) (((n : ℝ) + 1) * ((n : ℝ) + 2))) with hc₀
  have hc₀0 : (0 : ℝ) ≤ c₀ := le_trans (by positivity) (le_max_of_le_right (le_max_left _ _))
  obtain ⟨d₁, hd₁⟩ := exists_forall_mul_pow_natLog_le_sqrt c₀ (n + 1)
  set d₀ : ℕ := max 16 d₁ with hd₀
  set C : ℝ := max (3 / 2 * (lowSumConst n + 2) + ((n : ℝ) + 1) ^ 2) (Real.sqrt d₀) with hC
  refine ⟨C, lt_of_lt_of_le ?_ (le_max_left _ _), fun d hd => ?_⟩
  · nlinarith [sq_nonneg ((n : ℝ) + 1)]
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  by_cases hlarge : d₀ ≤ d
  swap
  · have hle : Real.sqrt d ≤ Real.sqrt d₀ :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : d ≤ d₀))
    refine le_trans MeasureTheory.prob_le_one ?_
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hsd]
    have := le_max_right (3 / 2 * (lowSumConst n + 2) + ((n : ℝ) + 1) ^ 2) (Real.sqrt d₀)
    rw [← hC] at this
    linarith
  have hd16 : 16 ≤ d := le_trans (le_max_left 16 d₁) hlarge
  have hdd₁ : d₁ ≤ d := le_trans (le_max_right 16 d₁) hlarge
  set L : ℕ := Nat.log 2 d + 1 with hL
  set R : ℕ := (n + 2) * L with hR
  have hL1 : 1 ≤ L := by omega
  have hL1R : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hR2 : 2 ≤ R := by
    rw [hR]
    calc 2 ≤ n + 2 := by omega
      _ ≤ (n + 2) * L := Nat.le_mul_of_pos_right _ (by omega)
  have hLR : c₀ * (L : ℝ) ^ (n + 1) ≤ Real.sqrt d := by
    have h := hd₁ d hdd₁
    rwa [show (Nat.log 2 d : ℝ) + 1 = (L : ℝ) by rw [hL]; push_cast; ring] at h
  have hLle : (L : ℝ) ≤ (L : ℝ) ^ (n + 1) := by
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L : ℝ) ^ (n + 1) := pow_le_pow_right₀ hL1R (by omega)
  have hlow : lowSumConst n ^ 2 * (R : ℝ) ^ (n + 1) ≤ Real.sqrt d := by
    have hRe : (R : ℝ) ^ (n + 1) = ((n : ℝ) + 2) ^ (n + 1) * (L : ℝ) ^ (n + 1) := by
      rw [hR]; push_cast; rw [mul_pow]
    rw [hRe]
    calc lowSumConst n ^ 2 * (((n : ℝ) + 2) ^ (n + 1) * (L : ℝ) ^ (n + 1))
        = lowSumConst n ^ 2 * ((n : ℝ) + 2) ^ (n + 1) * (L : ℝ) ^ (n + 1) := by ring
      _ ≤ c₀ * (L : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ Real.sqrt d := hLR
  have hRsqrt : 2 * (R : ℝ) + 2 ≤ Real.sqrt d := by
    have h1 : 2 * (R : ℝ) + 2 ≤ (2 * (n : ℝ) + 6) * (L : ℝ) := by
      rw [hR]; push_cast; nlinarith
    calc 2 * (R : ℝ) + 2 ≤ (2 * (n : ℝ) + 6) * (L : ℝ) := h1
      _ ≤ c₀ * (L : ℝ) ^ (n + 1) :=
          mul_le_mul (le_max_of_le_right (le_max_left _ _)) hLle (by positivity) hc₀0
      _ ≤ Real.sqrt d := hLR
  have hsdd : Real.sqrt d ≤ (d : ℝ) := by
    nlinarith [Real.sq_sqrt hdR.le, Real.one_le_sqrt.2 (by exact_mod_cast hd1 : (1:ℝ) ≤ (d:ℝ)),
      Real.sqrt_nonneg (d : ℝ)]
  have hRd : (n + 1) * R ≤ d + 1 := by
    have h1 : ((n : ℝ) + 1) * ((n : ℝ) + 2) * (L : ℝ) ≤ Real.sqrt d := by
      calc ((n : ℝ) + 1) * ((n : ℝ) + 2) * (L : ℝ)
          ≤ c₀ * (L : ℝ) ^ (n + 1) :=
            mul_le_mul (le_max_of_le_right (le_max_right _ _)) hLle (by positivity) hc₀0
        _ ≤ Real.sqrt d := hLR
    have h2 : (((n + 1) * R : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
      rw [hR]; push_cast; nlinarith
    exact_mod_cast h2
  have hsqrtlt : Real.sqrt d < (Nat.sqrt d : ℝ) + 1 := by
    have h := Nat.lt_succ_sqrt d
    rw [Real.sqrt_lt' (by positivity)]
    have h2 : ((d : ℕ) : ℝ) < ((Nat.sqrt d + 1) * (Nat.sqrt d + 1) : ℕ) := by exact_mod_cast h
    push_cast at h2
    nlinarith
  have hNsq : (Nat.sqrt d : ℝ) ≤ Real.sqrt d := by
    rw [Real.le_sqrt (by positivity) hdR.le]
    exact_mod_cast Nat.sqrt_le' d
  have hRm : 2 * R + 2 ≤ Nat.sqrt d := by
    have h1 : (2 * (R : ℝ) + 2) < (Nat.sqrt d : ℝ) + 1 := lt_of_le_of_lt hRsqrt hsqrtlt
    have h2 : ((2 * R + 2 : ℕ) : ℝ) < ((Nat.sqrt d + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h3 : 2 * R + 2 < Nat.sqrt d + 1 := by exact_mod_cast h2
    omega
  obtain ⟨q, hqp, hq1, hq2⟩ := exists_prime_lt_and_le_two_mul (m := Nat.sqrt d) (by omega)
  have : Fact q.Prime := ⟨hqp⟩
  have hq3 : 3 ≤ q := by omega
  have hqodd : Odd q := hqp.odd_of_ne_two (by omega)
  have hqlow : Real.sqrt d < (q : ℝ) := by
    have h0 : Nat.sqrt d + 1 ≤ q := by omega
    have h : ((Nat.sqrt d + 1 : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast h0
    push_cast at h
    linarith
  have hqhigh : (q : ℝ) ≤ 2 * Real.sqrt d := by
    have h : ((q : ℕ) : ℝ) ≤ ((2 * Nat.sqrt d : ℕ) : ℝ) := by exact_mod_cast hq2
    push_cast at h
    linarith
  have hRs : R ≤ lowerBlockLength q d := by
    rw [lowerBlockLength, Nat.le_div_iff_mul_le (by omega : 0 < q)]
    refine Nat.le_sub_one_of_lt ?_
    calc R * q ≤ R * (2 * Nat.sqrt d) := Nat.mul_le_mul_left _ hq2
      _ = 2 * R * Nat.sqrt d := by ring
      _ < 2 * R * Nat.sqrt d + 2 * Nat.sqrt d := Nat.lt_add_of_pos_right (by omega)
      _ = (2 * R + 2) * Nat.sqrt d := by ring
      _ ≤ Nat.sqrt d * Nat.sqrt d := Nat.mul_le_mul_right _ hRm
      _ ≤ d := by have := Nat.sqrt_le' d; nlinarith
  have hRt : R ≤ upperBlockLength q d :=
    le_trans hRs (Nat.div_le_div_right (Nat.sub_le d 1))
  have h2R : d ^ (n + 2) ≤ 2 ^ R := by
    have hlt : d < 2 ^ L := by rw [hL]; exact Nat.lt_pow_succ_log_self (by norm_num) d
    calc d ^ (n + 2) ≤ (2 ^ L) ^ (n + 2) := Nat.pow_le_pow_left hlt.le _
      _ = 2 ^ (L * (n + 2)) := by rw [← pow_mul]
      _ = 2 ^ R := by rw [hR, mul_comm]
  have hRdiv : R ≤ (d + 1) / (n + 1) :=
    (Nat.le_div_iff_mul_le (by omega : 0 < n + 1)).2 (by rw [mul_comm]; exact hRd)
  refine le_trans (measure_isSingularForm_complex_le_sigma hsemi hjac n d q) ?_
  refine le_trans (sigma_le hbez hdrop hjac hhs hqodd hn hd hRdiv) ?_
  have hlowbd := lowSum_le (n := n) (d := d) (R := R) (p := q) hd16 hqlow hqhigh hqodd hq3 hR2
    hRd hlow
  have hhighbd := highTerms_le (n := n) (d := d) (R := R) (s := lowerBlockLength q d)
    (t := upperBlockLength q d) hd1 hRs hRt h2R
  have hnn1 : (0 : ℝ) ≤ 3 / 2 * (lowSumConst n + 2) / Real.sqrt d :=
    div_nonneg (by linarith) hsd.le
  have hnn2 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 / Real.sqrt d := div_nonneg (by positivity) hsd.le
  refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal hlowbd) hhighbd) ?_
  rw [← ENNReal.ofReal_add hnn1 hnn2]
  refine ENNReal.ofReal_le_ofReal ?_
  have hjoin : 3 / 2 * (lowSumConst n + 2) / Real.sqrt d + ((n : ℝ) + 1) ^ 2 / Real.sqrt d
      = (3 / 2 * (lowSumConst n + 2) + ((n : ℝ) + 1) ^ 2) / Real.sqrt d := by ring
  rw [hjoin, div_le_div_iff_of_pos_right hsd, hC]
  exact le_max_left _ _

end MainBound

/-! ## The Browning–Sawin conjecture

`𝓑_{d,n}` is exactly the set of values of the random sign form `f`, and `f` parametrizes it
bijectively: a sign family is recovered from a form by reading off its coefficients. So `𝓑_{d,n}`
has `2^{N_{d,n}}` elements, `f` is uniform on it, and the proportion of `F ∈ 𝓑_{d,n}` with a given
property is the probability that `f` has it. -/

section Conjecture

open MeasureTheory
open scoped ENNReal

/-- The sign family read off the coefficients of a form in `𝓑_{d,n}`. -/
private def signsOf (n d : ℕ) (F : MvPolynomial (Fin (n + 1)) ℤ) :
    SignFamily (monomialsEq (n + 1) d) := fun α => if F.coeff α.1 = 1 then 1 else -1

/-- Outside degree `d` the random sign form has no coefficients. -/
private theorem coeff_signForm_of_ne {n d : ℕ} (ε : SignFamily (monomialsEq (n + 1) d))
    {α : Fin (n + 1) →₀ ℕ} (hα : α.degree ≠ d) : (signForm n d ε).coeff α = 0 :=
  (mem_signFormSet_signForm ε).1 α hα

/-- **The random sign form parametrizes `𝓑_{d,n}` bijectively.** `signForm n d` is a bijection from
the sign families indexed by the exponent tuples of degree `d` onto `𝓑_{d,n}`, with inverse
`signsOf`: a form in `𝓑_{d,n}` has each coefficient equal to `1` or `-1` in degree `d` and `0`
elsewhere, which is exactly the data of a sign family. -/
private noncomputable def signFormEquiv (n d : ℕ) :
    SignFamily (monomialsEq (n + 1) d) ≃ ↥(signFormSet n d) where
  toFun ε := ⟨signForm n d ε, mem_signFormSet_signForm ε⟩
  invFun F := signsOf n d F.1
  left_inv ε := by
    funext α
    have hα : α.1.degree = d := mem_monomialsEq.1 α.2
    have hc : (signForm n d ε).coeff α.1 = ((ε α : ℤˣ) : ℤ) := by
      rw [coeff_signForm ε hα, signOf_of_mem ε α.2]
    simp only [signsOf]
    rw [hc]
    rcases Int.units_eq_one_or (ε α) with h | h <;> rw [h] <;> norm_num
  right_inv F := by
    refine Subtype.ext (MvPolynomial.ext _ _ fun α => ?_)
    by_cases hα : α.degree = d
    · have hmem : α ∈ monomialsEq (n + 1) d := mem_monomialsEq.2 hα
      rw [coeff_signForm _ hα, signOf_of_mem _ hmem]
      simp only [signsOf]
      rcases F.2.2 α hα with h | h <;> simp [h]
    · rw [coeff_signForm_of_ne _ hα, F.2.1 α hα]

/-- `#{α : |α| = d} = N_{d,n}`: the exponent tuples of degree `d` in `n + 1` variables are counted
by `\binom{n+d}{n}`. -/
private theorem card_monomialsEq (n d : ℕ) :
    (monomialsEq (n + 1) d).card = monomialCount n d := by
  have h : (n + d).choose (n + d - n) = (n + d).choose n := Nat.choose_symm (by omega)
  rw [show n + d - n = d by omega] at h
  rw [monomialsEq, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    monomialCount, show n + 1 + d - 1 = n + d by omega]
  exact h

/-- There are `2^{N_{d,n}}` sign families indexed by the exponent tuples of degree `d`. -/
private theorem card_signFamily (n d : ℕ) :
    Nat.card (SignFamily (monomialsEq (n + 1) d)) = 2 ^ monomialCount n d := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units_int, Fintype.card_coe,
    card_monomialsEq]

/-- **`𝓑_{d,n}` splits into the nonsingular and the singular forms**, the latter counted through
the sign families, and the two counts add up to `2^{N_{d,n}}`. -/
private theorem card_notSingular_add_card_singular (n d : ℕ) :
    Nat.card {F : MvPolynomial (Fin (n + 1)) ℤ // F ∈ signFormSet n d ∧
        ¬ IsSingularForm (F.map (Int.castRingHom ℂ))}
      + Nat.card {ε : SignFamily (monomialsEq (n + 1) d) //
        IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
      = 2 ^ monomialCount n d := by
  classical
  have e1 : {ε : SignFamily (monomialsEq (n + 1) d) //
        ¬ IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
      ≃ {F : ↥(signFormSet n d) //
        ¬ IsSingularForm ((F : MvPolynomial (Fin (n + 1)) ℤ).map (Int.castRingHom ℂ))} :=
    (signFormEquiv n d).subtypeEquiv fun _ => Iff.rfl
  have e2 := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun F : MvPolynomial (Fin (n + 1)) ℤ => F ∈ signFormSet n d)
    (fun F : MvPolynomial (Fin (n + 1)) ℤ => ¬ IsSingularForm (F.map (Int.castRingHom ℂ)))
  have hequiv := e1.trans e2
  have h := Fintype.card_congr (Equiv.sumCompl fun ε : SignFamily (monomialsEq (n + 1) d) =>
    IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ)))
  rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, card_signFamily] at h
  rw [← Nat.card_congr hequiv]
  omega

/-- **The random sign form is uniform on `𝓑_{d,n}`.** The probability that `f` is singular over `ℂ`
is the number of sign families giving a singular form divided by `2^{N_{d,n}}`. -/
private theorem signMeasure_isSingularForm_complex_eq (n d : ℕ) :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
      = (Nat.card {ε : SignFamily (monomialsEq (n + 1) d) //
          IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))} : ℝ≥0∞)
        / 2 ^ monomialCount n d := by
  classical
  have h1 := signMeasure_coe_finset (ι := {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d})
    (Set.toFinset {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))})
  rw [Set.coe_toFinset] at h1
  rw [h1, Set.toFinset_card, ← Nat.card_eq_fintype_card, Fintype.card_coe, card_monomialsEq]
  rfl

/-- **The Browning–Sawin conjecture** (`thm_bs_conjecture`). For every `n ≥ 2` the proportion of
`F ∈ 𝓑_{d,n}` that are not singular over `ℂ` is `1 + O_n(d^{-1/2})`, conditional on `CitedResults`,
the results the source defers to the literature.

`𝓑_{d,n}` has `2^{N_{d,n}}` elements and `f` is uniform on it
(`signFormEquiv`, `signMeasure_isSingularForm_complex_eq`), so the proportion of nonsingular
elements is `1 - P(f is singular over ℂ)`, and `thm_main` — whose hypothesis `n ≥ 1` follows from
`n ≥ 2` — bounds the subtracted probability by `C_n d^{-1/2}`. -/
@[browning_sawin "thm_bs_conjecture"]
theorem exists_forall_abs_card_notSingular_div_sub_one_le (hcited : CitedResults.{0}) {n : ℕ}
    (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      |(Nat.card {F : MvPolynomial (Fin (n + 1)) ℤ // F ∈ signFormSet n d ∧
            ¬ IsSingularForm (F.map (Int.castRingHom ℂ))} : ℝ)
          / 2 ^ monomialCount n d - 1| ≤ C / Real.sqrt d := by
  obtain ⟨C, hC0, hC⟩ := exists_measure_isSingularForm_complex_le hcited (n := n) (by omega)
  refine ⟨C, hC0, fun d hd => ?_⟩
  have hdR : (0 : ℝ) < d := by positivity
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  set N : ℕ := monomialCount n d with hN
  set K : ℕ := Nat.card {ε : SignFamily (monomialsEq (n + 1) d) //
    IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))} with hK
  set M : ℕ := Nat.card {F : MvPolynomial (Fin (n + 1)) ℤ // F ∈ signFormSet n d ∧
    ¬ IsSingularForm (F.map (Int.castRingHom ℂ))} with hM
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  have hcast : (M : ℝ) + (K : ℝ) = 2 ^ N := by
    exact_mod_cast card_notSingular_add_card_singular n d
  have hratio : (M : ℝ) / 2 ^ N - 1 = -((K : ℝ) / 2 ^ N) := by
    field_simp
    linarith
  rw [hratio, abs_neg, abs_of_nonneg (by positivity)]
  have hmeas := hC d hd
  rw [signMeasure_isSingularForm_complex_eq n d, ← hK, ← hN] at hmeas
  have heq : ENNReal.ofReal ((K : ℝ) / 2 ^ N) = ((K : ℕ) : ℝ≥0∞) / 2 ^ N := by
    rw [ENNReal.ofReal_div_of_pos h2N, ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [← heq] at hmeas
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmeas

end Conjecture

end BrowningSawin
