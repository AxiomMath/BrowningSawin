/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-! # The formal challenge file, written by humans

This is a human-written file certifying the formal statements that this repository proves: random
hypersurfaces with sign coefficients are almost always nonsingular, at the rate `O_n(d^{-1/2})`.

The definitions below are reproduced from the library under its own fully-qualified names, so the
statements can be read without building it. The results the source defers to the literature are
`Prop`s here, and the theorems take them as an explicit hypothesis; nothing is assumed by fiat.
-/

@[expose] public section

namespace BrowningSawin

open Filter MvPolynomial MeasureTheory
open scoped ENNReal

/-! ## Numerical parameters and sign families -/

/-- `N_{d,n} = \binom{n+d}{n}`, the number of monomials of degree `d` in `n + 1` variables. -/
abbrev monomialCount (n d : ℕ) : ℕ := (n + d).choose n

/-- The exponent tuples `α` in `m` variables with `|α| = d`. -/
def monomialsEq (m d : ℕ) : Finset (Fin m →₀ ℕ) := Finset.finsuppAntidiag Finset.univ d

/-- A family of signs indexed by a finite set `s` of exponent tuples. -/
abbrev SignFamily {m : ℕ} (s : Finset (Fin m →₀ ℕ)) : Type := ↥s → ℤˣ

/-- The sign `ε_α` a sign family attaches to an exponent tuple, extended by `1` outside the index
set so that it can be evaluated at any tuple. -/
def signOf {m : ℕ} {s : Finset (Fin m →₀ ℕ)} (ε : SignFamily s) (α : Fin m →₀ ℕ) : ℤˣ :=
  if h : α ∈ s then ε ⟨α, h⟩ else 1

/-- The law of a family of independent uniform signs: the uniform probability measure on the finite
space `ι → ℤˣ` of sign families. -/
noncomputable def signMeasure (ι : Type*) [Fintype ι] [DecidableEq ι] : Measure (ι → ℤˣ) :=
  (PMF.uniformOfFintype (ι → ℤˣ)).toMeasure

/-- `𝓑_{d,n}`: the set of homogeneous `F ∈ ℤ[x₀,…,xₙ]` of the form `∑_{|α| = d} c_α x^α` with every
`c_α ∈ {-1, 1}`. -/
def signFormSet (n d : ℕ) : Set (MvPolynomial (Fin (n + 1)) ℤ) :=
  {F | (∀ α, α.degree ≠ d → F.coeff α = 0) ∧ ∀ α, α.degree = d → F.coeff α = 1 ∨ F.coeff α = -1}

/-- `f = ∑_{|α| = d} ε_α x^α`, the random sign form attached to a family of independent uniform
signs indexed by the exponent tuples of degree `d`. -/
noncomputable def signForm (n d : ℕ) (ε : SignFamily (monomialsEq (n + 1) d)) :
    MvPolynomial (Fin (n + 1)) ℤ :=
  ∑ α ∈ monomialsEq (n + 1) d, monomial α (signOf ε α : ℤ)

/-! ## Algebraic sets, dimension and degree

`dim` is valued in `ℤ`, with the empty set given dimension `-1`, and is computed from the reduced
coordinate ring. It is geometric because it is applied over an algebraic closure. -/

section AlgebraicSets

variable {K : Type*} [Field K] {n : ℕ}

/-- The ideal of polynomials vanishing on a set of affine points. -/
noncomputable def affineVanishingIdeal (V : Set (Fin n → K)) : Ideal (MvPolynomial (Fin n) K) :=
  ⨅ a ∈ V, RingHom.ker (MvPolynomial.eval a)

/-- `Z(h₁, …, h_j)`, the zero locus in `𝔸ⁿ` of an ideal. -/
def affineZeroLocus (I : Ideal (MvPolynomial (Fin n) K)) : Set (Fin n → K) :=
  {a | ∀ F ∈ I, eval a F = 0}

/-- The zero locus in `ℙⁿ` of a homogeneous ideal. -/
def projZeroLocus (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Set (Projectivization K (Fin (n + 1) → K)) := {P | ∀ F ∈ I, eval P.rep F = 0}

/-- The affine cone over a set of projective points. -/
noncomputable def affineCone (T : Set (Projectivization K (Fin (n + 1) → K))) :
    Set (Fin (n + 1) → K) := {a | ∃ P ∈ T, ∃ c : K, a = c • P.rep}

/-- The homogeneous ideal of a projective set: the polynomials vanishing on its affine cone. -/
noncomputable def coneVanishingIdeal (T : Set (Projectivization K (Fin (n + 1) → K))) :
    Ideal (MvPolynomial (Fin (n + 1)) K) := affineVanishingIdeal (affineCone T)

/-- The standard chart `x₀ ≠ 0`, embedding `𝔸ⁿ` into `ℙⁿ`. -/
noncomputable def standardChart (a : Fin n → K) : Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (Fin.cons 1 a) fun h => one_ne_zero (α := K) (by
    simpa using congrFun h 0)

/-- The projective closure of an affine algebraic set, taken along the standard chart. -/
noncomputable def projectiveClosure (V : Set (Fin n → K)) :
    Set (Projectivization K (Fin (n + 1) → K)) :=
  projZeroLocus (coneVanishingIdeal (standardChart '' V))

/-- The distinct irreducible components of an affine algebraic set: the zero loci of the minimal
primes over its vanishing ideal. -/
noncomputable def irreducibleComponentsOf (V : Set (Fin n → K)) : Set (Set (Fin n → K)) :=
  affineZeroLocus '' (affineVanishingIdeal V).minimalPrimes

/-- The Hilbert function of a projective algebraic set `T`: the `K`-dimension of the degree-`q`
graded piece of the homogeneous coordinate ring of `T`. -/
noncomputable def projHilbertFunction (T : Set (Projectivization K (Fin (n + 1) → K)))
    (q : ℕ) : ℕ :=
  Module.finrank K (↥(homogeneousSubmodule (Fin (n + 1)) K q) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K q).subtype
      ((coneVanishingIdeal T).restrictScalars K))

open Classical in
/-- The Hilbert polynomial of a numerical function `H`: the polynomial that agrees with `H` at all
large arguments, and `0` when there is none. -/
noncomputable def hilbertPolynomialOf (H : ℕ → ℕ) : Polynomial ℚ :=
  if h : ∃ P : Polynomial ℚ, ∀ᶠ q : ℕ in atTop, P.eval (q : ℚ) = H q then h.choose else 0

/-- `deg T` for an irreducible projective variety `T` of dimension `r`: the integer whose quotient
by `r !` is the leading coefficient of the Hilbert polynomial of its homogeneous coordinate
ring. -/
noncomputable def projDegree (T : Set (Projectivization K (Fin (n + 1) → K))) : ℕ :=
  ((Nat.factorial (hilbertPolynomialOf (projHilbertFunction T)).natDegree : ℚ) *
    (hilbertPolynomialOf (projHilbertFunction T)).leadingCoeff).num.toNat

/-- `δ(Z) = ∑_V deg V̄`, the sum of the degrees of the projective closures of the distinct
irreducible components of an affine algebraic set `Z`, so that `δ(∅) = 0`. -/
noncomputable def delta (V : Set (Fin n → K)) : ℕ :=
  ∑ᶠ W ∈ irreducibleComponentsOf V, projDegree (projectiveClosure W)

/-- `dim V`, the dimension of a set of affine points: the Krull dimension of its reduced coordinate
ring, with `dim ∅ = -1`. -/
noncomputable def affineDim (V : Set (Fin n → K)) : ℤ :=
  (ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)).recBotCoe (-1)
    fun r => (r.toNat : ℤ)

/-- `dim T`, the dimension of a set of projective points: one less than that of its affine cone,
with `dim ∅ = -1`. -/
noncomputable def projDim (T : Set (Projectivization K (Fin (n + 1) → K))) : ℤ :=
  max (-1) (affineDim (affineCone T) - 1)

end AlgebraicSets

/-! ## The generic point of an algebraic closure -/

section GenericPoint

variable {k : Type*} [Field k]

/-- The generic point of `Spec k̄`: the zero ideal, prime because an algebraic closure is a
field. -/
noncomputable def genericPoint : PrimeSpectrum (AlgebraicClosure k) := ⟨⊥, Ideal.isPrime_bot⟩

end GenericPoint

/-! ## The cited external results, as hypotheses

The five results the source defers to the literature. `CitedResults` is their
conjunction, and it is the single hypothesis each theorem below takes. -/

/-- **Affine Bézout inequality.** For `h₁, …, h_j` in `n` variables over an algebraically closed
field, each of degree at most `D ≥ 1`, `δ(Z(h₁, …, h_j)) ≤ D ^ j`.

Heintz, Theoret. Comput. Sci. **24** (1983), 239–277; Fulton, *Intersection Theory* (1984),
Example 8.4.6. -/
def AffineBezout : Prop :=
  ∀ {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {ι : Type} [Fintype ι] {D : ℕ},
    1 ≤ D → ∀ h : ι → MvPolynomial (Fin n) K, (∀ i, (h i).totalDegree ≤ D) →
      delta {a : Fin n → K | ∀ i, eval a (h i) = 0} ≤ D ^ Fintype.card ι

/-- **Dimension drop under a nonvanishing equation.** For `V = Z(P)` irreducible and
positive-dimensional and `h` not vanishing identically on `V`, every irreducible component of
`V ∩ Z(h)` has dimension at most `dim V - 1`.

Heintz, Theoret. Comput. Sci. **24** (1983), 239–277; Fulton, Example 8.4.6. -/
def DimensionDrop : Prop :=
  ∀ {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {P : Ideal (MvPolynomial (Fin n) K)},
    P.IsPrime → 0 < affineDim (affineZeroLocus P) → ∀ {h : MvPolynomial (Fin n) K},
      (∃ a ∈ affineZeroLocus P, eval a h ≠ 0) → ∀ {W : Set (Fin n → K)},
        W ∈ irreducibleComponentsOf (affineZeroLocus P ∩ {a | eval a h = 0}) →
          affineDim W ≤ affineDim (affineZeroLocus P) - 1

/-- **Semicontinuity of fiber dimension.** For a homogeneous ideal `I ⊆ ℤ[x₀, …, x_n]` and a prime
`p`, the projective set cut out over `𝔽̄ₚ` by the image of `I` has dimension at least that of the
projective set cut out over `ℂ`.

Cited by the source: upper semicontinuity of fiber dimension for proper morphisms, *The Stacks
Project*, Tag 0D4I. -/
def FiberDimensionSemicontinuity : Prop :=
  ∀ {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℤ)),
    (∀ F ∈ I, ∀ d : ℕ, homogeneousComponent d F ∈ I) → ∀ (p : ℕ) [Fact p.Prime],
      projDim (projZeroLocus (I.map (MvPolynomial.map (Int.castRingHom ℂ)))) ≤
        projDim (projZeroLocus
          (I.map (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))))))

/-- **Affine hypersurface Jacobian criterion.** Over a perfect field, a point of `𝔸ⁿ` at which a
nonzero `g` vanishes is singular on `g = 0` — outside the smooth locus of
`Spec k̄[y₁, …, y_n]/(g)`, which retains the repeated factors of `g` — exactly when every `∂ᵢg`
vanishes there too.

Hartshorne, *Algebraic Geometry* (1977), Ch. I §5 and Ch. II §8. -/
def AffineJacobianCriterion : Prop :=
  ∀ {k : Type*} [Field k] [PerfectField k] {σ : Type} [Finite σ] {g : MvPolynomial σ k},
    g ≠ 0 → ∀ {a : σ → AlgebraicClosure k}
      (ha : eval a (g.map (algebraMap k (AlgebraicClosure k))) = 0),
        (PrimeSpectrum.comap
            (Ideal.Quotient.lift (Ideal.span {g.map (algebraMap k (AlgebraicClosure k))}) (eval a)
              fun _ hx => (Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 ha) hx)
            genericPoint ∉
          Algebra.smoothLocus (AlgebraicClosure k)
            (MvPolynomial σ (AlgebraicClosure k) ⧸
              Ideal.span {g.map (algebraMap k (AlgebraicClosure k))}) ↔
          ∀ i, eval a ((pderiv i g).map (algebraMap k (AlgebraicClosure k))) = 0)

/-- **Hilbert–Serre: the Hilbert function of a projective algebraic set is eventually polynomial.**
For every `T ⊆ ℙⁿ` over a field there is a rational polynomial agreeing with
`projHilbertFunction T` in all large degrees.

Cited by the source: Hartshorne, *Algebraic Geometry* (1977), Ch. I §7, whose facts about Hilbert
functions and Hilbert polynomials the source recalls rather than proves. -/
def HilbertSerre : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (T : Set (Projectivization K (Fin (n + 1) → K))),
    ∃ P : Polynomial ℚ, ∀ᶠ q : ℕ in Filter.atTop,
      P.eval (q : ℚ) = projHilbertFunction T q

/-- The classical results the source defers to the literature: the single hypothesis the main
theorems take. -/
def CitedResults.{u} : Prop :=
  AffineBezout.{u} ∧ DimensionDrop.{u} ∧ FiberDimensionSemicontinuity ∧
    AffineJacobianCriterion.{u} ∧ HilbertSerre.{u}

/-! ## Hypersurfaces and their singular loci -/

section Hypersurface

variable {k : Type*} [Field k] {n : ℕ}

/-- The reduction of a form to an algebraic closure of its field of coefficients. -/
noncomputable def toClosure (F : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) := F.map (algebraMap k (AlgebraicClosure k))

/-- The coordinate ring of the affine cone `Z(F) ⊆ 𝔸ⁿ⁺¹` over an algebraic closure. Its scheme
structure retains repeated factors of `F`. -/
noncomputable abbrev coneRing (F : MvPolynomial (Fin (n + 1)) k) : Type _ :=
  MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) ⧸ Ideal.span {toClosure F}

/-- The point of the affine cone `Z(F)` cut out by a vector `a` on which `F` vanishes. -/
noncomputable def conePoint (F : MvPolynomial (Fin (n + 1)) k)
    (a : Fin (n + 1) → AlgebraicClosure k) (h : eval a (toClosure F) = 0) :
    PrimeSpectrum (coneRing F) :=
  PrimeSpectrum.comap
    (Ideal.Quotient.lift (Ideal.span {toClosure F}) (MvPolynomial.eval a) fun _ hx =>
      RingHom.mem_ker.mp
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.mpr h)) hx))
    genericPoint

/-- `Sing X_F`, the points of `X_F` over an algebraic closure at which `X_F` is not smooth.
Smoothness at a projective point is tested on the affine cone `Z(F) ⊆ 𝔸ⁿ⁺¹`. -/
noncomputable def singularLocus (F : MvPolynomial (Fin (n + 1)) k) :
    Set (Projectivization (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k)) :=
  {P | ∃ h : eval P.rep (toClosure F) = 0,
    conePoint F P.rep h ∉ Algebra.smoothLocus (AlgebraicClosure k) (coneRing F)}

/-- A form is *singular* when its hypersurface has a singular point. -/
def IsSingularForm (F : MvPolynomial (Fin (n + 1)) k) : Prop := (singularLocus F).Nonempty

end Hypersurface

end BrowningSawin

namespace BrowningSawin.Challenge

open MvPolynomial MeasureTheory
open scoped ENNReal

/-- **`thm_positive` — the positive-dimensional singular locus bound.** For `n ≥ 1` and `d ≥ 3`,
`𝐏(dim Sing X_f ≥ 1) ≤ n(n+1) d^{n-1} 2^{-⌊(d-1)/3⌋-1}` over `ℂ`. -/
theorem thm_positive (hcited : CitedResults.{0}) {n d : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d) :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | 1 ≤ projDim (singularLocus ((signForm n d ε).map (Int.castRingHom ℂ)))}
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ (n - 1)
          * ((2 : ℝ≥0∞) ^ ((d - 1) / 3 + 1))⁻¹ :=
  sorry

/-- **`thm_absolute_irred` — the reducibility bound.** For `n ≥ 3` and `d ≥ 3`, the probability
that `f` is reducible over `ℂ` obeys the same bound. -/
theorem thm_absolute_irred (hcited : CitedResults.{0}) {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | ¬ Irreducible ((signForm n d ε).map (Int.castRingHom ℂ))}
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ (n - 1)
          * ((2 : ℝ≥0∞) ^ ((d - 1) / 3 + 1))⁻¹ :=
  sorry

/-- **`thm_main` — the main theorem.** For each `n ≥ 1` there is a `C_n > 0` with
`𝐏(f is singular over ℂ) ≤ C_n d^{-1/2}` for every `d ≥ 3`. -/
theorem thm_main (hcited : CitedResults.{0}) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
          {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
        ≤ ENNReal.ofReal (C / Real.sqrt d) :=
  sorry

/-- **`thm_bs_conjecture` — the Browning–Sawin conjecture.** For each `n ≥ 2`, the proportion of
nonsingular forms in `𝓑_{d,n}` is `1 + O_n(d^{-1/2})`. -/
theorem thm_bs_conjecture (hcited : CitedResults.{0}) {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      |(Nat.card {F : MvPolynomial (Fin (n + 1)) ℤ // F ∈ signFormSet n d ∧
            ¬ IsSingularForm (F.map (Int.castRingHom ℂ))} : ℝ)
          / 2 ^ monomialCount n d - 1| ≤ C / Real.sqrt d :=
  sorry

end BrowningSawin.Challenge
