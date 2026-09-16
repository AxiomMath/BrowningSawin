/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Smooth.Locus
public import BrowningSawin.Attr
public import BrowningSawin.Defs.Definitions
public import BrowningSawin.Notation

/-!
# The cited external results, as hypotheses

The statements the source defers to the literature, each recorded as a `Prop`, so that a result
resting on one carries it as an explicit hypothesis.

Two of the seven cited results are already in Mathlib and are therefore theorems of this
development, proved in `BrowningSawin.External`: Bertrand's postulate and Krull's height theorem.
The five below are genuinely assumed.

## Main definitions

* `AffineBezout`: the affine Bézout inequality.
* `DimensionDrop`: the dimension drop under a nonvanishing equation.
* `FiberDimensionSemicontinuity`: semicontinuity of fiber dimension under reduction modulo `p`.
* `AffineJacobianCriterion`: the Jacobian criterion for an affine hypersurface.
* `HilbertSerre`: existence of the Hilbert polynomial.
* `CitedResults`: the conjunction of the five, the single hypothesis the main theorems take.
-/

@[expose] public section

namespace BrowningSawin

open MvPolynomial

/-- **Affine Bézout inequality.** For polynomials `h₁, …, h_j` in `n` variables over an
algebraically closed field, each of degree at most `D ≥ 1`, the sum `δ` of the degrees of the
projective closures of the irreducible components of `Z(h₁, …, h_j)` is at most `D ^ j`. The family
of polynomials is indexed by an arbitrary finite type, `j` being its cardinality.

Cited by the source: Heintz, *Definability and fast quantifier elimination in algebraically closed
fields*, Theoret. Comput. Sci. **24** (1983), 239–277; Fulton, *Intersection Theory* (1984),
Example 8.4.6. -/
@[browning_sawin "lem_bezout_degree"]
def AffineBezout : Prop :=
  ∀ {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ} {ι : Type} [Fintype ι] {D : ℕ},
    1 ≤ D → ∀ h : ι → MvPolynomial (Fin n) K, (∀ i, (h i).totalDegree ≤ D) →
      delta {a : Fin n → K | ∀ i, eval a (h i) = 0} ≤ D ^ Fintype.card ι

/-- **Dimension drop under a nonvanishing equation.** Let `V = Z(P)` be an irreducible
positive-dimensional affine algebraic set over an algebraically closed field — irreducibility being
primality of the prime `P` it is cut out by — and let `h` be a polynomial that does not vanish
identically on `V`. Then every irreducible component of `V ∩ Z(h)` has dimension at most
`dim V - 1`.

Cited by the source, with the same references as `AffineBezout`: Heintz, Theoret. Comput. Sci.
**24** (1983), 239–277; Fulton, *Intersection Theory* (1984), Example 8.4.6, via the
hypersurface-section argument for Hilbert polynomials. -/
@[browning_sawin "lem_bezout_dim_drop"]
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
@[browning_sawin "lem_specialization_dim"]
def FiberDimensionSemicontinuity : Prop :=
  ∀ {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℤ)),
    (∀ F ∈ I, ∀ d : ℕ, homogeneousComponent d F ∈ I) → ∀ (p : ℕ) [Fact p.Prime],
      projDim (projZeroLocus (I.map (MvPolynomial.map (Int.castRingHom ℂ)))) ≤
        projDim (projZeroLocus
          (I.map (MvPolynomial.map (Int.castRingHom (AlgebraicClosure (ZMod p))))))

/-- **Affine hypersurface Jacobian criterion.** Let `k` be a perfect field, let `g ∈ k[y₁, …, y_n]`
be nonzero and let `a` be a point of `𝔸ⁿ` over an algebraic closure of `k` at which `g` vanishes.
Then `a` is a singular point of the hypersurface `g = 0` — that is, the point of
`Spec k̄[y₁, …, y_n]/(g)` it cuts out is outside the smooth locus of that ring over `k̄`, the
hypersurface carrying the scheme structure of `g` including its repeated factors — if and only if
every partial derivative `∂ᵢg` vanishes at `a` as well.

Cited by the source: Hartshorne, *Algebraic Geometry* (1977), Ch. I §5 and Ch. II §8 — the
regular-local-ring criterion together with the agreement of geometric regularity and smoothness
over a perfect field. -/
@[browning_sawin "lem_jacobian_affine"]
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
@[browning_sawin "lem_hilbert_serre"]
def HilbertSerre : Prop :=
  ∀ {K : Type*} [Field K] {n : ℕ} (T : Set (Projectivization K (Fin (n + 1) → K))),
    ∃ P : Polynomial ℚ, ∀ᶠ q : ℕ in Filter.atTop,
      P.eval (q : ℚ) = projHilbertFunction T q

/-- The classical results the source defers to the literature: the single hypothesis the main
theorems take. -/
def CitedResults.{u} : Prop :=
  AffineBezout.{u} ∧ DimensionDrop.{u} ∧ FiberDimensionSemicontinuity ∧
    AffineJacobianCriterion.{u} ∧ HilbertSerre.{u}

end BrowningSawin
