/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Nullstellensatz
public import BrowningSawin.Attr
public import BrowningSawin.External
public import BrowningSawin.Cited
public import BrowningSawin.Defs.Definitions
public import BrowningSawin.Notation
public import BrowningSawin.ConcentrationOfSignSums
public import BrowningSawin.SingularityAtAPrescribedClosedPoint

/-!
# Closed points of large degree

The coefficient partition of the affine sign polynomial into the blocks `U, G₁, …, G_n, H`, the
independence of those blocks, and the resulting bound on the probability that the affine
hypersurface `g = 0` is singular at a closed point of large degree.

## Main definitions

* `functionField`: the function field `K(V)` of the irreducible affine algebraic set `V = Z(P)` cut
  out by a prime ideal `P`, namely the fraction field of its coordinate ring.
* `restrictToFunctionField`: the restriction to `V = Z(P)`, read in `K(V)`, of a polynomial with
  coefficients in a subfield of `K`.
* `BlockIndex`: the index type of the `n + 2` blocks `U, G₁, …, G_n, H`.
* `blockOf`: the block carrying the coefficient of a given exponent tuple.
* `block`: the `n + 2` blocks, as one family of random polynomials.
* `revealFailure`: the event that some positive-dimensional irreducible component of the critical
  locus `W_i` lies inside `Z(∂_i g)`.

## Main results

* `subsingleton_setOf_pow_eq`: in characteristic `p` at most one element has a given `p`-th power.
* `exists_transcendental_coordinate`: on an irreducible affine algebraic set of positive dimension
  over an algebraically closed field some coordinate function is transcendental, as an element of
  the function field. An irreducible set is presented as the zero locus of a prime ideal, the
  convention of `DimensionDrop`; the Nullstellensatz identifies the coordinate ring computing its
  dimension with the quotient by that prime.
* `exists_linearIndependent_pow_coordinate`: the powers `1, y_j, …, y_j ^ s` of that coordinate are
  linearly independent over any subfield of the base field — in the application, over `𝔽ₚ` inside
  `𝔽̄ₚ`.
* `affineSignPoly_eq_blockU_add_sum_add_blockH_pow`: `g = U + ∑ y_i G_i^p + H^p`. Only `p > 1` and
  `d ≥ 1` are used; the oddness of `p` and `d ≥ 3` are not needed. The two halves of the partition
  are isolated as `blockH_pow` and `X_mul_blockG_pow`, which say that `H^p` and `y_i G_i^p` are
  exactly the parts of `g` supported on the residue classes `0` and `e_i` modulo `p`.
* `pderiv_affineSignPoly`: `∂ᵢ g = ∂ᵢ U + G_i^p`.
* `iIndepFun_block`: the `n + 2` blocks `U, G₁, …, G_n, H`, packaged as the family `block` indexed
  by `BlockIndex n`, are mutually independent. The general fact behind it is
  `iIndepFun_of_forall_eq_on_fiber`: functions of the sign families cut out by the fibres of a map
  on the index set are mutually independent, the sign family factoring measure-preservingly as the
  product of its restrictions to those fibres.
* `ncard_criticalLocus_le_pow`: a finite critical locus of a polynomial of total degree at most
  `d ≥ 2` has at most `D ^ n` points. The geometric input is `delta_eq_ncard_of_finite`: for a
  finite algebraic set `δ` is the number of points, its irreducible components being its points and
  the projective closure of a point having degree `1` (`projDegree_projectiveClosure_singleton`).
* `one_le_projHilbertFunction`: the Hilbert function of a nonempty projective algebraic set is at
  least `1` in every degree.
* `signMeasure_inter_eq_mul` and `signMeasure_le_mul_of_cond`: functions of disjoint groups of
  independent signs are independent, and if — after fixing every sign outside one block — the event
  is covered by at most `N` events that depend on that block alone and each have probability at
  most `q`, then the whole event has probability at most `N q`.
* `affineDim_le_of_forall_minimalPrimes` and `ncard_minimalPrimes_le_delta`: the dimension of an
  affine algebraic set is bounded by the dimensions of its irreducible components (a chain of
  primes over an ideal lies entirely over one minimal prime of it), and the number of components is
  bounded by `δ`, each contributing at least `1` by `one_le_projDegree`.
* `affineDim_le_of_mem_minimalPrimes_sup`: if every irreducible component of `Z(J)` has dimension
  at most `m + 1` and `h` vanishes identically on none of the positive-dimensional ones, then every
  component of `Z(J) ∩ Z(h)` has dimension at most `m`.
* `signMeasure_zero_lt_affineDim_criticalLocus_le`:
  `P(dim W_n > 0) ≤ (∑_{i<n} D^i) 2^{-(s+1)}`.
* `finite_of_affineDim_nonpos`: an affine algebraic set of dimension at most `0` is finite, its
  points injecting into the minimal primes of its vanishing ideal.
* `exists_finset_linearIndependent_evalAt_monomial`: at a closed point `Q` of `𝔸ⁿ_k` there are
  `min (s+1, deg Q)` monomials of total degree at most `s` whose images in `κ(Q)` are `k`-linearly
  independent.
* `signMeasure_pow_restrictToFunctionField_blockG_le`: on an irreducible component `V = Z(P)` of
  positive dimension a prescribed `p`-th power of the restriction of `G_i` to `K(V)` has
  probability at most `2^{-(s+1)}`.
* `signMeasure_pow_evalAt_blockH_le`: at a closed point `Q` of degree `e` a prescribed value of
  `H(Q)^p` has probability at most `2^{-min(t+1,e)}`.
* `signMeasure_exists_singular_closedPoint_le`:
  `P(∃ a closed point P of 𝔸ⁿ_{𝔽ₚ} with deg P > R, singular on g = 0)
    ≤ (∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}`.
-/

@[expose] public section

namespace BrowningSawin

open MvPolynomial
open scoped ENNReal

universe u

/-! ## A `p`-th power prescribes its root -/

/-- **A `p`-th power prescribes its root.** In a field of characteristic `p` at most one element
has a given `p`-th power, because the `p`-th power map is an injective ring homomorphism there: if
`b ^ p = c ^ p` then `(b - c) ^ p = 0`, and a field has no nonzero nilpotents. -/
@[browning_sawin "lem_frobenius_unique_root"]
theorem subsingleton_setOf_pow_eq {k : Type*} [Field k] {p : ℕ} [ExpChar k p] (a : k) :
    {b : k | b ^ p = a}.Subsingleton := fun _ hb _ hc =>
  frobenius_inj k p (by simpa [frobenius_def] using hb.trans hc.symm)

/-! ## The function field of an irreducible affine algebraic set

An irreducible affine algebraic set is the zero locus of a prime ideal `P`, as in the statement of
`DimensionDrop`; its coordinate ring is the domain `K[y₁, …, y_n] ⧸ P` and its function field is
the fraction field of that domain. The coordinate function `y_j` restricts to the image of `X j`
there. -/

section FunctionField

variable {K : Type*} [Field K] {n : ℕ}

/-- An element of a field extension of an algebraically closed field that is algebraic over it lies
in it: the minimal polynomial is irreducible, hence of degree one. -/
theorem exists_algebraMap_eq_of_isAlgebraic {L : Type*} [IsAlgClosed K] [Field L] [Algebra K L]
    {x : L} (hx : IsAlgebraic K x) : ∃ c : K, algebraMap K L c = x := by
  have hi : IsIntegral K x := hx.isIntegral
  have hmonic := minpoly.monic hi
  have hdeg : (minpoly K x).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hi))
  have hc1 : (minpoly K x).coeff 1 = 1 := by
    have h := hmonic
    rwa [Polynomial.Monic, Polynomial.leadingCoeff, hdeg] at h
  have heq : minpoly K x = Polynomial.X + Polynomial.C ((minpoly K x).coeff 0) := by
    have h := Polynomial.eq_X_add_C_of_degree_le_one (p := minpoly K x)
      (by rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]; exact le_rfl)
    rwa [hc1, map_one, one_mul] at h
  have h0 := minpoly.aeval K x
  rw [heq] at h0
  simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h0
  exact ⟨-(minpoly K x).coeff 0, by rw [map_neg]; linear_combination -h0⟩

/-- `affineVanishingIdeal` agrees with `MvPolynomial.vanishingIdeal`. -/
theorem affineVanishingIdeal_eq_vanishingIdeal (V : Set (Fin n → K)) :
    affineVanishingIdeal V = MvPolynomial.vanishingIdeal K V := by
  ext F
  rw [mem_affineVanishingIdeal]
  rfl

/-- `affineZeroLocus` agrees with `MvPolynomial.zeroLocus`. -/
theorem affineZeroLocus_eq_zeroLocus (I : Ideal (MvPolynomial (Fin n) K)) :
    affineZeroLocus I = MvPolynomial.zeroLocus K I := rfl

/-- **Nullstellensatz for a prime.** Over an algebraically closed field, the polynomials vanishing
on the zero locus of a prime ideal are exactly that prime. -/
theorem affineVanishingIdeal_affineZeroLocus [IsAlgClosed K]
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime) :
    affineVanishingIdeal (affineZeroLocus P) = P := by
  rw [affineVanishingIdeal_eq_vanishingIdeal, affineZeroLocus_eq_zeroLocus,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hP.radical]

/-- An irreducible affine algebraic set whose coordinate ring is the base field is a point: its
dimension is `0`. -/
theorem affineDim_affineZeroLocus_eq_zero_of_ringEquiv [IsAlgClosed K]
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime)
    (e : (MvPolynomial (Fin n) K ⧸ P) ≃+* K) : affineDim (affineZeroLocus P) = 0 := by
  rw [affineDim, affineVanishingIdeal_affineZeroLocus hP, ringKrullDim_eq_of_ringEquiv e,
    ringKrullDim_eq_zero_of_field K]
  rfl

/-- **A nonconstant coordinate is transcendental.** On an irreducible affine algebraic set of
positive dimension some coordinate function is transcendental over the base field, as an element of
the function field: were every coordinate algebraic, each would lie in the algebraically closed
base field, the coordinate ring would be the base field itself, and the set would be a point. -/
@[browning_sawin "lem_transcendental_coordinate"]
theorem exists_transcendental_coordinate [IsAlgClosed K]
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime)
    (hdim : 0 < affineDim (affineZeroLocus P)) :
    ∃ j : Fin n, Transcendental K
      (algebraMap (MvPolynomial (Fin n) K ⧸ P) (FractionRing (MvPolynomial (Fin n) K ⧸ P))
        (Ideal.Quotient.mk P (X j))) := by
  have := hP
  have : IsDomain (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.isDomain P
  by_contra hcon
  push Not at hcon
  have hcoord : ∀ j : Fin n, ∃ c : K,
      algebraMap K (MvPolynomial (Fin n) K ⧸ P) c = Ideal.Quotient.mk P (X j) := by
    intro j
    obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic (not_not.1 (hcon j))
    refine ⟨c, IsFractionRing.injective (MvPolynomial (Fin n) K ⧸ P)
      (FractionRing (MvPolynomial (Fin n) K ⧸ P)) ?_⟩
    rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hsurj : Function.Surjective (algebraMap K (MvPolynomial (Fin n) K ⧸ P)) := by
    intro a
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction F using MvPolynomial.induction_on with
    | C c => exact ⟨c, rfl⟩
    | add F G hF hG =>
        obtain ⟨c, hc⟩ := hF
        obtain ⟨e, he⟩ := hG
        exact ⟨c + e, by rw [map_add, hc, he, map_add]⟩
    | mul_X F j hF =>
        obtain ⟨c, hc⟩ := hF
        obtain ⟨e, he⟩ := hcoord j
        exact ⟨c * e, by rw [map_mul, hc, he, map_mul]⟩
  have hzero := affineDim_affineZeroLocus_eq_zero_of_ringEquiv hP
    (RingEquiv.ofBijective (algebraMap K (MvPolynomial (Fin n) K ⧸ P))
      ⟨(algebraMap K (MvPolynomial (Fin n) K ⧸ P)).injective, hsurj⟩).symm
  omega

/-- The powers `1, x, …, x ^ s` of a transcendental element are linearly independent: a nontrivial
relation among them is a nonzero polynomial vanishing at `x`. -/
theorem linearIndependent_pow_of_transcendental {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} (hx : Transcendental R x) (s : ℕ) :
    LinearIndependent R fun i : Fin (s + 1) => x ^ (i : ℕ) := by
  have hinj := transcendental_iff_injective.1 hx
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  set q : Polynomial R := ∑ j : Fin (s + 1), Polynomial.C (g j) * Polynomial.X ^ (j : ℕ) with hqdef
  have hq : (Polynomial.aeval x) q = (Polynomial.aeval x) (0 : Polynomial R) := by
    rw [hqdef, map_sum]
    simpa [Algebra.smul_def] using hg
  have hcoeff := congrArg (fun r : Polynomial R => r.coeff (i : ℕ)) (hinj hq)
  simp only [hqdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i (fun j _ hj => by
    simp [show (i : ℕ) ≠ (j : ℕ) from fun h => hj (Fin.ext h.symm)]) (by simp)] at hcoeff
  simpa using hcoeff

/-- **Independence of powers of a coordinate.** On an irreducible affine algebraic set of positive
dimension over an algebraically closed field `K`, some coordinate function `y_j` has
`1, y_j, …, y_j ^ s` linearly independent over any subfield `F` of `K` — in the application
`F = 𝔽ₚ` inside `K = 𝔽̄ₚ`: the coordinate is transcendental over `K`, so its powers are
`K`-linearly independent, a fortiori `F`-linearly independent. -/
@[browning_sawin "lem_powers_independent"]
theorem exists_linearIndependent_pow_coordinate [IsAlgClosed K]
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime)
    (hdim : 0 < affineDim (affineZeroLocus P)) (s : ℕ) (F : Type*) [Field F] [Algebra F K]
    [Algebra F (FractionRing (MvPolynomial (Fin n) K ⧸ P))]
    [IsScalarTower F K (FractionRing (MvPolynomial (Fin n) K ⧸ P))] :
    ∃ j : Fin n, LinearIndependent F fun i : Fin (s + 1) =>
      (algebraMap (MvPolynomial (Fin n) K ⧸ P) (FractionRing (MvPolynomial (Fin n) K ⧸ P))
        (Ideal.Quotient.mk P (X j))) ^ (i : ℕ) := by
  obtain ⟨j, hj⟩ := exists_transcendental_coordinate hP hdim
  refine ⟨j, (linearIndependent_pow_of_transcendental hj s).restrict_scalars ?_⟩
  simpa [Algebra.smul_def] using (algebraMap F K).injective

end FunctionField

/-! ## The coefficient partition

The exponent tuples of `g` are partitioned by their coordinatewise residue class modulo `p`: the
class `0` carries the block `H`, the class `e_i` carries the block `G_i`, and all remaining classes
carry the block `U`. A tuple in class `0` is `pβ` for a unique `β`, one in class `e_i` is
`pβ + e_i`, and the degree bounds `|pβ| ≤ d` and `|pβ + e_i| ≤ d` are exactly `|β| ≤ t` and
`|β| ≤ s`. Only `p > 1` is used, not the oddness of `p`. -/

section Partition

variable {p n d : ℕ}

/-- The residue class of `α` modulo `p` has `j`-th entry the residue of `α j` modulo `p`. -/
theorem residueTuple_apply (α : Fin n →₀ ℕ) (j : Fin n) : residueTuple p α j = α j % p := rfl

/-- Scaling an exponent tuple scales its degree: `|mβ| = m |β|`. -/
theorem degree_nsmul (m : ℕ) (β : Fin n →₀ ℕ) : (m • β).degree = m * β.degree := by
  simp [Finsupp.degree_eq_sum, Finset.mul_sum]

/-- The tuple `pβ` lies in the residue class `0` modulo `p`. -/
theorem residueTuple_nsmul (β : Fin n →₀ ℕ) : residueTuple p (p • β) = 0 :=
  Finsupp.ext fun j => by simp [residueTuple_apply, Nat.mul_mod_right]

/-- For `p > 1` the tuple `pβ + e_i` lies in the residue class `e_i` modulo `p`. -/
theorem residueTuple_nsmul_add_single (hp : 1 < p) (β : Fin n →₀ ℕ) (i : Fin n) :
    residueTuple p (p • β + Finsupp.single i 1) = Finsupp.single i 1 := by
  refine Finsupp.ext fun j => ?_
  rcases eq_or_ne j i with rfl | hj
  · simp only [residueTuple_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_eq_same, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hp
  · simp [residueTuple_apply, Finsupp.single_eq_of_ne hj, Nat.mul_mod_right]

/-- `β ↦ pβ` is injective. -/
theorem nsmul_left_injective (hp : p ≠ 0) :
    Function.Injective fun β : Fin n →₀ ℕ => p • β := fun β γ h =>
  Finsupp.ext fun j => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) (by
    simpa using congrArg (fun δ : Fin n →₀ ℕ => δ j) h)

/-- The exponent tuples of degree at most `d` in the residue class `0` modulo `p` are exactly the
tuples `pβ` with `|β| ≤ t`. -/
theorem filter_residueTuple_eq_zero [Fact p.Prime] :
    ((monomialsLE n d).filter fun α => residueTuple p α = 0)
      = (monomialsLE n (upperBlockLength p d)).image fun β => p • β := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  ext α
  simp only [Finset.mem_filter, Finset.mem_image, mem_monomialsLE]
  refine ⟨fun ⟨hdeg, hres⟩ => ?_, fun ⟨β, hβ, hα⟩ => ?_⟩
  · refine ⟨Finsupp.mapRange (· / p) (Nat.zero_div p) α, ?_, ?_⟩
    · rw [upperBlockLength, Nat.le_div_iff_mul_le hp, mul_comm]
      have hd : p * (Finsupp.mapRange (· / p) (Nat.zero_div p) α).degree = α.degree := by
        rw [← degree_nsmul]
        congr 1
        refine Finsupp.ext fun j => ?_
        have hdvd : p ∣ α j := Nat.dvd_of_mod_eq_zero
          (by simpa [residueTuple_apply] using congrArg (fun γ : Fin n →₀ ℕ => γ j) hres)
        simpa using Nat.mul_div_cancel' hdvd
      omega
    · refine Finsupp.ext fun j => ?_
      have hdvd : p ∣ α j := Nat.dvd_of_mod_eq_zero
        (by simpa [residueTuple_apply] using congrArg (fun γ : Fin n →₀ ℕ => γ j) hres)
      simpa using Nat.mul_div_cancel' hdvd
  · subst hα
    rw [upperBlockLength, Nat.le_div_iff_mul_le hp, mul_comm] at hβ
    exact ⟨by rw [degree_nsmul]; omega, residueTuple_nsmul β⟩

/-- The exponent tuples of degree at most `d` in the residue class `e_i` modulo `p` are exactly the
tuples `pβ + e_i` with `|β| ≤ s`. -/
theorem filter_residueTuple_eq_single [Fact p.Prime] (hd : 1 ≤ d) (i : Fin n) :
    ((monomialsLE n d).filter fun α => residueTuple p α = Finsupp.single i 1)
      = (monomialsLE n (lowerBlockLength p d)).image fun β => p • β + Finsupp.single i 1 := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  ext α
  simp only [Finset.mem_filter, Finset.mem_image, mem_monomialsLE]
  refine ⟨fun ⟨hdeg, hres⟩ => ?_, fun ⟨β, hβ, hα⟩ => ?_⟩
  · have hmod : ∀ j, α j % p = (Finsupp.single i 1 : Fin n →₀ ℕ) j := fun j => by
      simpa [residueTuple_apply] using congrArg (fun γ : Fin n →₀ ℕ => γ j) hres
    set β := Finsupp.mapRange (· / p) (Nat.zero_div p) α with hβdef
    have hsum : p • β + Finsupp.single i 1 = α := by
      refine Finsupp.ext fun j => ?_
      rcases eq_or_ne j i with rfl | hj
      · have h := hmod j
        simp only [Finsupp.single_eq_same] at h
        have hdm := Nat.div_add_mod (α j) p
        simp only [hβdef, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
          Finsupp.mapRange_apply, Finsupp.single_eq_same]
        omega
      · have h := hmod j
        rw [Finsupp.single_eq_of_ne hj] at h
        have hdvd : p ∣ α j := Nat.dvd_of_mod_eq_zero h
        simpa [hβdef, Finsupp.single_eq_of_ne hj] using Nat.mul_div_cancel' hdvd
    refine ⟨β, ?_, hsum⟩
    rw [lowerBlockLength, Nat.le_div_iff_mul_le hp, mul_comm]
    have hdegα : p * β.degree + 1 = α.degree := by
      rw [← degree_nsmul, ← Finsupp.degree_single i 1, ← map_add, hsum]
    omega
  · subst hα
    rw [lowerBlockLength, Nat.le_div_iff_mul_le hp, mul_comm] at hβ
    refine ⟨?_, residueTuple_nsmul_add_single hp1 β i⟩
    rw [map_add, degree_nsmul, Finsupp.degree_single]
    omega

variable [Fact p.Prime]

/-- `H ^ p` is the part of `g` supported on the exponents in the residue class `0`: the `p`-th
power map is a ring homomorphism in characteristic `p`, and `c ^ p = c` for `c ∈ 𝔽ₚ`. -/
theorem blockH_pow (ε : SignFamily (monomialsLE n d)) :
    blockH p n d ε ^ p
      = ∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α = 0,
          monomial α ((signOf ε α : ℤ) : ZMod p) := by
  have : ExpChar (MvPolynomial (Fin n) (ZMod p)) p := ExpChar.prime Fact.out
  have hfrob : blockH p n d ε ^ p
      = ∑ β ∈ monomialsLE n (upperBlockLength p d),
          monomial (p • β) ((signOf ε (p • β) : ℤ) : ZMod p) := by
    rw [blockH, ← frobenius_def, map_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [frobenius_def, monomial_pow, ZMod.pow_card]
  rw [hfrob, filter_residueTuple_eq_zero,
    Finset.sum_image fun x _ y _ h => nsmul_left_injective (Fact.out (p := p.Prime)).ne_zero h]

/-- `y_i G_i ^ p` is the part of `g` supported on the exponents in the residue class `e_i`. -/
theorem X_mul_blockG_pow (hd : 1 ≤ d) (ε : SignFamily (monomialsLE n d)) (i : Fin n) :
    X i * blockG p n d ε i ^ p
      = ∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α = Finsupp.single i 1,
          monomial α ((signOf ε α : ℤ) : ZMod p) := by
  have : ExpChar (MvPolynomial (Fin n) (ZMod p)) p := ExpChar.prime Fact.out
  have hfrob : X i * blockG p n d ε i ^ p
      = ∑ β ∈ monomialsLE n (lowerBlockLength p d),
          monomial (p • β + Finsupp.single i 1)
            ((signOf ε (p • β + Finsupp.single i 1) : ℤ) : ZMod p) := by
    rw [blockG, ← frobenius_def, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [frobenius_def, monomial_pow, ZMod.pow_card, X_eq_monomial_single_one,
      monomial_mul_monomial, one_mul, add_comm (Finsupp.single i 1) (p • β)]
  have hinj : ∀ β ∈ monomialsLE n (lowerBlockLength p d),
      ∀ γ ∈ monomialsLE n (lowerBlockLength p d),
      p • β + Finsupp.single i 1 = p • γ + Finsupp.single i 1 → β = γ := fun β _ γ _ h =>
    nsmul_left_injective (Fact.out (p := p.Prime)).ne_zero (add_right_cancel h)
  rw [hfrob, filter_residueTuple_eq_single hd i, Finset.sum_image hinj]

/-- **The coefficient partition.** The affine sign polynomial splits as
`g = U + ∑ y_i G_i^p + H^p`: the blocks collect the terms of `g` whose exponent lies in the residue
classes outside `{0, e₁, …, e_n}`, in the class `e_i`, and in the class `0` respectively, and every
term of `g` occurs in exactly one of them. -/
@[browning_sawin "lem_partition_identity"]
theorem affineSignPoly_eq_blockU_add_sum_add_blockH_pow (hd : 1 ≤ d)
    (ε : SignFamily (monomialsLE n d)) :
    affineSignPoly p n d ε
      = blockU p n d ε + (∑ i : Fin n, X i * blockG p n d ε i ^ p) + blockH p n d ε ^ p := by
  classical
  set f : (Fin n →₀ ℕ) → MvPolynomial (Fin n) (ZMod p) :=
    fun α => monomial α ((signOf ε α : ℤ) : ZMod p) with hf
  have hsplit : (∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α ∈ specialTuples n, f α)
      + (∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α ∉ specialTuples n, f α)
      = ∑ α ∈ monomialsLE n d, f α :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hmaps : ∀ α ∈ (monomialsLE n d).filter fun α => residueTuple p α ∈ specialTuples n,
      residueTuple p α ∈ specialTuples n := fun α hα => (Finset.mem_filter.1 hα).2
  have hinner : ∀ c ∈ specialTuples n,
      (((monomialsLE n d).filter fun α => residueTuple p α ∈ specialTuples n).filter
          fun α => residueTuple p α = c)
        = (monomialsLE n d).filter fun α => residueTuple p α = c := by
    intro c hc
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun α _ =>
      ⟨fun h => h.2, fun h => ⟨h ▸ hc, h⟩⟩
  have hfib : ∑ c ∈ specialTuples n, ∑ α ∈ (monomialsLE n d).filter
      fun α => residueTuple p α = c, f α
      = ∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α ∈ specialTuples n, f α := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
    exact Finset.sum_congr rfl fun c hc => by rw [hinner c hc]
  have h0notin : (0 : Fin n →₀ ℕ) ∉ Finset.univ.image fun i : Fin n => Finsupp.single i 1 := by
    simp only [Finset.mem_image, not_exists]
    intro i hi
    exact absurd (congrArg (fun γ : Fin n →₀ ℕ => γ i) hi.2) (by simp)
  have hsingle : ∑ c ∈ specialTuples n, ∑ α ∈ (monomialsLE n d).filter
      fun α => residueTuple p α = c, f α
      = (∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α = 0, f α)
        + ∑ i : Fin n, ∑ α ∈ (monomialsLE n d).filter
            fun α => residueTuple p α = Finsupp.single i 1, f α := by
    rw [specialTuples, Finset.sum_insert h0notin,
      Finset.sum_image fun i _ j _ h => Finsupp.single_left_injective one_ne_zero h]
  rw [affineSignPoly, blockU, blockH_pow, Finset.sum_congr rfl
      fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => X_mul_blockG_pow hd ε i,
    ← hsplit, ← hfib, hsingle]
  abel

/-- In characteristic `p` the derivative of a `p`-th power vanishes: `∂ᵢ(F^p) = p F^{p-1} ∂ᵢF` and
`p = 0`. -/
theorem pderiv_pow_char (i : Fin n) (F : MvPolynomial (Fin n) (ZMod p)) :
    pderiv i (F ^ p) = 0 := by
  rw [Derivation.leibniz_pow, nsmul_eq_mul, CharP.cast_eq_zero (MvPolynomial (Fin n) (ZMod p)) p,
    zero_mul]

/-- **Derivatives of the partition.** Differentiating `g = U + ∑ y_j G_j^p + H^p` with respect to
`y_i` kills every `p`-th power and leaves `∂ᵢ g = ∂ᵢ U + G_i^p`. -/
@[browning_sawin "lem_partition_derivative"]
theorem pderiv_affineSignPoly (hd : 1 ≤ d) (ε : SignFamily (monomialsLE n d)) (i : Fin n) :
    pderiv i (affineSignPoly p n d ε) = pderiv i (blockU p n d ε) + blockG p n d ε i ^ p := by
  rw [affineSignPoly_eq_blockU_add_sum_add_blockH_pow hd, map_add, map_add, map_sum,
    pderiv_pow_char, add_zero]
  congr 1
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h),
    pderiv_mul, pderiv_X_self, pderiv_pow_char, one_mul, mul_zero, add_zero]
  rw [pderiv_mul, pderiv_X_of_ne hj, pderiv_pow_char, zero_mul, mul_zero, add_zero]

end Partition

/-! ## A prescribed restriction to a component

The blocks `G_i` enter the reveal argument one component at a time: on an irreducible component
`V = Z(P)` of the critical locus reached so far, the equation `∂ᵢ U + G_i^p = 0` says that the
restriction of `G_i` to the function field `𝔽̄ₚ(V)` has a prescribed `p`-th power. At most one
element of a field of characteristic `p` has a given `p`-th power, so the equation prescribes that
restriction outright; the restriction is the sign sum `∑_{|β| ≤ s} ε_{pβ + e_i} y^β|_V`, in which
the `s + 1` powers of a transcendental coordinate occur, so the rank bound gives probability at
most `2^{-(s+1)}`. -/

section Component

open MeasureTheory

/-- `K(V)`, the function field of the irreducible affine algebraic set `V = Z(P)` cut out by a
prime ideal `P` of `K[y₁, …, y_m]`: the fraction field of its coordinate ring. -/
abbrev functionField {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K)) : Type _ :=
  FractionRing (MvPolynomial (Fin m) K ⧸ P)

/-- Restriction to `V = Z(P)` of a polynomial with coefficients in a subfield `k` of `K`, read in
the function field `K(V)`: reduce the coefficients into `K`, restrict to `V` by passing to the
coordinate ring `K[y₁, …, y_m] ⧸ P`, and view the result in the fraction field of that ring. -/
noncomputable def restrictToFunctionField (k : Type*) [Field k] {K : Type*} [Field K] [Algebra k K]
    {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K)) :
    MvPolynomial (Fin m) k →+* functionField P :=
  (algebraMap (MvPolynomial (Fin m) K ⧸ P) (functionField P)).comp
    ((Ideal.Quotient.mk P).comp (MvPolynomial.map (algebraMap k K)))

/-- The restriction of a power of a coordinate to `V = Z(P)` is that power of the restricted
coordinate. -/
theorem restrictToFunctionField_monomial_single {k K : Type*} [Field k] [Field K] [Algebra k K]
    {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K)) (j : Fin m) (e : ℕ) :
    restrictToFunctionField k P (monomial (Finsupp.single j e) 1)
      = algebraMap (MvPolynomial (Fin m) K ⧸ P) (functionField P)
          (Ideal.Quotient.mk P (X j)) ^ e := by
  rw [← X_pow_eq_monomial, map_pow]
  simp [restrictToFunctionField]

variable {p n d : ℕ}

/-- Dividing out `p` recovers `β` from the exponent tuple `pβ + e_i`. -/
theorem mapRange_div_nsmul_add_single (hp : 1 < p) (β : Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.mapRange (· / p) (Nat.zero_div p) (p • β + Finsupp.single i 1) = β := by
  refine Finsupp.ext fun j => ?_
  simp only [Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rcases eq_or_ne j i with rfl | hj
  · rw [Finsupp.single_eq_same, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp, add_zero]
  · rw [Finsupp.single_eq_of_ne hj, add_zero, Nat.mul_div_cancel_left _ (by omega : 0 < p)]

set_option synthInstance.maxHeartbeats 1000000 in
-- The function field `K(V)` is a localization of a quotient of a polynomial ring, and neither
-- synthesizing the scalar actions on it nor unifying two descriptions of one of them fits the
-- default budgets.
set_option maxHeartbeats 1000000 in
/-- **A prescribed restriction of `G_i` to a component is unlikely.** Let `V = Z(P)` be an
irreducible affine algebraic set of positive dimension over an algebraically closed field `K` of
characteristic an odd prime `p`, and let `d ≥ 1`. Then for every element `v` of the function field
`K(V)` the restriction of the block `G_i` to `V` has `p`-th power `v` with probability at most
`2^{-(s+1)}`, where `s = ⌊(d-1)/p⌋` is the length of that block.

At most one element of `K(V)` has `p`-th power `v` (`subsingleton_setOf_pow_eq`), so the event is
contained in the event that the restriction of `G_i` takes one prescribed value. That restriction
is the sign sum `∑_α ε_α w_α`, where `w_α` is the restriction of `y^β` when `α = pβ + e_i` and `0`
otherwise; the `s + 1` signs indexed by `α = p m e_j + e_i`, `0 ≤ m ≤ s`, contribute the powers
`1, y_j, …, y_j^s` of a coordinate that `exists_linearIndependent_pow_coordinate` makes
`𝔽ₚ`-linearly independent, and `signMeasure_sign_sum_le_inv_two_pow` bounds the probability of a
prescribed value of such a sum by `2^{-(s+1)}`. -/
theorem signMeasure_pow_restrictToFunctionField_blockG_le [Fact p.Prime] (hodd : Odd p) (hd : 1 ≤ d)
    {K : Type*} [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    {P : Ideal (MvPolynomial (Fin n) K)} (hP : P.IsPrime)
    [Algebra (ZMod p) (functionField P)] [IsScalarTower (ZMod p) K (functionField P)]
    (hdim : 0 < affineDim (affineZeroLocus P)) (i : Fin n) (v : functionField P) :
    signMeasure ↥(monomialsLE n d)
        {ε | restrictToFunctionField (ZMod p) P (blockG p n d ε i) ^ p = v}
      ≤ ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹ := by
  classical
  have := hP
  have : IsDomain (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.isDomain P
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  set R := restrictToFunctionField (ZMod p) P with hR
  set W : (Fin n →₀ ℕ) → functionField P := fun α =>
    if residueTuple p α = Finsupp.single i 1 then
      R (monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) α) 1)
    else 0 with hW
  have hWpos : ∀ α : Fin n →₀ ℕ, residueTuple p α = Finsupp.single i 1 →
      W α = R (monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) α) 1) := by
    intro α hα
    simp only [hW]
    rw [ite_eq_left hα]
  have hWneg : ∀ α : Fin n →₀ ℕ, residueTuple p α ≠ Finsupp.single i 1 → W α = 0 := by
    intro α hα
    simp only [hW]
    rw [ite_eq_right hα]
  have hrep : ∀ ε : SignFamily (monomialsLE n d),
      R (blockG p n d ε i) = ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) := by
    intro ε
    have hzsmul : ∀ (β : Fin n →₀ ℕ) (z : ℤˣ),
        (monomial β (((z : ℤ) : ZMod p)) : MvPolynomial (Fin n) (ZMod p))
          = (z : ℤ) • monomial β 1 := fun β z => by
      rw [zsmul_eq_mul, ← map_intCast (C : ZMod p →+* MvPolynomial (Fin n) (ZMod p)) (z : ℤ),
        C_mul_monomial, mul_one]
    have hlhs : R (blockG p n d ε i)
        = ∑ β ∈ monomialsLE n (lowerBlockLength p d),
            (signOf ε (p • β + Finsupp.single i 1) : ℤ) • R (monomial β 1) := by
      rw [blockG, map_sum]
      exact Finset.sum_congr rfl fun β _ => by rw [hzsmul, map_zsmul]
    have hrhs : ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ)
        = ∑ α ∈ monomialsLE n d, (signOf ε α : ℤ) • W α := by
      rw [← Finset.sum_coe_sort (monomialsLE n d) fun α => (signOf ε α : ℤ) • W α]
      exact Finset.sum_congr rfl fun α _ => by rw [signOf_of_mem ε α.2]
    have hzero : ∑ α ∈ (monomialsLE n d).filter
        (fun α => ¬ residueTuple p α = Finsupp.single i 1), (signOf ε α : ℤ) • W α = 0 :=
      Finset.sum_eq_zero fun α hα => by
        rw [hWneg α (Finset.mem_filter.1 hα).2]
        simp
    have hsplit : ∑ α ∈ monomialsLE n d, (signOf ε α : ℤ) • W α
        = ∑ α ∈ (monomialsLE n d).filter (fun α => residueTuple p α = Finsupp.single i 1),
            (signOf ε α : ℤ) • W α := by
      rw [← Finset.sum_filter_add_sum_filter_not (monomialsLE n d)
        (fun α => residueTuple p α = Finsupp.single i 1) (fun α => (signOf ε α : ℤ) • W α), hzero,
        add_zero]
    have himage : ∑ α ∈ (monomialsLE n d).filter
          (fun α => residueTuple p α = Finsupp.single i 1), (signOf ε α : ℤ) • W α
        = ∑ β ∈ monomialsLE n (lowerBlockLength p d),
            (signOf ε (p • β + Finsupp.single i 1) : ℤ) • R (monomial β 1) := by
      rw [filter_residueTuple_eq_single hd i, Finset.sum_image fun β _ γ _ h =>
        nsmul_left_injective (Fact.out (p := p.Prime)).ne_zero (add_right_cancel h)]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [hWpos _ (residueTuple_nsmul_add_single hp1 β i), mapRange_div_nsmul_add_single hp1]
    rw [hlhs, hrhs, hsplit, himage]
  obtain ⟨j₀, hli⟩ :=
    exists_linearIndependent_pow_coordinate hP hdim (lowerBlockLength p d) (ZMod p)
  have hmem : ∀ e : ℕ, e ≤ lowerBlockLength p d →
      p • Finsupp.single j₀ e + Finsupp.single i 1 ∈ monomialsLE n d := by
    intro e he
    have hps : p * lowerBlockLength p d ≤ d - 1 := by
      rw [lowerBlockLength, mul_comm]
      exact Nat.div_mul_le_self _ _
    have hpe : p * e ≤ p * lowerBlockLength p d := Nat.mul_le_mul_left p he
    rw [mem_monomialsLE, map_add, degree_nsmul, Finsupp.degree_single, Finsupp.degree_single]
    omega
  set ψ : Fin (lowerBlockLength p d + 1) → ↥(monomialsLE n d) := fun e =>
    ⟨p • Finsupp.single j₀ (e : ℕ) + Finsupp.single i 1, hmem e (Nat.lt_succ_iff.1 e.is_lt)⟩ with hψ
  have hψval : ∀ e : Fin (lowerBlockLength p d + 1), W (ψ e : Fin n →₀ ℕ)
      = algebraMap (MvPolynomial (Fin n) K ⧸ P) (functionField P)
          (Ideal.Quotient.mk P (X j₀)) ^ (e : ℕ) := by
    intro e
    rw [hψ, hWpos _ (residueTuple_nsmul_add_single hp1 _ i), mapRange_div_nsmul_add_single hp1, hR,
      restrictToFunctionField_monomial_single]
  have hψinj : Function.Injective ψ := by
    intro e e' hee
    refine Fin.ext ?_
    have h1 := congrArg (fun α : ↥(monomialsLE n d) =>
      Finsupp.mapRange (· / p) (Nat.zero_div p) (α : Fin n →₀ ℕ)) hee
    simp only [hψ] at h1
    rw [mapRange_div_nsmul_add_single hp1, mapRange_div_nsmul_add_single hp1] at h1
    simpa using congrArg (fun γ : Fin n →₀ ℕ => γ j₀) h1
  set J : Finset ↥(monomialsLE n d) := Finset.image ψ Finset.univ with hJ
  have hJcard : J.card = lowerBlockLength p d + 1 := by
    rw [hJ, Finset.card_image_of_injective _ hψinj, Finset.card_univ, Fintype.card_fin]
  have hbij : Function.Bijective fun e : Fin (lowerBlockLength p d + 1) =>
      (⟨ψ e, Finset.mem_image_of_mem ψ (Finset.mem_univ e)⟩ : ↥J) := by
    refine ⟨fun e e' h => hψinj (Subtype.ext_iff.1 h), fun a => ?_⟩
    obtain ⟨e, -, he⟩ := Finset.mem_image.1 a.2
    exact ⟨e, Subtype.ext he⟩
  have hJli : LinearIndependent (ZMod p)
      fun a : ↥J => W ((a : ↥(monomialsLE n d)) : Fin n →₀ ℕ) := by
    refine (linearIndependent_equiv' (e := Equiv.ofBijective _ hbij)
      (f := fun a : ↥J => W ((a : ↥(monomialsLE n d)) : Fin n →₀ ℕ))
      (g := fun e : Fin (lowerBlockLength p d + 1) =>
        algebraMap (MvPolynomial (Fin n) K ⧸ P) (functionField P)
          (Ideal.Quotient.mk P (X j₀)) ^ (e : ℕ)) (_root_.funext fun e => ?_)).1 hli
    exact hψval e
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hodd
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p 2]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have : CharP (functionField P) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (functionField P)).injective p
  have : ExpChar (functionField P) p := ExpChar.prime Fact.out
  by_cases hex : ∃ c : functionField P, c ^ p = v
  · obtain ⟨c, hc⟩ := hex
    have hsub : {ε : SignFamily (monomialsLE n d) | R (blockG p n d ε i) ^ p = v}
        ⊆ {ε | ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) = c} := by
      intro ε hε
      rw [Set.mem_ofPred_eq, ← hrep ε]
      exact subsingleton_setOf_pow_eq v hε hc
    calc signMeasure ↥(monomialsLE n d) {ε | R (blockG p n d ε i) ^ p = v}
        ≤ signMeasure ↥(monomialsLE n d)
            {ε | ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) = c} :=
          measure_mono hsub
      _ ≤ ((2 : ℝ≥0∞) ^ J.card)⁻¹ :=
          signMeasure_sign_sum_le_inv_two_pow (k := ZMod p) (V := functionField P)
            (v := fun α : ↥(monomialsLE n d) => W (α : Fin n →₀ ℕ)) (J := J) h2 hJli c
      _ = ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹ := by rw [hJcard]
  · have hempty : {ε : SignFamily (monomialsLE n d) | R (blockG p n d ε i) ^ p = v} = ∅ := by
      ext ε
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hex ⟨_, h⟩
    rw [hempty, measure_empty]
    simp

end Component

/-! ## Independence of the blocks

The signs `ε_α` are indexed by the exponent tuples `α` of degree at most `d`, and each of the
`n + 2` blocks uses only the signs whose exponent lies in its own residue class modulo `p`: the
block `H` those with `α ≡ 0`, the block `G_i` those with `α ≡ e_i`, and the block `U` all the rest.
These index sets are the fibres of `blockOf`, hence pairwise disjoint, and functions of disjoint
groups of an independent family of random variables are independent. -/

section Independence

open MeasureTheory ProbabilityTheory

/-- A family of independent uniform signs is uniform: a single sign family has probability
`2 ^ (-#ι)`. -/
theorem signMeasure_singleton {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ι → ℤˣ) :
    signMeasure ι {ε} = ((2 : ℝ≥0∞) ^ Fintype.card ι)⁻¹ := by
  rw [signMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ε),
    PMF.uniformOfFintype_apply, Fintype.card_pi]
  simp [Fintype.card_units_int]

/-- Independence is preserved by composing an independent family with a measure-preserving map. -/
theorem iIndepFun_comp_of_measurePreserving {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'} {e : Ω → Ω'}
    (he : MeasurePreserving e μ ν) {β : ι → Type*} [m : ∀ i, MeasurableSpace (β i)]
    {g : ∀ i, Ω' → β i} (hg : ∀ i, Measurable (g i)) (h : iIndepFun g ν) :
    iIndepFun (fun i ω => g i (e ω)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro S sets hsets
  have hmeas : ∀ i ∈ S, MeasurableSet (g i ⁻¹' sets i) := fun i hi => hg i (hsets i hi)
  have hpre : (⋂ i ∈ S, (fun ω => g i (e ω)) ⁻¹' sets i) = e ⁻¹' ⋂ i ∈ S, g i ⁻¹' sets i := by
    simp only [Set.preimage_iInter]
    rfl
  calc μ (⋂ i ∈ S, (fun ω => g i (e ω)) ⁻¹' sets i)
      = ν (⋂ i ∈ S, g i ⁻¹' sets i) := by
        rw [hpre]
        exact he.measure_preimage
          (MeasurableSet.biInter S.countable_toSet hmeas).nullMeasurableSet
    _ = ∏ i ∈ S, ν (g i ⁻¹' sets i) := h S hsets
    _ = ∏ i ∈ S, μ ((fun ω => g i (e ω)) ⁻¹' sets i) :=
        Finset.prod_congr rfl fun i hi =>
          (he.measure_preimage (hmeas i hi).nullMeasurableSet).symm

/-- **Functions of disjoint groups of independent signs are independent.** Let the index set of a
family of independent uniform signs be partitioned into the fibres of a map `c`, and let `f k` be a
function of the signs indexed by the fibre over `k` alone. Then the family `f` is mutually
independent: the sign family factors, measurably and measure-preservingly, as the product over `k`
of its restrictions to the fibres, and `f k` is a function of the `k`-th factor only. -/
theorem iIndepFun_of_forall_eq_on_fiber {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Finite κ]
    {β : κ → Type*} [m : ∀ k, MeasurableSpace (β k)] (c : ι → κ) {f : ∀ k, (ι → ℤˣ) → β k}
    (hf : ∀ (k : κ) (ε ε' : ι → ℤˣ), (∀ i, c i = k → ε i = ε' i) → f k ε = f k ε') :
    iIndepFun f (signMeasure ι) := by
  classical
  have := Fintype.ofFinite κ
  set e : (ι → ℤˣ) → ∀ k : κ, ({i : ι // c i = k} → ℤˣ) := fun ε k i => ε i.1 with he
  set X : ∀ k : κ, ({i : ι // c i = k} → ℤˣ) → β k :=
    fun k ω => f k fun i => if h : c i = k then ω ⟨i, h⟩ else 1 with hX
  have hfe : f = fun k ε => X k (e ε k) := by
    funext k ε
    refine (hf k _ ε fun i hi => ?_).symm
    simp only [he]
    rw [dite_eq_left hi]
  have hebij : Function.Bijective e := by
    refine ⟨fun ε ε' hee => funext fun i => congrFun (congrFun hee (c i)) ⟨i, rfl⟩, fun ω => ?_⟩
    refine ⟨fun i => ω (c i) ⟨i, rfl⟩, ?_⟩
    funext k x
    obtain ⟨i, hi⟩ := x
    subst hi
    rfl
  have hcard : ∑ k : κ, Fintype.card {i : ι // c i = k} = Fintype.card ι := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv c)
  have hmp : MeasurePreserving e (signMeasure ι)
      (Measure.pi fun k : κ => signMeasure {i : ι // c i = k}) := by
    refine ⟨Measurable.of_discrete, Measure.ext_of_singleton fun ω => ?_⟩
    obtain ⟨ε₀, hε₀⟩ := hebij.surjective ω
    have hpre : e ⁻¹' {ω} = {ε₀} := by
      ext ε
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hεω => hebij.injective (hεω.trans hε₀.symm), fun hε => hε ▸ hε₀⟩
    rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton ω), hpre,
      signMeasure_singleton, ← Set.univ_pi_singleton ω, Measure.pi_pi,
      Finset.prod_congr rfl fun k (_ : k ∈ (Finset.univ : Finset κ)) =>
        signMeasure_singleton (ω k)]
    simp only [ENNReal.inv_pow]
    rw [Finset.prod_pow_eq_pow_sum, hcard]
  rw [hfe]
  exact iIndepFun_comp_of_measurePreserving hmp (fun _ => Measurable.of_discrete)
    (iIndepFun_pi fun _ => Measurable.of_discrete.aemeasurable)

/-- An index for the `n + 2` coefficient blocks of `g`: the block `U`, the blocks `G_i` and the
block `H`. -/
inductive BlockIndex (n : ℕ) where
  /-- The block `U`. -/
  | u : BlockIndex n
  /-- The block `G_i`. -/
  | g (i : Fin n) : BlockIndex n
  /-- The block `H`. -/
  | h : BlockIndex n
  deriving DecidableEq, Fintype

variable {p n d : ℕ}

open Classical in
/-- The block that carries the coefficient of the exponent tuple `α`: the block `H` if `α ≡ 0`, the
block `G_i` if `α ≡ e_i`, and the block `U` otherwise, congruences being coordinatewise modulo
`p`. -/
noncomputable def blockOf (p n : ℕ) (α : Fin n →₀ ℕ) : BlockIndex n :=
  if residueTuple p α = 0 then .h
  else if h : ∃ i, residueTuple p α = Finsupp.single i 1 then .g h.choose
  else .u

/-- An exponent tuple in the residue class `0` modulo `p` belongs to the block `H`. -/
theorem blockOf_eq_h {α : Fin n →₀ ℕ} (h : residueTuple p α = 0) : blockOf p n α = .h := by
  rw [blockOf, ite_eq_left h]

/-- An exponent tuple in the residue class `e_i` modulo `p` belongs to the block `G_i`. -/
theorem blockOf_eq_g {α : Fin n →₀ ℕ} {i : Fin n} (h : residueTuple p α = Finsupp.single i 1) :
    blockOf p n α = .g i := by
  have hne : residueTuple p α ≠ 0 := fun h0 => by
    rw [h] at h0
    simpa using congrArg (fun γ : Fin n →₀ ℕ => γ i) h0
  have hex : ∃ j, residueTuple p α = Finsupp.single j 1 := ⟨i, h⟩
  have hchoose : i = hex.choose :=
    Finsupp.single_left_injective one_ne_zero (h.symm.trans hex.choose_spec)
  rw [blockOf, ite_eq_right hne, dite_eq_left hex, hchoose]

/-- An exponent tuple whose residue class modulo `p` is neither `0` nor any `e_i` belongs to the
block `U`. -/
theorem blockOf_eq_u {α : Fin n →₀ ℕ} (h0 : residueTuple p α ≠ 0)
    (h1 : ∀ i, residueTuple p α ≠ Finsupp.single i 1) : blockOf p n α = .u := by
  rw [blockOf, ite_eq_right h0, dite_eq_right (fun ⟨i, hi⟩ => h1 i hi)]

/-- The `n + 2` coefficient blocks of `g`, as one family of random polynomials. -/
noncomputable def block (p n d : ℕ) (ε : SignFamily (monomialsLE n d)) :
    BlockIndex n → MvPolynomial (Fin n) (ZMod p)
  | .u => blockU p n d ε
  | .g i => blockG p n d ε i
  | .h => blockH p n d ε

/-- The member of the family `block` indexed by `.u` is the block `U`. -/
@[simp]
theorem block_u (ε : SignFamily (monomialsLE n d)) : block p n d ε .u = blockU p n d ε := rfl

/-- The member of the family `block` indexed by `.g i` is the block `G_i`. -/
@[simp]
theorem block_g (ε : SignFamily (monomialsLE n d)) (i : Fin n) :
    block p n d ε (.g i) = blockG p n d ε i := rfl

/-- The member of the family `block` indexed by `.h` is the block `H`. -/
@[simp]
theorem block_h (ε : SignFamily (monomialsLE n d)) : block p n d ε .h = blockH p n d ε := rfl

/-- Two sign families that agree on the signs belonging to one block give that block the same
coefficient at every exponent tuple assigned to it. -/
theorem signOf_congr {ε ε' : SignFamily (monomialsLE n d)} {k : BlockIndex n}
    (h : ∀ i : ↥(monomialsLE n d), blockOf p n i.1 = k → ε i = ε' i) {α : Fin n →₀ ℕ}
    (hα : blockOf p n α = k) : signOf ε α = signOf ε' α := by
  by_cases hmem : α ∈ monomialsLE n d
  · rw [signOf_of_mem ε hmem, signOf_of_mem ε' hmem]
    exact h ⟨α, hmem⟩ hα
  · simp [signOf, hmem]

/-- Each block is a function of the signs assigned to it alone. -/
theorem block_congr (hp : 1 < p) (k : BlockIndex n) {ε ε' : SignFamily (monomialsLE n d)}
    (h : ∀ i : ↥(monomialsLE n d), blockOf p n i.1 = k → ε i = ε' i) :
    block p n d ε k = block p n d ε' k := by
  cases k with
  | u =>
      rw [block_u, block_u, blockU, blockU]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hres := (Finset.mem_filter.1 hα).2
      rw [signOf_congr h (blockOf_eq_u
        (fun h0 => hres (h0 ▸ Finset.mem_insert_self _ _))
        (fun i hi => hres (hi ▸ Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_univ i)))))]
  | g i =>
      rw [block_g, block_g, blockG, blockG]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [signOf_congr h (blockOf_eq_g (residueTuple_nsmul_add_single hp β i))]
  | h =>
      rw [block_h, block_h, blockH, blockH]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [signOf_congr h (blockOf_eq_h (residueTuple_nsmul β))]

/-- **The blocks are independent.** The `n + 2` random polynomials `U, G₁, …, G_n, H` are mutually
independent: the exponent tuples of degree at most `d` are partitioned by their residue class
modulo `p` into the index set of `U`, the index sets of the `G_i` and the index set of `H`, each
block is a function of the signs indexed by its own set only, and functions of disjoint groups of
an independent family of random variables are independent. Independence is with respect to the
discrete `σ`-algebra on the space of polynomials, which is the strongest form of the statement. -/
@[browning_sawin "lem_blocks_independent"]
theorem iIndepFun_block (hp : 1 < p) :
    iIndepFun (m := fun _ : BlockIndex n => (⊤ : MeasurableSpace (MvPolynomial (Fin n) (ZMod p))))
      (fun k ε => block p n d ε k) (signMeasure ↥(monomialsLE n d)) :=
  iIndepFun_of_forall_eq_on_fiber (m := fun _ => ⊤)
    (fun i : ↥(monomialsLE n d) => blockOf p n i.1) fun k _ _ h => block_congr hp k h

end Independence

/-! ## The size of a finite critical locus

A finite affine algebraic set has one irreducible component for each of its points, and the
projective closure of a point has degree `1`, so the invariant `δ` of such a set is exactly the
number of its points. The affine Bézout inequality `AffineBezout`, applied to the `n` partial
derivatives of `g`, each of degree at most `D = d - 1`, bounds that number by `D ^ n`. -/

section FiniteAlgebraicSet

variable {K : Type u} [Field K] {n : ℕ}

/-- The number of elements of a finite set, as a sum of ones. -/
theorem finsum_mem_one_eq_ncard {α : Type*} {s : Set α} (hs : s.Finite) :
    ∑ᶠ _ ∈ s, (1 : ℕ) = s.ncard := by
  have h1 : ∑ᶠ _ ∈ s, (1 : ℕ) = ∑ᶠ _ ∈ (↑hs.toFinset : Set α), (1 : ℕ) := by rw [hs.coe_toFinset]
  rw [h1, finsum_mem_coe_finset, Finset.sum_const, smul_eq_mul, mul_one,
    Set.ncard_eq_toFinset_card s hs]

/-- `|β|` as a sum over the support of `β`. -/
theorem degree_eq_finsuppSum (β : Fin n →₀ ℕ) : β.degree = β.sum fun _ e => e := rfl

/-! ### Forms along a line -/

/-- The exponents occurring in a form homogeneous of degree `q` all have degree `q`. -/
theorem degree_eq_of_isHomogeneous {q : ℕ} {F : MvPolynomial (Fin n) K} (hF : F.IsHomogeneous q)
    {β : Fin n →₀ ℕ} (hβ : β ∈ F.support) : β.degree = q := by
  have h := hF (mem_support_iff.1 hβ)
  rw [Finsupp.weight_apply] at h
  rw [degree_eq_finsuppSum]
  simpa using h

/-! ### The projective set cut out by a single point -/

section Point

variable (P : Projectivization K (Fin (n + 1) → K))

/-- The cone over a single projective point is the line spanned by a representative of it. -/
theorem mem_affineCone_singleton {v : Fin (n + 1) → K} :
    v ∈ affineCone {P} ↔ ∃ c : K, v = c • P.rep := by
  simp [affineCone]

/-- A representative of a projective point lies on the cone over that point. -/
theorem rep_mem_affineCone_singleton : P.rep ∈ affineCone {P} :=
  (mem_affineCone_singleton P).2 ⟨1, (one_smul K P.rep).symm⟩

/-- A form of degree `q` vanishes on the line through a point exactly when it vanishes at that
point. -/
theorem mem_coneVanishingIdeal_singleton_iff {q : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F.IsHomogeneous q) : F ∈ coneVanishingIdeal {P} ↔ eval P.rep F = 0 := by
  rw [coneVanishingIdeal, mem_affineVanishingIdeal]
  refine ⟨fun h => h _ (rep_mem_affineCone_singleton P), fun h v hv => ?_⟩
  obtain ⟨c, rfl⟩ := (mem_affineCone_singleton P).1 hv
  rw [eval_smul_of_isHomogeneous hF, h, mul_zero]

/-- A projective point lies in the projective set cut out by the homogeneous ideal of the cone over
it. -/
theorem mem_projZeroLocus_coneVanishingIdeal_singleton :
    P ∈ projZeroLocus (coneVanishingIdeal {P}) := fun F hF => by
  rw [coneVanishingIdeal, mem_affineVanishingIdeal] at hF
  exact hF _ (rep_mem_affineCone_singleton P)

/-- The degree-`q` part of the homogeneous ideal of the projective set cut out by a single point
consists of the forms vanishing at that point: such a form vanishes at every point of that set, and
hence, being homogeneous, on the whole cone over it. -/
theorem mem_coneVanishingIdeal_projZeroLocus_iff {q : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F.IsHomogeneous q) :
    F ∈ coneVanishingIdeal (projZeroLocus (coneVanishingIdeal {P})) ↔ eval P.rep F = 0 := by
  rw [coneVanishingIdeal, mem_affineVanishingIdeal]
  refine ⟨fun h => h _ ⟨P, mem_projZeroLocus_coneVanishingIdeal_singleton P, 1,
      (one_smul K P.rep).symm⟩, fun h v hv => ?_⟩
  obtain ⟨Q, hQ, c, rfl⟩ := hv
  rw [eval_smul_of_isHomogeneous hF,
    hQ F ((mem_coneVanishingIdeal_singleton_iff P hF).2 h), mul_zero]

/-- The Hilbert function of the projective set cut out by a single point is `1` in every degree:
evaluation at a representative maps the degree-`q` forms onto the base field, with kernel exactly
the degree-`q` part of the homogeneous ideal of that set. -/
theorem projHilbertFunction_projZeroLocus_singleton (q : ℕ) :
    projHilbertFunction (projZeroLocus (coneVanishingIdeal {P})) q = 1 := by
  set φ : ↥(homogeneousSubmodule (Fin (n + 1)) K q) →ₗ[K] K :=
    { toFun := fun F => eval P.rep (F : MvPolynomial (Fin (n + 1)) K)
      map_add' := fun F G => by simp
      map_smul' := fun c F => by simp [smul_eval] } with hφ
  have hker : Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K q).subtype
      ((coneVanishingIdeal (projZeroLocus (coneVanishingIdeal {P}))).restrictScalars K)
        = LinearMap.ker φ := by
    ext F
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem,
      LinearMap.mem_ker, hφ, LinearMap.coe_mk, AddHom.coe_mk]
    exact mem_coneVanishingIdeal_projZeroLocus_iff P ((mem_homogeneousSubmodule _ _).1 F.2)
  have hsurj : Function.Surjective φ := by
    obtain ⟨i, hi⟩ : ∃ i, P.rep i ≠ 0 := by
      by_contra hcon
      exact P.rep_nonzero (funext fun i => not_not.1 fun h => hcon ⟨i, h⟩)
    intro c
    refine ⟨⟨monomial (Finsupp.single i q) (c / P.rep i ^ q),
      (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (by simp))⟩, ?_⟩
    simp only [hφ, LinearMap.coe_mk, AddHom.coe_mk, eval_monomial]
    rw [Finsupp.prod_single_index (by simp)]
    field_simp
  rw [projHilbertFunction, hker, (φ.quotKerEquivOfSurjective hsurj).finrank_eq,
    Module.finrank_self]

/-- The projective set cut out by a single point has degree `1`: its Hilbert function is constantly
`1`, so its Hilbert polynomial is the constant `1`, of degree `0` and leading coefficient `1`. -/
theorem projDegree_projZeroLocus_singleton :
    projDegree (projZeroLocus (coneVanishingIdeal {P})) = 1 := by
  have hpoly : hilbertPolynomialOf
      (projHilbertFunction (projZeroLocus (coneVanishingIdeal {P}))) = 1 :=
    hilbertPolynomialOf_eq (Filter.Eventually.of_forall fun q => by
      rw [projHilbertFunction_projZeroLocus_singleton]; simp)
  rw [projDegree, hpoly]
  simp

end Point

/-- **The Hilbert function of a nonempty projective set is positive.** In every degree `q` the
monomial `x_i ^ q`, for a coordinate `i` at which a representative of a point of `T` is nonzero,
is a form of degree `q` that does not vanish on the cone over `T`, so its class in the degree-`q`
piece of
the homogeneous coordinate ring of `T` is nonzero. -/
@[browning_sawin "lem_hilbert_positive"]
theorem one_le_projHilbertFunction {T : Set (Projectivization K (Fin (n + 1) → K))}
    (hT : T.Nonempty) (q : ℕ) : 1 ≤ projHilbertFunction T q := by
  obtain ⟨P, hP⟩ := hT
  obtain ⟨i, hi⟩ : ∃ i, P.rep i ≠ 0 := by
    by_contra hcon
    exact P.rep_nonzero (funext fun i => not_not.1 fun h => hcon ⟨i, h⟩)
  have hFmem : (monomial (Finsupp.single i q) (1 : K)) ∈
      homogeneousSubmodule (Fin (n + 1)) K q :=
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (by simp))
  have heval : eval P.rep (monomial (Finsupp.single i q) (1 : K)) ≠ 0 := by
    rw [eval_monomial, Finsupp.prod_single_index (by simp), one_mul]
    exact pow_ne_zero q hi
  rw [projHilbertFunction]
  have hle : homogeneousSubmodule (Fin (n + 1)) K q ≤ restrictTotalDegree (Fin (n + 1)) K q :=
    fun F hF => (mem_restrictTotalDegree _ _ _).2
      ((mem_homogeneousSubmodule _ _).1 hF).totalDegree_le
  have : Module.Finite K ↥(homogeneousSubmodule (Fin (n + 1)) K q) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have : Module.Finite K (↥(homogeneousSubmodule (Fin (n + 1)) K q) ⧸
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K q).subtype
        ((coneVanishingIdeal T).restrictScalars K)) :=
    Module.Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have : Nontrivial (↥(homogeneousSubmodule (Fin (n + 1)) K q) ⧸
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K q).subtype
        ((coneVanishingIdeal T).restrictScalars K)) := by
    refine ⟨⟨Submodule.Quotient.mk ⟨_, hFmem⟩, 0, fun hzero => ?_⟩⟩
    have hmem := (Submodule.Quotient.mk_eq_zero _).1 hzero
    rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem,
      coneVanishingIdeal, mem_affineVanishingIdeal] at hmem
    exact heval (hmem P.rep ⟨P, hP, 1, (one_smul K P.rep).symm⟩)
  exact Module.finrank_pos

/-- A polynomial agreeing in all large degrees with a function bounded below by `1` has positive
leading coefficient: otherwise it is either a constant at most `0`, or of positive degree and
therefore tending to `-∞` along the integers. -/
theorem zero_lt_leadingCoeff_of_eventually_eq (P : Polynomial ℚ) (H : ℕ → ℕ)
    (hP : ∀ᶠ q : ℕ in Filter.atTop, P.eval (q : ℚ) = H q) (hH : ∀ q, 1 ≤ H q) :
    0 < P.leadingCoeff := by
  have hge : ∀ᶠ q : ℕ in Filter.atTop, (1 : ℚ) ≤ P.eval (q : ℚ) := by
    filter_upwards [hP] with q hq
    rw [hq]
    exact_mod_cast hH q
  by_contra hcon
  rw [not_lt] at hcon
  rcases lt_or_ge 0 P.degree with hdeg | hdeg
  · have htend : Filter.Tendsto (fun q : ℕ => P.eval (q : ℚ)) Filter.atTop Filter.atBot :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hcon).comp tendsto_natCast_atTop_atTop
    obtain ⟨q, h1, h2⟩ := (hge.and (htend.eventually_lt_atBot 1)).exists
    exact absurd h1 (not_le.2 h2)
  · have hP0 : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
    obtain ⟨q, hq⟩ := hge.exists
    rw [hP0, Polynomial.eval_C] at hq
    rw [hP0, Polynomial.leadingCoeff_C] at hcon
    linarith

/-- **A nonempty projective algebraic set has degree at least `1`.** Hilbert–Serre supplies a
polynomial agreeing with the Hilbert function in all large degrees, and the Hilbert function of a
nonempty set is at least `1` everywhere, so that polynomial has positive leading coefficient; the
degree is the numerator of `r !` times it, hence a positive integer. -/
@[browning_sawin "lem_one_le_proj_degree"]
theorem one_le_projDegree (hhs : HilbertSerre.{u})
    {T : Set (Projectivization K (Fin (n + 1) → K))} (hT : T.Nonempty) :
    1 ≤ projDegree T := by
  obtain ⟨P, hP⟩ := hhs T
  have hpoly : hilbertPolynomialOf (projHilbertFunction T) = P := hilbertPolynomialOf_eq hP
  have hlead : 0 < P.leadingCoeff :=
    zero_lt_leadingCoeff_of_eventually_eq P _ hP fun q => one_le_projHilbertFunction hT q
  have hpos : 0 < (Nat.factorial P.natDegree : ℚ) * P.leadingCoeff :=
    mul_pos (by positivity) hlead
  rw [projDegree, hpoly]
  have hnum := Rat.num_pos.2 hpos
  omega

/-- The projective closure of a single affine point has degree `1`. -/
theorem projDegree_projectiveClosure_singleton (a : Fin n → K) :
    projDegree (projectiveClosure ({a} : Set (Fin n → K))) = 1 := by
  rw [projectiveClosure, Set.image_singleton]
  exact projDegree_projZeroLocus_singleton _

/-! ### The components of a finite algebraic set -/

/-- The polynomials vanishing at a point form a maximal ideal: evaluation there is a surjection
onto the base field. -/
theorem isMaximal_ker_eval (a : Fin n → K) : (RingHom.ker (eval a)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (eval a) fun c => ⟨C c, eval_C c⟩

/-- The vanishing ideal of a finite set of points is the intersection of the maximal ideals of its
points. -/
theorem affineVanishingIdeal_coe_finset (s : Finset (Fin n → K)) :
    affineVanishingIdeal (↑s : Set (Fin n → K)) = s.inf fun a => RingHom.ker (eval a) := by
  rw [Finset.inf_eq_iInf]
  rfl

/-- **The minimal primes of a finite set of points.** They are the maximal ideals of its points: a
prime containing a finite intersection of ideals contains one of them, and the ideals in question
are maximal, so no smaller prime lies between. -/
theorem minimalPrimes_affineVanishingIdeal_coe_finset (s : Finset (Fin n → K)) :
    (affineVanishingIdeal (↑s : Set (Fin n → K))).minimalPrimes
      = (fun a => RingHom.ker (eval a)) '' ↑s := by
  have hinf := affineVanishingIdeal_coe_finset s
  have hle : ∀ a ∈ s, affineVanishingIdeal (↑s : Set (Fin n → K)) ≤ RingHom.ker (eval a) :=
    fun a ha => by rw [hinf]; exact Finset.inf_le ha
  have hkey : ∀ {q : Ideal (MvPolynomial (Fin n) K)}, q.IsPrime →
      affineVanishingIdeal (↑s : Set (Fin n → K)) ≤ q → ∃ b ∈ s, RingHom.ker (eval b) = q := by
    intro q hq hqle
    obtain ⟨b, hb, hble⟩ := hq.inf_le'.1 (hinf ▸ hqle)
    exact ⟨b, hb, (isMaximal_ker_eval b).eq_of_le hq.ne_top hble⟩
  ext P
  refine ⟨fun hP => hkey hP.1.1 hP.1.2, ?_⟩
  rintro ⟨a, ha, rfl⟩
  refine ⟨⟨(isMaximal_ker_eval a).isPrime, hle a ha⟩, fun q hq hqle => ?_⟩
  obtain ⟨b, hb, hbq⟩ := hkey hq.1 hq.2
  subst hbq
  exact le_of_eq ((isMaximal_ker_eval b).eq_of_le (isMaximal_ker_eval a).ne_top hqle).symm

/-- The zero locus of the ideal of a point is that point. -/
theorem affineZeroLocus_ker_eval (a : Fin n → K) :
    affineZeroLocus (RingHom.ker (eval a)) = {a} := by
  ext b
  simp only [affineZeroLocus, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hb => funext fun i => ?_, fun hb F hF => hb ▸ RingHom.mem_ker.1 hF⟩
  have h := hb (X i - C (a i)) (RingHom.mem_ker.2 (by simp))
  simpa [sub_eq_zero] using h

/-- The irreducible components of a finite affine algebraic set are its points. -/
theorem irreducibleComponentsOf_coe_finset (s : Finset (Fin n → K)) :
    irreducibleComponentsOf (↑s : Set (Fin n → K))
      = (fun a => ({a} : Set (Fin n → K))) '' ↑s := by
  rw [irreducibleComponentsOf, minimalPrimes_affineVanishingIdeal_coe_finset, ← Set.image_comp]
  exact Set.image_congr' fun a => affineZeroLocus_ker_eval a

/-- **`δ` counts the points of a finite algebraic set.** Its irreducible components are its points,
each of whose projective closures has degree `1`. -/
theorem delta_eq_ncard_of_finite {V : Set (Fin n → K)} (hV : V.Finite) : delta V = V.ncard := by
  have hcomp : irreducibleComponentsOf V = (fun a => ({a} : Set (Fin n → K))) '' V := by
    conv_lhs => rw [← hV.coe_toFinset]
    rw [irreducibleComponentsOf_coe_finset, hV.coe_toFinset]
  have hone : ∀ W ∈ irreducibleComponentsOf V, projDegree (projectiveClosure W) = 1 := by
    intro W hW
    rw [hcomp] at hW
    obtain ⟨a, -, rfl⟩ := hW
    exact projDegree_projectiveClosure_singleton a
  have hinj : Function.Injective fun a : Fin n → K => ({a} : Set (Fin n → K)) :=
    fun a b hab => by simpa using hab
  have hfin : (irreducibleComponentsOf V).Finite := by rw [hcomp]; exact hV.image _
  rw [delta]
  calc ∑ᶠ W ∈ irreducibleComponentsOf V, projDegree (projectiveClosure W)
      = ∑ᶠ _ ∈ irreducibleComponentsOf V, (1 : ℕ) := finsum_mem_congr rfl hone
    _ = (irreducibleComponentsOf V).ncard := finsum_mem_one_eq_ncard hfin
    _ = V.ncard := by rw [hcomp, Set.ncard_image_of_injective V hinj]

/-! ### The bound -/

/-- A partial derivative drops the total degree by at least one: a monomial of `∂ᵢ g` comes from a
monomial of `g` in which `y_i` occurs, whose exponent it lowers by one. -/
theorem totalDegree_pderiv_le (i : Fin n) (g : MvPolynomial (Fin n) K) :
    (pderiv i g).totalDegree ≤ g.totalDegree - 1 := by
  rw [pderiv_eq_sum_monomial]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun β hβ => ?_)
  rcases eq_or_ne (β i) 0 with hi | hi
  · simp [hi]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have hsub : (β - Finsupp.single i 1).degree + 1 = β.degree := by
      have hle : Finsupp.single i 1 ≤ β := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
      calc (β - Finsupp.single i 1).degree + 1
          = (β - Finsupp.single i 1).degree + (Finsupp.single i (1 : ℕ)).degree := by
            rw [Finsupp.degree_single]
        _ = ((β - Finsupp.single i 1) + Finsupp.single i 1).degree := by
            simp [Finsupp.degree_eq_sum, Finset.sum_add_distrib]
        _ = β.degree := by rw [tsub_add_cancel_of_le hle]
    have hle := le_totalDegree hβ
    rw [← degree_eq_finsuppSum] at hle
    change (β - Finsupp.single i 1).degree ≤ g.totalDegree - 1
    omega

/-- **Size of a finite critical locus.** The critical locus `W_n = Z(∂₁g, …, ∂_n g)` of a
polynomial of total degree at most `d ≥ 2`, taken over an algebraic closure of the base field, has
at most `D ^ n` points when it is finite, where `D = d - 1`: each `∂ᵢ g` has degree at most `D`, so
the affine Bézout inequality bounds `δ(W_n)` by `D ^ n`, and for a finite algebraic set `δ` is the
number of points. -/
@[browning_sawin "lem_critical_point_bound"]
theorem ncard_criticalLocus_le_pow (hbez : AffineBezout.{u}) {k : Type u} [Field k] {d : ℕ}
    (hd : 2 ≤ d)
    {g : MvPolynomial (Fin n) k} (hg : g.totalDegree ≤ d)
    (hfin : (criticalLocus g n).Finite) :
    (criticalLocus g n).ncard ≤ pderivDegBound d ^ n := by
  have hD : 1 ≤ pderivDegBound d := by simp only [pderivDegBound]; omega
  have hset : criticalLocus g n = {a : Fin n → AlgebraicClosure k |
      ∀ i : Fin n, eval a ((pderiv i g).map (algebraMap k (AlgebraicClosure k))) = 0} := by
    ext a
    simp only [criticalLocus, Set.mem_ofPred_eq]
    exact ⟨fun h i => h i i.is_lt, fun h i _ => h i⟩
  have hdeg : ∀ i : Fin n,
      ((pderiv i g).map (algebraMap k (AlgebraicClosure k))).totalDegree ≤ pderivDegBound d := by
    intro i
    refine le_trans (Finset.sup_le fun β hβ => le_totalDegree (support_map_subset _ _ hβ)) ?_
    have h := totalDegree_pderiv_le i g
    simp only [pderivDegBound]
    omega
  calc (criticalLocus g n).ncard = delta (criticalLocus g n) :=
        (delta_eq_ncard_of_finite hfin).symm
    _ ≤ pderivDegBound d ^ n := by
        rw [hset]
        simpa using hbez hD
          (fun i : Fin n => (pderiv i g).map (algebraMap k (AlgebraicClosure k))) hdeg

end FiniteAlgebraicSet

/-! ## Conditioning on a group of signs

The reveal argument conditions on all the signs outside one block and bounds, uniformly in that
conditioning, the probability of an event depending on the block alone. Two general facts do the
work: functions of disjoint groups of independent signs are independent
(`signMeasure_inter_eq_mul`), and a union bound inside each fibre of the conditioning glues to a
union bound for the whole event (`signMeasure_le_mul_of_cond`). -/

section Conditioning

open MeasureTheory ProbabilityTheory

/-- **Two disjoint groups of signs are independent.** If the event `B` depends only on the signs
indexed by `T` and the event `C` only on those outside `T`, then `B` and `C` are independent. -/
theorem signMeasure_inter_eq_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Prop)
    {B C : Set (ι → ℤˣ)}
    (hB : ∀ ε ε' : ι → ℤˣ, (∀ i, T i → ε i = ε' i) → (ε ∈ B → ε' ∈ B))
    (hC : ∀ ε ε' : ι → ℤˣ, (∀ i, ¬ T i → ε i = ε' i) → (ε ∈ C → ε' ∈ C)) :
    signMeasure ι (B ∩ C) = signMeasure ι B * signMeasure ι C := by
  classical
  set f : ∀ _ : Bool, (ι → ℤˣ) → Prop := fun b ε => if b then ε ∈ B else ε ∈ C with hf
  have hind : iIndepFun (m := fun _ : Bool => (⊤ : MeasurableSpace Prop)) f (signMeasure ι) := by
    refine iIndepFun_of_forall_eq_on_fiber (m := fun _ => ⊤) (fun i => decide (T i))
      fun k ε ε' h => ?_
    cases k with
    | true =>
        simp only [hf, ite_eq_left]
        exact propext ⟨hB ε ε' (fun i hi => h i (by simp [hi])),
          hB ε' ε (fun i hi => (h i (by simp [hi])).symm)⟩
    | false =>
        simp only [hf]
        exact propext ⟨hC ε ε' (fun i hi => h i (by simp [hi])),
          hC ε' ε (fun i hi => (h i (by simp [hi])).symm)⟩
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hind
  have hkey := hind (Finset.univ : Finset Bool) (sets := fun _ => {True}) (fun _ _ => trivial)
  have hI : (⋂ i : Bool, {x : ι → ℤˣ | if i = true then x ∈ B else x ∈ C}) = B ∩ C := by
    ext x
    simp [Set.mem_iInter, Bool.forall_bool, and_comm]
  rw [← hI]
  simpa [hf, Set.preimage, Fintype.prod_bool, Set.inter_comm] using hkey

/-- **A conditional union bound.** Suppose that, after fixing the signs outside a group `T`, the
event `A` is covered by at most `N` events, each depending on the signs in `T` alone and each of
probability at most `q`. Then `P(A) ≤ N q`: the fibres of the conditioning partition the space, on
each of them the union bound applies and the covering events are independent of the fibre, and the
resulting bounds recombine because the fibre probabilities sum to one. -/
theorem signMeasure_le_mul_of_cond {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Prop)
    {A : Set (ι → ℤˣ)} {N : ℕ} {q : ℝ≥0∞} {γ : Type*}
    (h : ∀ ω : ι → ℤˣ, ∃ (S : Finset γ) (B : γ → Set (ι → ℤˣ)), S.card ≤ N ∧
      (∀ c ∈ S, ∀ ε ε' : ι → ℤˣ, (∀ i, T i → ε i = ε' i) → ε ∈ B c → ε' ∈ B c) ∧
      (∀ c ∈ S, signMeasure ι (B c) ≤ q) ∧
      (∀ ε ∈ A, (∀ i, ¬ T i → ε i = ω i) → ∃ c ∈ S, ε ∈ B c)) :
    signMeasure ι A ≤ N * q := by
  classical
  set Fib : ({i : ι // ¬ T i} → ℤˣ) → Set (ι → ℤˣ) :=
    fun ω => {ε | ∀ i : {i : ι // ¬ T i}, ε i.1 = ω i} with hFib
  have hFibOut : ∀ ω, ∀ ε ε' : ι → ℤˣ, (∀ i, ¬ T i → ε i = ε' i) → ε ∈ Fib ω → ε' ∈ Fib ω :=
    fun ω ε ε' hee hε i => by rw [← hee i.1 i.2]; exact hε i
  have hdisj : Pairwise (Function.onFun Disjoint Fib) := by
    intro ω ω' hne
    refine Set.disjoint_left.2 fun ε hε hε' => hne (funext fun i => ?_)
    rw [← hε i, ← hε' i]
  have hunion : (⋃ ω, Fib ω) = Set.univ :=
    Set.eq_univ_of_forall fun ε => Set.mem_iUnion.2 ⟨fun i => ε i.1, fun _ => rfl⟩
  have hsum : ∀ f : (({i : ι // ¬ T i} → ℤˣ)) → Set (ι → ℤˣ),
      (∀ ω, f ω ⊆ Fib ω) → signMeasure ι (⋃ ω, f ω) = ∑ ω, signMeasure ι (f ω) := by
    intro f hf
    rw [measure_iUnion (fun ω ω' hne => (hdisj hne).mono (hf ω) (hf ω'))
      (fun _ => MeasurableSet.of_discrete), tsum_fintype]
  have htotal : ∑ ω, signMeasure ι (Fib ω) = 1 := by
    rw [← hsum Fib fun _ => le_rfl, hunion, measure_univ]
  have hA : signMeasure ι A = ∑ ω, signMeasure ι (A ∩ Fib ω) := by
    have h1 : A = ⋃ ω, (A ∩ Fib ω) := by rw [← Set.inter_iUnion, hunion, Set.inter_univ]
    conv_lhs => rw [h1]
    rw [hsum _ fun _ => Set.inter_subset_right]
  have hstep : ∀ ω, signMeasure ι (A ∩ Fib ω) ≤ (N : ℝ≥0∞) * q * signMeasure ι (Fib ω) := by
    intro ω
    obtain ⟨S, B, hcard, hin, hq, hcov⟩ := h fun i => if hi : ¬ T i then ω ⟨i, hi⟩ else 1
    have hsub : A ∩ Fib ω ⊆ ⋃ c ∈ S, (B c ∩ Fib ω) := by
      rintro ε ⟨hεA, hεF⟩
      obtain ⟨c, hcS, hcB⟩ := hcov ε hεA fun i hi => by
        rw [dite_eq_left hi]; exact hεF ⟨i, hi⟩
      exact Set.mem_biUnion hcS ⟨hcB, hεF⟩
    calc signMeasure ι (A ∩ Fib ω) ≤ ∑ c ∈ S, signMeasure ι (B c ∩ Fib ω) :=
          le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _c ∈ S, q * signMeasure ι (Fib ω) := by
          refine Finset.sum_le_sum fun c hc => ?_
          rw [signMeasure_inter_eq_mul T (hin c hc) (hFibOut ω)]
          gcongr
          exact hq c hc
      _ = (S.card : ℝ≥0∞) * (q * signMeasure ι (Fib ω)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ≥0∞) * q * signMeasure ι (Fib ω) := by
          rw [mul_assoc]
          gcongr
  calc signMeasure ι A = ∑ ω, signMeasure ι (A ∩ Fib ω) := hA
    _ ≤ ∑ ω, (N : ℝ≥0∞) * q * signMeasure ι (Fib ω) := Finset.sum_le_sum fun ω _ => hstep ω
    _ = (N : ℝ≥0∞) * q := by rw [← Finset.mul_sum, htotal, mul_one]

end Conditioning

/-! ## Dimension and the irreducible components of an affine algebraic set

The reveal argument controls `dim W_i` through the irreducible components of `W_i`, that is through
the minimal primes over its vanishing ideal. Two facts are needed: the dimension of an algebraic
set is bounded by the dimensions of its components (`affineDim_le_of_forall_minimalPrimes`, from
the observation that a chain of primes over an ideal lies entirely over one minimal prime of it),
and the number of components is bounded by `δ` (`ncard_minimalPrimes_le_delta`, from
`one_le_projDegree`). -/

section Components

variable {K : Type u} [Field K] {n : ℕ}

/-- An element of `WithBot ℕ∞` less than `m + 1` is at most `m`. -/
theorem withBot_le_of_lt_add_one {x : WithBot ℕ∞} {m : ℕ} (h : x < ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  cases x with
  | bot => exact bot_le
  | coe r =>
      have h1 : r < ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
      have h2 : r ≠ ⊤ := ne_top_of_lt h1
      have h3 : r.toNat < m + 1 := by
        rw [← Nat.cast_lt (α := ℕ∞), ENat.natCast_toNat h2]
        exact_mod_cast h1
      have h4 : r ≤ (m : ℕ∞) := by
        rw [← ENat.natCast_toNat h2]
        exact_mod_cast Nat.lt_succ_iff.1 h3
      exact_mod_cast h4

/-- Passing to a larger ideal cannot raise the Krull dimension of the quotient. -/
theorem ringKrullDim_quotient_le_quotient_of_le {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I ≤ J) : ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  refine Order.krullDim_le_of_strictMono
    (fun q : PrimeSpectrum.zeroLocus (R := R) J =>
      (⟨q.1, (PrimeSpectrum.mem_zeroLocus _ _).2
        (le_trans h ((PrimeSpectrum.mem_zeroLocus _ _).1 q.2))⟩ :
        PrimeSpectrum.zeroLocus (R := R) I))
    fun _ _ hab => hab

/-- **The dimension of a quotient is attained on a minimal prime.** A chain of primes over `J` has
its smallest member over some minimal prime of `J`, hence lies entirely over that minimal prime; so
a bound valid for every minimal prime bounds the dimension of `R ⧸ J`. -/
theorem ringKrullDim_quotient_le_of_forall_minimalPrimes {R : Type*} [CommRing R]
    {J : Ideal R} {m : ℕ}
    (h : ∀ P ∈ J.minimalPrimes, ringKrullDim (R ⧸ P) ≤ ((m : ℕ∞) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ J) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient]
  refine withBot_le_of_lt_add_one ?_
  rw [Order.krullDim_lt_coe_iff]
  intro l
  have hJle : J ≤ ((l 0 : PrimeSpectrum R)).asIdeal :=
    (PrimeSpectrum.mem_zeroLocus _ _).1 (l 0).2
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hJle
  have hall : ∀ i, ((l i : PrimeSpectrum R)) ∈ PrimeSpectrum.zeroLocus (R := R) P := fun i =>
    (PrimeSpectrum.mem_zeroLocus _ _).2 (le_trans hPle (l.monotone (Fin.zero_le i)))
  have h1 := Order.LTSeries.length_le_krullDim
    (α := PrimeSpectrum.zeroLocus (R := R) P)
    { length := l.length
      toFun := fun i => ⟨(l i : PrimeSpectrum R), hall i⟩
      step := fun i => l.step i }
  have h2 := h P hP
  rw [ringKrullDim_quotient] at h2
  have h3 : (l.length : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞) := le_trans (by exact_mod_cast h1) h2
  have h4 : (l.length : ℕ) ≤ m := by exact_mod_cast h3
  omega

/-- `dim V ≤ m` is the Krull dimension bound on the coordinate ring; the truncation in the
definition of `affineDim` is harmless because that dimension is at most `n`. -/
theorem affineDim_le_iff {V : Set (Fin n → K)} {m : ℕ} :
    affineDim V ≤ (m : ℤ) ↔
      ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  have hpoly : ringKrullDim (MvPolynomial (Fin n) K) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hle : ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) ≤
      ((n : ℕ∞) : WithBot ℕ∞) := hpoly ▸ ringKrullDim_quotient_le _
  rw [affineDim]
  cases hcase : ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) with
  | bot => simp
  | coe r =>
      rw [hcase] at hle
      have hrn : r ≤ (n : ℕ∞) := by exact_mod_cast hle
      have hrtop : r ≠ ⊤ := fun h => by simp [h] at hrn
      have hr : r = (r.toNat : ℕ∞) := (ENat.natCast_toNat hrtop).symm
      simp only [WithBot.recBotCoe_coe, Nat.cast_le]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hr]; exact_mod_cast h
      · rw [hr] at h; exact_mod_cast h

/-- The zero locus of the ideal generated by a set of polynomials is their common zero set. -/
theorem affineZeroLocus_span (S : Set (MvPolynomial (Fin n) K)) :
    affineZeroLocus (Ideal.span S) = {a : Fin n → K | ∀ F ∈ S, eval a F = 0} := by
  ext a
  simp only [affineZeroLocus, Set.mem_ofPred_eq]
  refine ⟨fun h F hF => h F (Ideal.subset_span hF), fun h F hF => ?_⟩
  induction hF using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ ihx ihy => simp [ihx, ihy]
  | smul c x _ ih => simp [ih]

/-- Adjoining `h` to an ideal cuts its zero locus with the zero set of `h`:
`Z(J + (h)) = Z(J) ∩ Z(h)`. -/
theorem affineZeroLocus_sup_span_singleton (J : Ideal (MvPolynomial (Fin n) K))
    (h : MvPolynomial (Fin n) K) :
    affineZeroLocus (J ⊔ Ideal.span {h}) = affineZeroLocus J ∩ {a | eval a h = 0} := by
  ext a
  simp only [affineZeroLocus, Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine ⟨fun hall => ⟨fun F hF => hall F ((le_sup_left : J ≤ J ⊔ Ideal.span {h}) hF),
    hall h ((le_sup_right : Ideal.span {h} ≤ J ⊔ Ideal.span {h})
      (Ideal.mem_span_singleton_self h))⟩, ?_⟩
  rintro ⟨h1, h2⟩ F hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  rw [map_add, h1 y hy, map_mul, h2, mul_zero, add_zero]

/-- An ideal and its radical have the same zero locus. -/
theorem affineZeroLocus_radical (I : Ideal (MvPolynomial (Fin n) K)) :
    affineZeroLocus I.radical = affineZeroLocus I := by
  ext a
  simp only [affineZeroLocus, Set.mem_ofPred_eq]
  refine ⟨fun h F hF => h F (Ideal.le_radical hF), fun h F hF => ?_⟩
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hF
  have hz := h _ hm
  rw [map_pow] at hz
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp at hz
  · exact (pow_eq_zero_iff hpos.ne').1 hz

/-- **Nullstellensatz.** Over an algebraically closed field the polynomials vanishing on the zero
locus of an ideal are its radical. -/
theorem affineVanishingIdeal_affineZeroLocus_eq_radical [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin n) K)) :
    affineVanishingIdeal (affineZeroLocus I) = I.radical := by
  rw [affineVanishingIdeal_eq_vanishingIdeal, affineZeroLocus_eq_zeroLocus,
    MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]

/-- An affine algebraic set is the zero locus of its own vanishing ideal. -/
theorem affineZeroLocus_affineVanishingIdeal_affineZeroLocus [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin n) K)) :
    affineZeroLocus (affineVanishingIdeal (affineZeroLocus I)) = affineZeroLocus I := by
  rw [affineVanishingIdeal_affineZeroLocus_eq_radical, affineZeroLocus_radical]

/-- The irreducible components of the zero locus of an ideal are cut out by its minimal primes. -/
theorem minimalPrimes_affineVanishingIdeal_affineZeroLocus [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin n) K)) :
    (affineVanishingIdeal (affineZeroLocus I)).minimalPrimes = I.minimalPrimes := by
  rw [affineVanishingIdeal_affineZeroLocus_eq_radical, Ideal.radical_minimalPrimes]

/-- Over an algebraically closed field the zero locus of a prime ideal is nonempty. -/
theorem affineZeroLocus_nonempty [IsAlgClosed K] {P : Ideal (MvPolynomial (Fin n) K)}
    (hP : P.IsPrime) : (affineZeroLocus P).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  have hv := affineVanishingIdeal_affineZeroLocus hP
  rw [he, affineVanishingIdeal_eq_top_iff.2 rfl] at hv
  exact hP.ne_top hv.symm

/-- For a prime `P`, `dim Z(P) ≤ m` is the Krull dimension bound on `K[y₁, …, y_n] ⧸ P`. -/
theorem affineDim_affineZeroLocus_le_iff [IsAlgClosed K] {P : Ideal (MvPolynomial (Fin n) K)}
    (hP : P.IsPrime) {m : ℕ} :
    affineDim (affineZeroLocus P) ≤ (m : ℤ) ↔
      ringKrullDim (MvPolynomial (Fin n) K ⧸ P) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by
  rw [affineDim_le_iff, affineVanishingIdeal_affineZeroLocus hP]

/-- **The dimension of an algebraic set is bounded by that of its components.** -/
theorem affineDim_le_of_forall_minimalPrimes [IsAlgClosed K] {V : Set (Fin n → K)} {m : ℕ}
    (h : ∀ P ∈ (affineVanishingIdeal V).minimalPrimes, affineDim (affineZeroLocus P) ≤ (m : ℤ)) :
    affineDim V ≤ (m : ℤ) := by
  rw [affineDim_le_iff]
  exact ringKrullDim_quotient_le_of_forall_minimalPrimes fun P hP =>
    (affineDim_affineZeroLocus_le_iff hP.1.1).1 (h P hP)

/-- The zero locus of a larger prime has the smaller dimension. -/
theorem affineDim_affineZeroLocus_mono [IsAlgClosed K] {P Q : Ideal (MvPolynomial (Fin n) K)}
    (hP : P.IsPrime) (hQ : Q.IsPrime) (hPQ : P ≤ Q) :
    affineDim (affineZeroLocus Q) ≤ affineDim (affineZeroLocus P) := by
  have hnn : 0 ≤ affineDim (affineZeroLocus P) := zero_le_affineDim (affineZeroLocus_nonempty hP)
  have heq : affineDim (affineZeroLocus P) = ((affineDim (affineZeroLocus P)).toNat : ℤ) := by omega
  rw [heq, affineDim_affineZeroLocus_le_iff hQ]
  exact le_trans (ringKrullDim_quotient_le_quotient_of_le hPQ)
    ((affineDim_affineZeroLocus_le_iff hP).1 heq.le)

/-- The projective closure of a nonempty affine algebraic set is nonempty. -/
theorem projectiveClosure_nonempty {V : Set (Fin n → K)} (hV : V.Nonempty) :
    (projectiveClosure V).Nonempty := by
  obtain ⟨a, ha⟩ := hV
  refine ⟨standardChart a, fun F hF => ?_⟩
  rw [coneVanishingIdeal, mem_affineVanishingIdeal] at hF
  exact hF _ ⟨standardChart a, ⟨a, ha, rfl⟩, 1, (one_smul K _).symm⟩

/-- **`δ` bounds the number of irreducible components.** Each component is nonempty, so its
projective closure has degree at least `1` by `one_le_projDegree`, and distinct minimal primes cut
out distinct components. -/
theorem ncard_minimalPrimes_le_delta (hhs : HilbertSerre.{u}) [IsAlgClosed K]
    (V : Set (Fin n → K)) :
    (affineVanishingIdeal V).minimalPrimes.ncard ≤ delta V := by
  set S := (affineVanishingIdeal V).minimalPrimes with hS
  have hfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  have hinj : Set.InjOn affineZeroLocus S := by
    intro P hP Q hQ hPQ
    rw [← affineVanishingIdeal_affineZeroLocus hP.1.1,
      ← affineVanishingIdeal_affineZeroLocus hQ.1.1, hPQ]
  have hcomp : irreducibleComponentsOf V = affineZeroLocus '' S := rfl
  have hcfin : (irreducibleComponentsOf V).Finite := hcomp ▸ hfin.image _
  have hone : ∀ W ∈ irreducibleComponentsOf V, 1 ≤ projDegree (projectiveClosure W) := by
    intro W hW
    rw [hcomp] at hW
    obtain ⟨P, hP, rfl⟩ := hW
    exact one_le_projDegree hhs (projectiveClosure_nonempty (affineZeroLocus_nonempty hP.1.1))
  have hdelta : delta V = ∑ W ∈ hcfin.toFinset, projDegree (projectiveClosure W) := by
    have h1 : ∑ᶠ W ∈ irreducibleComponentsOf V, projDegree (projectiveClosure W)
        = ∑ᶠ W ∈ (↑hcfin.toFinset : Set (Set (Fin n → K))), projDegree (projectiveClosure W) := by
      rw [hcfin.coe_toFinset]
    rw [delta, h1, finsum_mem_coe_finset]
  calc S.ncard = (affineZeroLocus '' S).ncard := (Set.InjOn.ncard_image hinj).symm
    _ = (irreducibleComponentsOf V).ncard := by rw [hcomp]
    _ = ∑ _W ∈ hcfin.toFinset, 1 := by
        rw [Set.ncard_eq_toFinset_card _ hcfin, Finset.card_eq_sum_ones]
    _ ≤ ∑ W ∈ hcfin.toFinset, projDegree (projectiveClosure W) :=
        Finset.sum_le_sum fun W hW => hone W (hcfin.mem_toFinset.1 hW)
    _ = delta V := hdelta.symm

/-- **One step of the reveal.** Let every irreducible component of the algebraic set `Z(J)` have
dimension at most `m + 1`, and let `h` vanish identically on none of its positive-dimensional
components. Then every irreducible component of `Z(J) ∩ Z(h)` has dimension at most `m`: such a
component is a component of `Z(P) ∩ Z(h)` for some component `Z(P)` of `Z(J)`, and it is cut down
by one dimension when `dim Z(P) > 0` (`DimensionDrop`) while already having dimension at most `0`
otherwise. -/
theorem affineDim_le_of_mem_minimalPrimes_sup (hdrop : DimensionDrop.{u}) [IsAlgClosed K]
    {J : Ideal (MvPolynomial (Fin n) K)} {h : MvPolynomial (Fin n) K} {m : ℕ}
    (hJ : ∀ P ∈ J.minimalPrimes, affineDim (affineZeroLocus P) ≤ (m : ℤ) + 1)
    (hgood : ∀ P ∈ J.minimalPrimes, 0 < affineDim (affineZeroLocus P) → h ∉ P)
    {Q : Ideal (MvPolynomial (Fin n) K)} (hQ : Q ∈ (J ⊔ Ideal.span {h}).minimalPrimes) :
    affineDim (affineZeroLocus Q) ≤ (m : ℤ) := by
  have hQp : Q.IsPrime := hQ.1.1
  have hJQ : J ≤ Q := le_trans le_sup_left hQ.1.2
  have hhQ : h ∈ Q := hQ.1.2 ((le_sup_right : Ideal.span {h} ≤ J ⊔ Ideal.span {h})
    (Ideal.mem_span_singleton_self h))
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hPp : P.IsPrime := hP.1.1
  have hQmin : Q ∈ (P ⊔ Ideal.span {h}).minimalPrimes := by
    refine ⟨⟨hQp, sup_le hPQ (Ideal.span_le.2 (Set.singleton_subset_iff.2 hhQ))⟩, ?_⟩
    intro q hq hqle
    exact hQ.2 ⟨hq.1, sup_le (le_trans hP.1.2 (le_trans le_sup_left hq.2))
      (le_trans le_sup_right hq.2)⟩ hqle
  rcases le_or_gt (affineDim (affineZeroLocus P)) 0 with hdim | hdim
  · have h1 := affineDim_affineZeroLocus_mono hPp hQp hPQ
    have h2 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    omega
  · have hnv : ∃ a ∈ affineZeroLocus P, eval a h ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hgood P hP hdim ((affineVanishingIdeal_affineZeroLocus hPp) ▸
        mem_affineVanishingIdeal.2 hcon)
    have hcomp : affineZeroLocus Q ∈ irreducibleComponentsOf
        (affineZeroLocus P ∩ {a | eval a h = 0}) := by
      rw [irreducibleComponentsOf, ← affineZeroLocus_sup_span_singleton,
        minimalPrimes_affineVanishingIdeal_affineZeroLocus]
      exact ⟨Q, hQmin, rfl⟩
    have h1 := hdrop hPp hdim hnv hcomp
    have h2 := hJ P hP
    omega

end Components

/-! ## The critical locus

Revealing `G_1, …, G_n` in order, the inequality `dim W_i ≤ n - i` can first fail at step `i` only
if some irreducible component of `W_{i-1}` of dimension `n - i + 1 ≥ 1` lies inside
`Z(∂_i U + G_i^p)`; there are at most `δ(W_{i-1}) ≤ D^{i-1}` components to consider, each of them a
function of `U, G_1, …, G_{i-1}` alone, and for each of them the prescribed restriction of `G_i`
has probability at most `2^{-(s+1)}`. -/

section Critical

open MeasureTheory

section Reveal

variable {k : Type u} [Field k] {n : ℕ}

/-- `W_{i+1}` is `W_i` cut with the zero set of `∂_i g`. -/
theorem criticalLocus_succ (g : MvPolynomial (Fin n) k) {i : ℕ} (hi : i < n) :
    criticalLocus g (i + 1) = criticalLocus g i ∩
      {a | eval a ((pderiv (⟨i, hi⟩ : Fin n) g).map (algebraMap k (AlgebraicClosure k))) = 0} := by
  ext a
  simp only [criticalLocus, Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine ⟨fun h => ⟨fun j hj => h j (by omega), h ⟨i, hi⟩ (by simp)⟩, ?_⟩
  rintro ⟨h1, h2⟩ j hj
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hj) with hlt | heq
  · exact h1 j hlt
  · rw [show j = (⟨i, hi⟩ : Fin n) from Fin.ext heq]
    exact h2

/-- `W_i` is the zero locus of the ideal generated by the first `i` partial derivatives of `g`. -/
theorem criticalLocus_eq_affineZeroLocus_span (g : MvPolynomial (Fin n) k) (i : ℕ) :
    criticalLocus g i = affineZeroLocus (Ideal.span
      {F | ∃ j : Fin n, (j : ℕ) < i ∧
        F = (pderiv j g).map (algebraMap k (AlgebraicClosure k))}) := by
  rw [affineZeroLocus_span]
  ext a
  simp only [criticalLocus, Set.mem_ofPred_eq]
  refine ⟨fun hall F => ?_, fun hall j hj => hall _ ⟨j, hj, rfl⟩⟩
  rintro ⟨j, hj, rfl⟩
  exact hall j hj

/-- A critical locus is the zero locus of its own vanishing ideal. -/
theorem affineZeroLocus_affineVanishingIdeal_criticalLocus (g : MvPolynomial (Fin n) k) (i : ℕ) :
    affineZeroLocus (affineVanishingIdeal (criticalLocus g i)) = criticalLocus g i := by
  conv_lhs => rw [criticalLocus_eq_affineZeroLocus_span]
  rw [affineZeroLocus_affineVanishingIdeal_affineZeroLocus,
    ← criticalLocus_eq_affineZeroLocus_span]

/-- **The reveal succeeds when no step fails.** If at every step `i` the equation `∂_i g = 0` fails
to hold identically on each positive-dimensional irreducible component of `W_i`, then every
irreducible component of `W_i` has dimension at most `n - i`. -/
theorem forall_minimalPrimes_affineDim_le_of_forall_notMem (hdrop : DimensionDrop.{u})
    (g : MvPolynomial (Fin n) k)
    (hfail : ∀ (i : ℕ) (hi : i < n),
      ∀ P ∈ (affineVanishingIdeal (criticalLocus g i)).minimalPrimes,
        0 < affineDim (affineZeroLocus P) →
        (pderiv (⟨i, hi⟩ : Fin n) g).map (algebraMap k (AlgebraicClosure k)) ∉ P) :
    ∀ i ≤ n, ∀ P ∈ (affineVanishingIdeal (criticalLocus g i)).minimalPrimes,
      affineDim (affineZeroLocus P) ≤ ((n - i : ℕ) : ℤ) := by
  intro i
  induction i with
  | zero => exact fun _ P _ => le_trans (affineDim_le _) (by simp)
  | succ i ih =>
      intro hi P hP
      have hi' : i < n := by omega
      set h := (pderiv (⟨i, hi'⟩ : Fin n) g).map (algebraMap k (AlgebraicClosure k)) with hhdef
      set J := affineVanishingIdeal (criticalLocus g i) with hJdef
      have hWi1 : criticalLocus g (i + 1) = affineZeroLocus (J ⊔ Ideal.span {h}) := by
        rw [affineZeroLocus_sup_span_singleton, hJdef,
          affineZeroLocus_affineVanishingIdeal_criticalLocus, criticalLocus_succ g hi']
      have hPmin : P ∈ (J ⊔ Ideal.span {h}).minimalPrimes := by
        rw [← minimalPrimes_affineVanishingIdeal_affineZeroLocus, ← hWi1]
        exact hP
      refine affineDim_le_of_mem_minimalPrimes_sup hdrop (m := n - (i + 1)) (fun Q hQ => ?_)
        (fun Q hQ hdim => hfail i hi' Q hQ hdim) hPmin
      have h1 := ih (by omega) Q hQ
      have h2 : ((n - i : ℕ) : ℤ) = ((n - (i + 1) : ℕ) : ℤ) + 1 := by
        have : n - i = (n - (i + 1)) + 1 := by omega
        rw [this]
        push_cast
        ring
      omega

/-- The affine Bézout bound for a critical locus: `δ(W_i) ≤ D ^ i`. -/
theorem delta_criticalLocus_le (hbez : AffineBezout.{u}) {d : ℕ} (hd : 2 ≤ d)
    {g : MvPolynomial (Fin n) k}
    (hg : g.totalDegree ≤ d) {i : ℕ} (hi : i ≤ n) :
    delta (criticalLocus g i) ≤ pderivDegBound d ^ i := by
  have hD : 1 ≤ pderivDegBound d := by simp only [pderivDegBound]; omega
  have hset : criticalLocus g i = {a : Fin n → AlgebraicClosure k | ∀ j : Fin i,
      eval a ((pderiv (⟨(j : ℕ), by omega⟩ : Fin n) g).map
        (algebraMap k (AlgebraicClosure k))) = 0} := by
    ext a
    simp only [criticalLocus, Set.mem_ofPred_eq]
    exact ⟨fun hall j => hall _ j.is_lt, fun hall j hj => hall ⟨(j : ℕ), hj⟩⟩
  have hdeg : ∀ j : Fin i,
      ((pderiv (⟨(j : ℕ), by omega⟩ : Fin n) g).map
        (algebraMap k (AlgebraicClosure k))).totalDegree ≤ pderivDegBound d := by
    intro j
    refine le_trans (Finset.sup_le fun β hβ => le_totalDegree (support_map_subset _ _ hβ)) ?_
    have h := totalDegree_pderiv_le (⟨(j : ℕ), by omega⟩ : Fin n) g
    simp only [pderivDegBound]
    omega
  rw [hset]
  simpa using hbez hD
    (fun j : Fin i => (pderiv (⟨(j : ℕ), by omega⟩ : Fin n) g).map
      (algebraMap k (AlgebraicClosure k))) hdeg

end Reveal

variable {p n d : ℕ}

/-- The affine sign polynomial has total degree at most `d`. -/
theorem totalDegree_affineSignPoly_le [Fact p.Prime] (ε : SignFamily (monomialsLE n d)) :
    (affineSignPoly p n d ε).totalDegree ≤ d := by
  rw [affineSignPoly]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun β hβ => ?_)
  exact (totalDegree_monomial_le _ _).trans (mem_monomialsLE.1 hβ)

/-- Two sign families that agree outside the block `G_j` give every other block the same value. -/
theorem block_congr_of_ne (hp : 1 < p) {j : Fin n} {ε ω : SignFamily (monomialsLE n d)}
    (h : ∀ α : ↥(monomialsLE n d), blockOf p n α.1 ≠ BlockIndex.g j → ε α = ω α)
    {c : BlockIndex n} (hc : c ≠ BlockIndex.g j) : block p n d ε c = block p n d ω c :=
  block_congr hp c fun α hα => h α (by rw [hα]; exact hc)

/-- Two sign families that agree outside the block `G_j` give the same derivatives `∂_i g` for
`i ≠ j`, since `∂_i g = ∂_i U + G_i^p` involves no other block. -/
theorem pderiv_affineSignPoly_congr [Fact p.Prime] (hd : 1 ≤ d) {i j : Fin n} (hij : i ≠ j)
    {ε ω : SignFamily (monomialsLE n d)}
    (h : ∀ α : ↥(monomialsLE n d), blockOf p n α.1 ≠ BlockIndex.g j → ε α = ω α) :
    pderiv i (affineSignPoly p n d ε) = pderiv i (affineSignPoly p n d ω) := by
  have hp : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hU : blockU p n d ε = blockU p n d ω :=
    block_congr_of_ne hp h (c := BlockIndex.u) (by simp)
  have hG : blockG p n d ε i = blockG p n d ω i :=
    block_congr_of_ne hp h (c := BlockIndex.g i) fun hh => hij (by injection hh)
  rw [pderiv_affineSignPoly hd, pderiv_affineSignPoly hd, hU, hG]

/-- The critical locus `W_j` is a function of `U, G_1, …, G_j` alone. -/
theorem criticalLocus_congr [Fact p.Prime] (hd : 1 ≤ d) {j : Fin n}
    {ε ω : SignFamily (monomialsLE n d)}
    (h : ∀ α : ↥(monomialsLE n d), blockOf p n α.1 ≠ BlockIndex.g j → ε α = ω α) :
    criticalLocus (affineSignPoly p n d ε) (j : ℕ)
      = criticalLocus (affineSignPoly p n d ω) (j : ℕ) := by
  ext a
  simp only [criticalLocus, Set.mem_ofPred_eq]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [pderiv_affineSignPoly_congr hd (fun hh => absurd (hh ▸ hi) (lt_irrefl _)) h]

/-- The event that the reveal fails at step `i`: some positive-dimensional irreducible component of
`W_i` lies inside `Z(∂_i g)`. -/
def revealFailure (p n d : ℕ) [Fact p.Prime] (i : Fin n) : Set (SignFamily (monomialsLE n d)) :=
  {ε | ∃ P ∈ (affineVanishingIdeal (criticalLocus (affineSignPoly p n d ε) (i : ℕ))).minimalPrimes,
    0 < affineDim (affineZeroLocus P) ∧
    (pderiv i (affineSignPoly p n d ε)).map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∈ P}

set_option synthInstance.maxHeartbeats 1000000 in
-- The function field of a component is a localization of a quotient of a polynomial ring, and
-- synthesizing the scalar actions on it does not fit the default budgets.
set_option maxHeartbeats 1000000 in
/-- Vanishing identically on the component `Z(P)` is vanishing in the function field of `Z(P)`. -/
theorem map_mem_iff_restrictToFunctionField_eq_zero [Fact p.Prime]
    {P : Ideal (MvPolynomial (Fin n) (AlgebraicClosure (ZMod p)))} (hP : P.IsPrime)
    (F : MvPolynomial (Fin n) (ZMod p)) :
    F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∈ P ↔
      restrictToFunctionField (ZMod p) P F = 0 := by
  have := hP
  have : IsDomain (MvPolynomial (Fin n) (AlgebraicClosure (ZMod p)) ⧸ P) :=
    Ideal.Quotient.isDomain P
  rw [restrictToFunctionField]
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun hh => by rw [hh, map_zero], fun hh =>
    IsFractionRing.injective (MvPolynomial (Fin n) (AlgebraicClosure (ZMod p)) ⧸ P)
      (functionField P) (by rw [hh, map_zero])⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- As in `map_mem_iff_restrictToFunctionField_eq_zero`, the scalar actions on the function fields
-- of the components do not synthesize inside the default budgets.
set_option maxHeartbeats 1000000 in
/-- **The reveal fails at step `i` with probability at most `D^i 2^{-(s+1)}`.** Condition on every
sign outside the block `G_i`. That fixes `W_i` (`criticalLocus_congr`), hence its at most
`δ(W_i) ≤ D^i` irreducible components (`ncard_minimalPrimes_le_delta`,
`delta_criticalLocus_le`), and it fixes `∂_i U`. On each positive-dimensional component `Z(P)` the
failure says the restriction
of `G_i` to the function field of `Z(P)` has `p`-th power `-∂_i U`, an event of probability at most
`2^{-(s+1)}` by `signMeasure_pow_restrictToFunctionField_blockG_le`; a union bound over the
components inside each fibre of the conditioning finishes. -/
theorem signMeasure_revealFailure_le (hbez : AffineBezout.{0}) (hhs : HilbertSerre.{0})
    [Fact p.Prime] (hodd : Odd p) (hd : 3 ≤ d) (i : Fin n) :
    signMeasure ↥(monomialsLE n d) (revealFailure p n d i)
      ≤ ((pderivDegBound d : ℝ≥0∞) ^ (i : ℕ)) *
        ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹ := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hcast : ((pderivDegBound d ^ (i : ℕ) : ℕ) : ℝ≥0∞) = (pderivDegBound d : ℝ≥0∞) ^ (i : ℕ) := by
    push_cast
    ring
  rw [← hcast]
  refine signMeasure_le_mul_of_cond (fun α : ↥(monomialsLE n d) => blockOf p n α.1 = .g i)
    (γ := Ideal (MvPolynomial (Fin n) (AlgebraicClosure (ZMod p)))) fun ω => ?_
  set gω := affineSignPoly p n d ω with hgω
  set Jω := affineVanishingIdeal (criticalLocus gω (i : ℕ)) with hJω
  have hfin : Jω.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ _
  refine ⟨hfin.toFinset.filter fun P => 0 < affineDim (affineZeroLocus P),
    fun P => {ε | restrictToFunctionField (ZMod p) P (blockG p n d ε i) ^ p =
      - restrictToFunctionField (ZMod p) P (pderiv i (blockU p n d ω))}, ?_, ?_, ?_, ?_⟩
  · calc (hfin.toFinset.filter fun P => 0 < affineDim (affineZeroLocus P)).card
        ≤ hfin.toFinset.card := Finset.card_filter_le _ _
      _ = Jω.minimalPrimes.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
      _ ≤ delta (criticalLocus gω (i : ℕ)) := ncard_minimalPrimes_le_delta hhs _
      _ ≤ pderivDegBound d ^ (i : ℕ) :=
          delta_criticalLocus_le hbez (by omega) (totalDegree_affineSignPoly_le ω)
            (le_of_lt i.is_lt)
  · intro P _ ε ε' hee hε
    have hG : blockG p n d ε i = blockG p n d ε' i :=
      block_congr (Fact.out (p := p.Prime)).one_lt (.g i) fun α hα => hee α hα
    rw [Set.mem_ofPred_eq, ← hG]
    exact hε
  · intro P hP
    obtain ⟨hPmem, hPdim⟩ := Finset.mem_filter.1 hP
    exact signMeasure_pow_restrictToFunctionField_blockG_le hodd hd1
      (hfin.mem_toFinset.1 hPmem).1.1 hPdim i _
  · rintro ε ⟨P, hPmin, hPdim, hPmem⟩ hfib
    have hW : criticalLocus (affineSignPoly p n d ε) (i : ℕ) = criticalLocus gω (i : ℕ) :=
      criticalLocus_congr hd1 fun α hα => hfib α hα
    rw [hW] at hPmin
    have hPp : P.IsPrime := hPmin.1.1
    refine ⟨P, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hPmin, hPdim⟩, ?_⟩
    have hzero := (map_mem_iff_restrictToFunctionField_eq_zero hPp _).1 hPmem
    rw [pderiv_affineSignPoly hd1, map_add, map_pow] at hzero
    have hU : blockU p n d ε = blockU p n d ω :=
      block_congr_of_ne (Fact.out (p := p.Prime)).one_lt (fun α hα => hfib α hα)
        (c := BlockIndex.u) (by simp)
    rw [hU] at hzero
    rw [Set.mem_ofPred_eq, eq_neg_iff_add_eq_zero, add_comm]
    exact hzero

/-- The event `dim W_n > 0` is covered by the failures of the reveal. -/
theorem zero_lt_affineDim_criticalLocus_subset (hdrop : DimensionDrop.{0}) [Fact p.Prime] :
    {ε : SignFamily (monomialsLE n d) |
        0 < affineDim (criticalLocus (affineSignPoly p n d ε) n)}
      ⊆ ⋃ i : Fin n, revealFailure p n d i := by
  intro ε hε
  by_contra hcon
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hfail : ∀ (i : ℕ) (hi : i < n),
      ∀ P ∈ (affineVanishingIdeal (criticalLocus (affineSignPoly p n d ε) i)).minimalPrimes,
        0 < affineDim (affineZeroLocus P) →
        (pderiv (⟨i, hi⟩ : Fin n) (affineSignPoly p n d ε)).map
          (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∉ P := by
    intro i hi P hP hdim hmem
    exact hcon ⟨i, hi⟩ ⟨P, hP, hdim, hmem⟩
  have hall := forall_minimalPrimes_affineDim_le_of_forall_notMem hdrop _ hfail n le_rfl
  have hzero : affineDim (criticalLocus (affineSignPoly p n d ε) n) ≤ (0 : ℤ) := by
    have := affineDim_le_of_forall_minimalPrimes (m := 0) (V := criticalLocus
      (affineSignPoly p n d ε) n) fun P hP => by simpa using hall P hP
    simpa using this
  rw [Set.mem_ofPred_eq] at hε
  omega

/-- **The critical locus is positive-dimensional with small probability.** Revealing `G_1, …, G_n`
in order, the bound `dim W_i ≤ n - i` can first fail at step `i` only if one of the at most
`D^{i-1}` irreducible components of `W_{i-1}` — a function of `U, G_1, …, G_{i-1}` alone — is
contained in `Z(∂_i U + G_i^p)`, which prescribes the restriction of `G_i` to the function field of
that component and so has probability at most `2^{-(s+1)}`; and if no step fails then
`dim W_n ≤ 0`. -/
@[browning_sawin "prop_critical"]
theorem signMeasure_zero_lt_affineDim_criticalLocus_le (hbez : AffineBezout.{0})
    (hdrop : DimensionDrop.{0}) (hhs : HilbertSerre.{0}) [Fact p.Prime] (hodd : Odd p)
    (_hn : 1 ≤ n) (hd : 3 ≤ d) :
    signMeasure ↥(monomialsLE n d)
        {ε | 0 < affineDim (criticalLocus (affineSignPoly p n d ε) n)}
      ≤ (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹ := by
  calc signMeasure ↥(monomialsLE n d)
        {ε | 0 < affineDim (criticalLocus (affineSignPoly p n d ε) n)}
      ≤ signMeasure ↥(monomialsLE n d) (⋃ i : Fin n, revealFailure p n d i) :=
        measure_mono (zero_lt_affineDim_criticalLocus_subset hdrop)
    _ ≤ ∑ i : Fin n, signMeasure ↥(monomialsLE n d) (revealFailure p n d i) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin n, (pderivDegBound d : ℝ≥0∞) ^ (i : ℕ) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹ :=
        Finset.sum_le_sum fun i _ => signMeasure_revealFailure_le hbez hhs hodd hd i
    _ = (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i) *
          ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹ := by
        rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range]

end Critical

/-! ## Closed points of large degree

One more reveal, of the block `H`, turns the bound on `P(dim W_n > 0)` into a bound on the
probability of a singular closed point of large degree. Outside the event `dim W_n > 0` the
critical locus `W_n` is finite (`finite_of_affineDim_nonpos`) with at most `D^n` points
(`ncard_criticalLocus_le_pow`), and it is determined by the blocks `U, G₁, …, G_n`
(`criticalLocus_eq_of_blockU_eq_of_blockG_eq`), which `iIndepFun_block` makes independent of `H`. A
singular closed point of `g = 0` of degree `e > R` contributes a geometric point of `W_n` above it
at which `g` itself vanishes, and by `affineSignPoly_eq_blockU_add_sum_add_blockH_pow` that last
equation reads `H(P)^p = -U(P) - ∑ y_i(P) G_i(P)^p`, prescribing `H(P)` because the residue field
is a field of characteristic `p`. Among the monomials of degree at most `t` occurring in `H` there
are `min (t+1, e)` with `𝔽ₚ`-linearly independent values in `κ(P)`, so the rank bound charges each
point `2^{-min(t+1,e)} ≤ 2^{-min(t+1,R+1)}`, and a union bound over the at most `D^n` points
finishes. -/

section HighDegree

open MeasureTheory

/-! ### Affine algebraic sets of dimension zero -/

section DimensionZero

/-- **A prime over an ideal with zero-dimensional quotient is maximal among the primes over it.**
A strict inclusion between two such primes is a chain of length one in `Spec (R ⧸ I)`. -/
theorem eq_of_le_of_ringKrullDim_quotient_nonpos {R : Type*} [CommRing R] {I : Ideal R}
    (hdim : ringKrullDim (R ⧸ I) ≤ (0 : WithBot ℕ∞)) {Q Q' : Ideal R} (hQ : Q.IsPrime)
    (hQ' : Q'.IsPrime) (hIQ : I ≤ Q) (hQQ' : Q ≤ Q') : Q = Q' := by
  by_contra hne
  have hlt : (⟨Q, hQ⟩ : PrimeSpectrum R) < ⟨Q', hQ'⟩ :=
    lt_of_le_of_ne hQQ' (by simpa [PrimeSpectrum.ext_iff] using hne)
  have h1 := Order.LTSeries.length_le_krullDim
    (α := PrimeSpectrum.zeroLocus (R := R) I)
    { length := 1
      toFun := fun i => if i = 0 then ⟨⟨Q, hQ⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 hIQ⟩
        else ⟨⟨Q', hQ'⟩, (PrimeSpectrum.mem_zeroLocus _ _).2 (hIQ.trans hQQ')⟩
      step := by intro i; fin_cases i; simpa using hlt }
  rw [← ringKrullDim_quotient] at h1
  have h2 : ((1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    simpa using le_trans (by exact_mod_cast h1) hdim
  have h3 := (Nat.cast_le (α := WithBot ℕ∞)).1 h2
  omega

variable {K : Type*} [Field K] {n : ℕ}

/-- Distinct points have distinct maximal ideals, the zero locus of the ideal of the functions
vanishing at a point being that point. -/
theorem ker_eval_injective : Function.Injective fun a : Fin n → K => RingHom.ker (eval a) := by
  intro a b hab
  have h : affineZeroLocus (RingHom.ker (eval (R := K) (σ := Fin n) a))
      = affineZeroLocus (RingHom.ker (eval (R := K) (σ := Fin n) b)) := by
    rw [show RingHom.ker (eval (R := K) (σ := Fin n) a)
      = RingHom.ker (eval (R := K) (σ := Fin n) b) from hab]
  rw [affineZeroLocus_ker_eval, affineZeroLocus_ker_eval] at h
  simpa using h

/-- At a point of an affine algebraic set of dimension at most `0`, the maximal ideal of the
functions vanishing there is a minimal prime of the vanishing ideal of the set: a prime strictly
between the two would be a chain of length one in the coordinate ring. -/
theorem ker_eval_mem_minimalPrimes_of_affineDim_nonpos {V : Set (Fin n → K)}
    (hdim : affineDim V ≤ 0) {a : Fin n → K} (ha : a ∈ V) :
    RingHom.ker (eval a) ∈ (affineVanishingIdeal V).minimalPrimes := by
  have hmax : (RingHom.ker (eval (R := K) (σ := Fin n) a)).IsMaximal := isMaximal_ker_eval a
  have hIle : affineVanishingIdeal V ≤ RingHom.ker (eval a) := fun F hF =>
    RingHom.mem_ker.2 (mem_affineVanishingIdeal.1 hF a ha)
  have hdim' : ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)
      ≤ ((0 : ℕ∞) : WithBot ℕ∞) := affineDim_le_iff.1 (by simpa using hdim)
  refine ⟨⟨hmax.isPrime, hIle⟩, fun Q hQ hQle => ?_⟩
  exact le_of_eq (eq_of_le_of_ringKrullDim_quotient_nonpos (by simpa using hdim') hQ.1
    hmax.isPrime hQ.2 hQle).symm

/-- **An affine algebraic set of dimension at most `0` is finite.** Its points inject into the
minimal primes of its vanishing ideal, of which a Noetherian ring has only finitely many. -/
theorem finite_of_affineDim_nonpos {V : Set (Fin n → K)} (hdim : affineDim V ≤ 0) : V.Finite := by
  refine Set.Finite.of_finite_image (f := fun a : Fin n → K => RingHom.ker (eval a)) ?_
    ker_eval_injective.injOn
  refine Set.Finite.subset
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (affineVanishingIdeal V)) ?_
  rintro I ⟨a, ha, rfl⟩
  exact ker_eval_mem_minimalPrimes_of_affineDim_nonpos hdim ha

end DimensionZero

/-! ### Independent monomials of bounded degree at a closed point -/

section IndependentMonomials

variable {k : Type*} [Field k] {n : ℕ}

/-- **Independent monomials of bounded degree at a closed point.** At a closed point `Q` of `𝔸ⁿ_k`
there are `min (s+1) (deg Q)` monomials `y^β` of total degree at most `s` whose images in the
residue field `κ(Q)` are `k`-linearly independent.

Those images span the degree filtration `V_s` of `κ(Q)` with respect to the coordinate functions,
whose dimension `min_le_finrank_degreeFiltration` bounds below by `min (s+1) (deg Q)`, and a
spanning family contains a linearly independent subfamily of that dimension's size. -/
theorem exists_finset_linearIndependent_evalAt_monomial
    (Q : MaximalSpectrum (MvPolynomial (Fin n) k)) (s : ℕ) :
    ∃ J : Finset (Fin n →₀ ℕ), (∀ β ∈ J, β.degree ≤ s) ∧
      min (s + 1) (pointDegree k Q) ≤ J.card ∧
      LinearIndependent k fun β : J => evalAt Q (monomial (β : Fin n →₀ ℕ) 1) := by
  classical
  have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
  let : Field (residueFieldAt Q) := Ideal.Quotient.field _
  have : Module.Finite k (residueFieldAt Q) := module_finite_residueFieldAt Q
  set y : Fin n → residueFieldAt Q := fun i => evalAt Q (X i) with hy
  set w : (Fin n →₀ ℕ) → residueFieldAt Q := fun β => evalAt Q (monomial β 1) with hw
  have hwprod : ∀ β : Fin n →₀ ℕ, w β = ∏ i, y i ^ β i := fun β => mk_monomial_eq_prod _ β
  set T : Set (Fin n →₀ ℕ) := {β | β.degree ≤ s} with hT
  have hTfin : T.Finite :=
    Set.Finite.subset (monomialsLE n s).finite_toSet fun β hβ => mem_monomialsLE.2 hβ
  have hspanT : degreeFiltration k y s = Submodule.span k (w '' T) := by
    rw [degreeFiltration]
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image, hT]
    refine ⟨fun ⟨e, he, hx⟩ => ⟨Finsupp.equivFunOnFinite.symm e, ?_, ?_⟩,
      fun ⟨β, hβ, hx⟩ => ⟨fun i => β i, ?_, ?_⟩⟩
    · simpa [Finsupp.degree_eq_sum, Finsupp.equivFunOnFinite] using he
    · rw [hwprod, hx]; rfl
    · simpa [Finsupp.degree_eq_sum] using hβ
    · rw [← hx, hwprod]
  obtain ⟨b, hbT, -, hbspan, hbli⟩ :=
    exists_linearIndepOn_extension (K := k) (v := w) (linearIndepOn_empty k w)
      (Set.empty_subset T)
  have hbfin : b.Finite := hTfin.subset hbT
  have : Fintype ↥b := hbfin.fintype
  have hspanb : Submodule.span k (w '' b) = degreeFiltration k y s := by
    refine le_antisymm ?_ ?_
    · rw [hspanT]
      exact Submodule.span_mono (Set.image_mono hbT)
    · rw [hspanT]
      exact Submodule.span_le.2 hbspan
  have hrange : Set.range (fun x : ↥b => w x) = w '' b := by rw [Set.image_eq_range]
  have hcard : Module.finrank k (degreeFiltration k y s) = b.ncard := by
    rw [← hspanb, ← hrange, finrank_span_eq_card hbli, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hmin : min (s + 1) (pointDegree k Q) ≤ Module.finrank k (degreeFiltration k y s) :=
    min_le_finrank_degreeFiltration k (adjoin_range_mk_X Q.asIdeal) s
  refine ⟨hbfin.toFinset, fun β hβ => hbT (hbfin.mem_toFinset.1 hβ), ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hbfin, ← hcard]
    exact hmin
  · exact (linearIndependent_equiv'
      (e := Equiv.subtypeEquivRight fun β => (hbfin.mem_toFinset (a := β)).symm)
      (f := fun β : hbfin.toFinset => evalAt Q (monomial (β : Fin n →₀ ℕ) 1))
      (g := fun x : ↥b => w x) rfl).1 hbli

end IndependentMonomials

/-! ### A prescribed value of the block `H` at a closed point -/

section BlockH

variable {p n d : ℕ} [Fact p.Prime]

/-- **A prescribed value of `H` at a closed point is unlikely.** Let `Q` be a closed point of
`𝔸ⁿ_{𝔽ₚ}` of degree `e` and let `p` be odd. Then for every `v ∈ κ(Q)` the value `H(Q)` of the block
`H` in the residue field has `p`-th power `v` with probability at most `2^{-min(t+1,e)}`, where
`t = ⌊d/p⌋` is the length of that block.

At most one element of `κ(Q)` has `p`-th power `v` (`subsingleton_setOf_pow_eq`), so the event is
contained in the event that `H(Q)` takes one prescribed value. That value is the sign sum
`∑_α ε_α W_α`, where `W_α` is the value of `y^β` at `Q` when `α = pβ` and `0` otherwise, and
`exists_finset_linearIndependent_evalAt_monomial` makes `min (t+1,e)` of those values `𝔽ₚ`-linearly
independent. -/
theorem signMeasure_pow_evalAt_blockH_le (hodd : Odd p)
    (Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p))) (v : residueFieldAt Q) :
    signMeasure ↥(monomialsLE n d) {ε | evalAt Q (blockH p n d ε) ^ p = v}
      ≤ ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (pointDegree (ZMod p) Q))⁻¹ := by
  classical
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
  let : Field (residueFieldAt Q) := Ideal.Quotient.field _
  set π : MvPolynomial (Fin n) (ZMod p) →+* residueFieldAt Q := Ideal.Quotient.mk Q.asIdeal with hπ
  have hπeval : ∀ f : MvPolynomial (Fin n) (ZMod p), evalAt Q f = π f := fun _ => rfl
  have hdiv : ∀ β : Fin n →₀ ℕ, Finsupp.mapRange (· / p) (Nat.zero_div p) (p • β) = β :=
    fun β => Finsupp.ext fun j => by
      simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
      exact Nat.mul_div_cancel_left _ (by omega)
  set W : (Fin n →₀ ℕ) → residueFieldAt Q := fun α =>
    if residueTuple p α = 0 then
      π (monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) α) 1)
    else 0 with hW
  have hWzero : ∀ α : Fin n →₀ ℕ, residueTuple p α ≠ 0 → W α = 0 := fun α hα => by
    simp only [hW]; rw [ite_eq_right hα]
  have hWnsmul : ∀ β : Fin n →₀ ℕ, W (p • β) = π (monomial β 1) := fun β => by
    simp only [hW]
    rw [ite_eq_left (residueTuple_nsmul β), hdiv]
  have hrep : ∀ ε : SignFamily (monomialsLE n d),
      π (blockH p n d ε) = ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) := by
    intro ε
    have hzsmul : ∀ (β : Fin n →₀ ℕ) (z : ℤˣ),
        (monomial β (((z : ℤ) : ZMod p)) : MvPolynomial (Fin n) (ZMod p))
          = (z : ℤ) • monomial β 1 := fun β z => by
      rw [zsmul_eq_mul, ← map_intCast (C : ZMod p →+* MvPolynomial (Fin n) (ZMod p)) (z : ℤ),
        C_mul_monomial, mul_one]
    have hlhs : π (blockH p n d ε)
        = ∑ β ∈ monomialsLE n (upperBlockLength p d),
            (signOf ε (p • β) : ℤ) • π (monomial β 1) := by
      rw [blockH, map_sum]
      exact Finset.sum_congr rfl fun β _ => by rw [hzsmul, map_zsmul]
    have hrhs : ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ)
        = ∑ α ∈ monomialsLE n d, (signOf ε α : ℤ) • W α := by
      rw [← Finset.sum_coe_sort (monomialsLE n d) fun α => (signOf ε α : ℤ) • W α]
      exact Finset.sum_congr rfl fun α _ => by rw [signOf_of_mem ε α.2]
    have hzero : ∑ α ∈ (monomialsLE n d).filter (fun α => ¬ residueTuple p α = 0),
        (signOf ε α : ℤ) • W α = 0 :=
      Finset.sum_eq_zero fun α hα => by
        rw [hWzero α (Finset.mem_filter.1 hα).2]; simp
    have hsplit : ∑ α ∈ monomialsLE n d, (signOf ε α : ℤ) • W α
        = ∑ α ∈ (monomialsLE n d).filter (fun α => residueTuple p α = 0),
            (signOf ε α : ℤ) • W α := by
      rw [← Finset.sum_filter_add_sum_filter_not (monomialsLE n d)
        (fun α => residueTuple p α = 0) (fun α => (signOf ε α : ℤ) • W α), hzero, add_zero]
    have himage : ∑ α ∈ (monomialsLE n d).filter (fun α => residueTuple p α = 0),
          (signOf ε α : ℤ) • W α
        = ∑ β ∈ monomialsLE n (upperBlockLength p d),
            (signOf ε (p • β) : ℤ) • π (monomial β 1) := by
      rw [filter_residueTuple_eq_zero, Finset.sum_image fun β _ γ _ h =>
        nsmul_left_injective (Fact.out (p := p.Prime)).ne_zero h]
      exact Finset.sum_congr rfl fun β _ => by rw [hWnsmul]
    rw [hlhs, hrhs, hsplit, himage]
  obtain ⟨J₀, hJ₀deg, hJ₀card, hJ₀li⟩ :=
    exists_finset_linearIndependent_evalAt_monomial Q (upperBlockLength p d)
  have hmem : ∀ β : Fin n →₀ ℕ, β.degree ≤ upperBlockLength p d → p • β ∈ monomialsLE n d := by
    intro β hβ
    have hpt : p * upperBlockLength p d ≤ d := by
      rw [upperBlockLength, mul_comm]
      exact Nat.div_mul_le_self _ _
    have := Nat.mul_le_mul_left p hβ
    rw [mem_monomialsLE, degree_nsmul]
    omega
  set φ : ↥J₀ → ↥(monomialsLE n d) := fun β => ⟨p • (β : Fin n →₀ ℕ), hmem _ (hJ₀deg _ β.2)⟩ with hφ
  have hφinj : Function.Injective φ := fun β γ h =>
    Subtype.ext (nsmul_left_injective (Fact.out (p := p.Prime)).ne_zero (Subtype.ext_iff.1 h))
  set J : Finset ↥(monomialsLE n d) := J₀.attach.image φ with hJ
  have hJcard : J₀.card ≤ J.card := by
    rw [hJ, Finset.card_image_of_injective _ hφinj, Finset.card_attach]
  have hbij : Function.Bijective fun β : ↥J₀ =>
      (⟨φ β, Finset.mem_image_of_mem φ (Finset.mem_attach _ β)⟩ : ↥J) := by
    refine ⟨fun β γ h => hφinj (Subtype.ext_iff.1 h), fun c => ?_⟩
    obtain ⟨β, -, hβ⟩ := Finset.mem_image.1 c.2
    exact ⟨β, Subtype.ext hβ⟩
  have hJli : LinearIndependent (ZMod p)
      fun c : ↥J => W ((c : ↥(monomialsLE n d)) : Fin n →₀ ℕ) := by
    refine (linearIndependent_equiv' (e := Equiv.ofBijective _ hbij)
      (f := fun c : ↥J => W ((c : ↥(monomialsLE n d)) : Fin n →₀ ℕ))
      (g := fun β : ↥J₀ => evalAt Q (monomial (β : Fin n →₀ ℕ) 1)) (funext fun β => ?_)).1 hJ₀li
    rw [hπeval]
    exact hWnsmul _
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hodd
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p 2]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have : CharP (residueFieldAt Q) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (residueFieldAt Q)).injective p
  have : ExpChar (residueFieldAt Q) p := ExpChar.prime Fact.out
  have hfinal : signMeasure ↥(monomialsLE n d) {ε | evalAt Q (blockH p n d ε) ^ p = v}
      ≤ ((2 : ℝ≥0∞) ^ J.card)⁻¹ := by
    by_cases hex : ∃ c : residueFieldAt Q, c ^ p = v
    · obtain ⟨c, hc⟩ := hex
      have hsub : {ε : SignFamily (monomialsLE n d) | evalAt Q (blockH p n d ε) ^ p = v}
          ⊆ {ε | ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) = c} := by
        intro ε hε
        rw [Set.mem_ofPred_eq, ← hrep ε, ← hπeval]
        exact subsingleton_setOf_pow_eq v hε hc
      exact le_trans (measure_mono hsub) (signMeasure_sign_sum_le_inv_two_pow (k := ZMod p)
        (V := residueFieldAt Q)
        (v := fun α : ↥(monomialsLE n d) => W (α : Fin n →₀ ℕ)) (J := J) h2 hJli c)
    · have hempty : {ε : SignFamily (monomialsLE n d) | evalAt Q (blockH p n d ε) ^ p = v} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun ε hε => hex ⟨_, hε⟩
      rw [hempty, measure_empty]
      exact zero_le
  refine le_trans hfinal (ENNReal.inv_le_inv.2 ?_)
  exact pow_le_pow_right₀ one_le_two (le_trans hJ₀card hJcard)

end BlockH

/-! ### The contribution of the closed points of large degree -/

section Bound

variable {p n d : ℕ} [Fact p.Prime]

/-- **The critical loci depend on the blocks `U, G₁, …, G_n` alone.** Two sign families giving
those `n + 1` blocks the same values have the same critical loci, because `∂ᵢ g = ∂ᵢ U + G_i^p`
involves no other block. -/
theorem criticalLocus_eq_of_blockU_eq_of_blockG_eq (hd : 1 ≤ d)
    {ε ω : SignFamily (monomialsLE n d)} (hU : blockU p n d ε = blockU p n d ω)
    (hG : ∀ i, blockG p n d ε i = blockG p n d ω i) (j : ℕ) :
    criticalLocus (affineSignPoly p n d ε) j = criticalLocus (affineSignPoly p n d ω) j := by
  have key : ∀ i : Fin n, pderiv i (affineSignPoly p n d ε) = pderiv i (affineSignPoly p n d ω) :=
    fun i => by rw [pderiv_affineSignPoly hd, pderiv_affineSignPoly hd, hU, hG i]
  ext a
  simp only [criticalLocus, Set.mem_ofPred_eq]
  exact forall_congr' fun i => forall_congr' fun _ => by rw [key i]

set_option maxHeartbeats 1000000 in
-- The conditioning lemma is applied with the points of `W_n` indexing the covering family, so the
-- elaborator carries the whole affine geometry of `W_n` through the union bound; that does not fit
-- the default budget.
/-- **Contribution of the closed points of large degree.** For every `R` the probability that the
affine hypersurface `g = 0` cut out by the affine sign polynomial is singular at a closed point of
`𝔸ⁿ_{𝔽ₚ}` of degree greater than `R` is at most
`(∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}`.

A closed point is a maximal ideal `Q` of `𝔽ₚ[y₁, …, y_n]`, and singularity at it is singularity of
the hypersurface at a geometric point above it.

Exclude the event `dim W_n > 0`, whose probability `signMeasure_zero_lt_affineDim_criticalLocus_le`
bounds by the first term. On its complement `W_n` is finite with at most `D^n` points
(`finite_of_affineDim_nonpos` and `ncard_criticalLocus_le_pow`), and a singular geometric point
lies in `W_n` and satisfies `g = 0` besides. Condition on the blocks `U, G₁, …, G_n`, which
determine `W_n` (`criticalLocus_eq_of_blockU_eq_of_blockG_eq`) and, by `iIndepFun_block`, leave the
signs of `H` independent and uniform: by `affineSignPoly_eq_blockU_add_sum_add_blockH_pow` the
remaining equation `g = 0` prescribes `H^p` at the point, and `signMeasure_pow_evalAt_blockH_le`
bounds the probability of that by `2^{-min(t+1,R+1)}` above a closed point of degree greater than
`R`. A union bound over the at most `D^n` points gives the second term. -/
@[browning_sawin "prop_high"]
theorem signMeasure_exists_singular_closedPoint_le (hbez : AffineBezout.{0})
    (hdrop : DimensionDrop.{0}) (hjac : AffineJacobianCriterion.{0}) (hhs : HilbertSerre.{0})
    (hodd : Odd p) (hn : 1 ≤ n) (hd : 3 ≤ d)
    (R : ℕ) :
    signMeasure ↥(monomialsLE n d)
        {ε | ∃ (Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p)))
              (a : Fin n → AlgebraicClosure (ZMod p)),
            R < pointDegree (ZMod p) Q ∧
            (∀ f ∈ Q.asIdeal,
              eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0) ∧
            a ∈ affineSingularLocus (affineSignPoly p n d ε)}
      ≤ (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
            * ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹
        + (pderivDegBound d : ℝ≥0∞) ^ n
            * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹ := by
  classical
  have hp : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hd1 : 1 ≤ d := by omega
  have haeval : ∀ (a : Fin n → AlgebraicClosure (ZMod p)) (f : MvPolynomial (Fin n) (ZMod p)),
      aeval a f = eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) :=
    fun a f => by rw [aeval_def, eval₂_eq_eval_map]
  set A : Set (SignFamily (monomialsLE n d)) :=
    {ε | ∃ (Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p)))
          (a : Fin n → AlgebraicClosure (ZMod p)),
        R < pointDegree (ZMod p) Q ∧
        (∀ f ∈ Q.asIdeal,
          eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0) ∧
        a ∈ affineSingularLocus (affineSignPoly p n d ε)} with hA
  set Adim : Set (SignFamily (monomialsLE n d)) :=
    {ε | 0 < affineDim (criticalLocus (affineSignPoly p n d ε) n)} with hAdim
  have hcast : ((pderivDegBound d ^ n : ℕ) : ℝ≥0∞) = (pderivDegBound d : ℝ≥0∞) ^ n := by
    push_cast; ring
  have hsecond : signMeasure ↥(monomialsLE n d) (A \ Adim)
      ≤ (pderivDegBound d : ℝ≥0∞) ^ n
          * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹ := by
    rw [← hcast]
    refine signMeasure_le_mul_of_cond
      (fun α : ↥(monomialsLE n d) => blockOf p n α.1 = BlockIndex.h)
      (γ := Fin n → AlgebraicClosure (ZMod p)) fun ω => ?_
    set c : (Fin n → AlgebraicClosure (ZMod p)) → AlgebraicClosure (ZMod p) := fun a =>
      -(aeval a (blockU p n d ω) + ∑ i : Fin n, a i * aeval a (blockG p n d ω i) ^ p) with hc
    set B : (Fin n → AlgebraicClosure (ZMod p)) → Set (SignFamily (monomialsLE n d)) := fun a =>
      {ε | aeval a (blockH p n d ε) ^ p = c a} with hB
    have hBmem : ∀ a, ∀ ε ε' : SignFamily (monomialsLE n d),
        (∀ α : ↥(monomialsLE n d), blockOf p n α.1 = BlockIndex.h → ε α = ε' α) →
        ε ∈ B a → ε' ∈ B a := by
      intro a ε ε' hee hε
      have hH : blockH p n d ε = blockH p n d ε' := block_congr hp .h fun α hα => hee α hα
      rw [hB, Set.mem_ofPred_eq, ← hH]
      exact hε
    by_cases hdimω : affineDim (criticalLocus (affineSignPoly p n d ω) n) ≤ 0
    · have hfin : (criticalLocus (affineSignPoly p n d ω) n).Finite :=
        finite_of_affineDim_nonpos hdimω
      have hncard : hfin.toFinset.card ≤ pderivDegBound d ^ n := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact ncard_criticalLocus_le_pow hbez (by omega) (totalDegree_affineSignPoly_le ω) hfin
      refine ⟨hfin.toFinset.filter fun a => ∃ Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p)),
        R < pointDegree (ZMod p) Q ∧ ∀ f ∈ Q.asIdeal,
          eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0,
        B, le_trans (Finset.card_filter_le _ _) hncard, fun a _ => hBmem a, fun a haS => ?_,
        fun ε hε hfib => ?_⟩
      · obtain ⟨Q, hQdeg, hQa⟩ := (Finset.mem_filter.1 haS).2
        have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
        let : Field (residueFieldAt Q) := Ideal.Quotient.field _
        set ψ : residueFieldAt Q →+* AlgebraicClosure (ZMod p) :=
          Ideal.Quotient.lift Q.asIdeal
            (eval₂Hom (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) a)
            (fun f hf => by
              have h := hQa f hf
              rw [← haeval a f] at h
              exact h) with hψ
        have hψmk : ∀ f, ψ (evalAt Q f) = aeval a f := fun _ => rfl
        have hψinj : Function.Injective ψ := ψ.injective
        have hmin : min (upperBlockLength p d + 1) (R + 1)
            ≤ min (upperBlockLength p d + 1) (pointDegree (ZMod p) Q) := by omega
        by_cases hex : ∃ u : residueFieldAt Q, ψ u = c a
        · obtain ⟨u, hu⟩ := hex
          have hsub : B a ⊆ {ε | evalAt Q (blockH p n d ε) ^ p = u} := by
            intro ε hε
            refine hψinj ?_
            rw [map_pow, hψmk, hu]
            exact hε
          refine le_trans (le_trans (measure_mono hsub)
            (signMeasure_pow_evalAt_blockH_le hodd Q u)) (ENNReal.inv_le_inv.2 ?_)
          exact pow_le_pow_right₀ one_le_two hmin
        · have hempty : B a = ∅ :=
            Set.eq_empty_iff_forall_notMem.2 fun ε hε =>
              hex ⟨evalAt Q (blockH p n d ε) ^ p, by rw [map_pow, hψmk]; exact hε⟩
          rw [hempty, measure_empty]
          exact zero_le
      · obtain ⟨⟨Q, a, hQdeg, hQa, hsing⟩, -⟩ := hε
        have hU : blockU p n d ε = blockU p n d ω :=
          block_congr hp .u fun α hα => hfib α (by rw [hα]; exact fun hh => by cases hh)
        have hG : ∀ i, blockG p n d ε i = blockG p n d ω i := fun i =>
          block_congr hp (.g i) fun α hα => hfib α (by rw [hα]; exact fun hh => by cases hh)
        have hWeq : criticalLocus (affineSignPoly p n d ε) n
            = criticalLocus (affineSignPoly p n d ω) n :=
          criticalLocus_eq_of_blockU_eq_of_blockG_eq hd1 hU hG n
        obtain ⟨hg0, hgi⟩ :=
          (mem_affineSingularLocus_iff hjac (affineSignPoly_ne_zero ε) a).1 hsing
        have haW : a ∈ criticalLocus (affineSignPoly p n d ω) n := by
          rw [← hWeq]
          exact fun i _ => hgi i
        refine ⟨a, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 haW, ⟨Q, hQdeg, hQa⟩⟩, ?_⟩
        have hgeval : aeval a (affineSignPoly p n d ε) = 0 := by
          rw [haeval a]
          exact hg0
        rw [affineSignPoly_eq_blockU_add_sum_add_blockH_pow hd1, map_add, map_add, map_sum,
          map_pow, hU] at hgeval
        rw [hB, Set.mem_ofPred_eq, hc, eq_neg_iff_add_eq_zero, add_comm, ← hgeval]
        refine congrArg₂ _ (congrArg₂ _ rfl (Finset.sum_congr rfl fun i _ => ?_)) rfl
        rw [map_mul, aeval_X, map_pow, hG i]
    · refine ⟨∅, B, by simp, fun a _ => hBmem a, by simp, fun ε hε hfib => ?_⟩
      have hU : blockU p n d ε = blockU p n d ω :=
        block_congr hp .u fun α hα => hfib α (by rw [hα]; exact fun hh => by cases hh)
      have hG : ∀ i, blockG p n d ε i = blockG p n d ω i := fun i =>
        block_congr hp (.g i) fun α hα => hfib α (by rw [hα]; exact fun hh => by cases hh)
      have hWeq : criticalLocus (affineSignPoly p n d ε) n
          = criticalLocus (affineSignPoly p n d ω) n :=
        criticalLocus_eq_of_blockU_eq_of_blockG_eq hd1 hU hG n
      have h1 : ε ∉ Adim := hε.2
      rw [hAdim, Set.mem_ofPred_eq, hWeq] at h1
      exact absurd (not_le.1 hdimω) h1
  have hAsub : A ⊆ Adim ∪ (A \ Adim) := fun ε hε => by
    by_cases h : ε ∈ Adim
    · exact Or.inl h
    · exact Or.inr ⟨hε, h⟩
  calc signMeasure ↥(monomialsLE n d) A
      ≤ signMeasure ↥(monomialsLE n d) (Adim ∪ (A \ Adim)) := measure_mono hAsub
    _ ≤ signMeasure ↥(monomialsLE n d) Adim + signMeasure ↥(monomialsLE n d) (A \ Adim) :=
        measure_union_le _ _
    _ ≤ (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
            * ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹
          + (pderivDegBound d : ℝ≥0∞) ^ n
            * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹ :=
        add_le_add (signMeasure_zero_lt_affineDim_criticalLocus_le hbez hdrop hhs hodd hn hd)
          hsecond

end Bound

end HighDegree

end BrowningSawin
