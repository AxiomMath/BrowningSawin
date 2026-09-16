/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import BrowningSawin.Attr

/-!
# Definitions for the Browning–Sawin conjecture

The objects the development is stated in terms of: the numerical parameters, the random sign forms
and the blocks their coefficients are partitioned into, the local algebras at a closed point, and
the classical projective geometry (hypersurfaces, singular loci, degrees) the estimates are about.

## Conventions

* Affine `n`-space over a field `K` is `Fin n → K`, and projective `n`-space is
  `Projectivization K (Fin (n + 1) → K)`; geometric statements are taken over `AlgebraicClosure k`.
* Exponent tuples are finitely supported functions `Fin m →₀ ℕ`, and `Finsupp.degree` is `|α|`.
* A family of independent uniform signs is modelled by the uniform probability measure on the
  finite space of sign families, `signMeasure`.
* Mathlib carries no Zariski topology on classical affine or projective space, so irreducibility,
  the projective closure and the degree of a projective variety are described here through the
  ideal-theoretic data that defines them: minimal primes, vanishing ideals and Hilbert functions.
-/

@[expose] public section

namespace BrowningSawin

open Filter MvPolynomial MeasureTheory
open scoped ENNReal

/-! ### Numerical parameters -/

/-- `N_{d,n} = \binom{n+d}{n}`, the number of monomials of degree `d` in `n + 1` variables. -/
@[browning_sawin "def_N_dn"]
abbrev monomialCount (n d : ℕ) : ℕ := (n + d).choose n

/-- `D = d - 1`, the degree bound for the first partial derivatives of a form of degree `d`. -/
@[browning_sawin "def_D_param"]
abbrev pderivDegBound (d : ℕ) : ℕ := d - 1

/-- `s = ⌊(d-1)/p⌋`, the length of the blocks `G_i`. -/
@[browning_sawin "def_s_param"]
abbrev lowerBlockLength (p d : ℕ) : ℕ := (d - 1) / p

/-- `t = ⌊d/p⌋`, the length of the block `H`. -/
@[browning_sawin "def_t_param"]
abbrev upperBlockLength (p d : ℕ) : ℕ := d / p

/-- `K_e = ⌊(d+1)/((n+1)e)⌋`, the number of disjoint monomial bases available at a closed point of
degree `e`. -/
@[browning_sawin "def_K_e"]
abbrev basisCount (n d e : ℕ) : ℕ := (d + 1) / ((n + 1) * e)

/-! ### The cosine average -/

/-- `Θ_K(p) = p⁻¹ ∑_{a ∈ 𝔽ₚ} |cos(2πa/p)|^K`. The summand depends only on the residue `a`, so the
choice of integer representative `a.val` is immaterial. -/
@[browning_sawin "def_theta"]
noncomputable def theta (p K : ℕ) [NeZero p] : ℝ :=
  (∑ a : ZMod p, |Real.cos (2 * Real.pi * a.val / p)| ^ K) / p

/-! ### Exponent tuples and sign families -/

/-- The exponent tuples `α` in `m` variables with `|α| = d`. -/
def monomialsEq (m d : ℕ) : Finset (Fin m →₀ ℕ) := Finset.finsuppAntidiag Finset.univ d

/-- The exponent tuples `β` in `m` variables with `|β| ≤ d`. -/
def monomialsLE (m d : ℕ) : Finset (Fin m →₀ ℕ) :=
  (Finset.range (d + 1)).biUnion (monomialsEq m)

/-- An exponent tuple belongs to `monomialsEq m d` exactly when its total degree is `d`. -/
theorem mem_monomialsEq {m d : ℕ} {α : Fin m →₀ ℕ} : α ∈ monomialsEq m d ↔ α.degree = d := by
  have h : Finset.univ.sum (α : Fin m → ℕ) = α.degree := by
    rw [Finsupp.degree]
    exact (Finset.sum_subset (Finset.subset_univ α.support) fun x _ hx => by simpa using hx).symm
  rw [monomialsEq, Finset.mem_finsuppAntidiag, ← h]
  simp

/-- An exponent tuple belongs to `monomialsLE m d` exactly when its total degree is at most `d`. -/
theorem mem_monomialsLE {m d : ℕ} {α : Fin m →₀ ℕ} : α ∈ monomialsLE m d ↔ α.degree ≤ d := by
  simp only [monomialsLE, Finset.mem_biUnion, Finset.mem_range, mem_monomialsEq]
  constructor
  · rintro ⟨j, hj, rfl⟩; omega
  · intro h; exact ⟨α.degree, by omega, rfl⟩

/-- A family of signs indexed by a finite set `s` of exponent tuples. -/
abbrev SignFamily {m : ℕ} (s : Finset (Fin m →₀ ℕ)) : Type := ↥s → ℤˣ

/-- The sign `ε_α` a sign family attaches to an exponent tuple, extended by `1` outside the
index set so that it can be evaluated at any tuple. -/
def signOf {m : ℕ} {s : Finset (Fin m →₀ ℕ)} (ε : SignFamily s) (α : Fin m →₀ ℕ) : ℤˣ :=
  if h : α ∈ s then ε ⟨α, h⟩ else 1

/-- At a tuple of the index set, `signOf ε` is the sign that `ε` attaches to it. -/
@[simp]
theorem signOf_of_mem {m : ℕ} {s : Finset (Fin m →₀ ℕ)} (ε : SignFamily s) {α : Fin m →₀ ℕ}
    (h : α ∈ s) : signOf ε α = ε ⟨α, h⟩ := dite_eq_left h

/-- The law of a family of independent uniform signs: the uniform probability measure on the
finite space `ι → ℤˣ` of sign families. Independence of the coordinates and uniformity of each are
both consequences of uniformity on the product. -/
noncomputable def signMeasure (ι : Type*) [Fintype ι] [DecidableEq ι] : Measure (ι → ℤˣ) :=
  (PMF.uniformOfFintype (ι → ℤˣ)).toMeasure

/-- The law of a family of independent uniform signs is a probability measure. -/
instance (ι : Type*) [Fintype ι] [DecidableEq ι] : IsProbabilityMeasure (signMeasure ι) := by
  unfold signMeasure; infer_instance

/-! ### The random sign form -/

/-- `𝓑_{d,n}`: the set of homogeneous `F ∈ ℤ[x₀,…,xₙ]` of the form `∑_{|α| = d} c_α x^α` with every
`c_α ∈ {-1, 1}`. -/
@[browning_sawin "def_sign_form_set"]
def signFormSet (n d : ℕ) : Set (MvPolynomial (Fin (n + 1)) ℤ) :=
  {F | (∀ α, α.degree ≠ d → F.coeff α = 0) ∧ ∀ α, α.degree = d → F.coeff α = 1 ∨ F.coeff α = -1}

/-- `f = ∑_{|α| = d} ε_α x^α`, the random sign form attached to a family of independent uniform
signs indexed by the exponent tuples of degree `d` (see `signMeasure`). -/
@[browning_sawin "def_uniform_sign_form"]
noncomputable def signForm (n d : ℕ) (ε : SignFamily (monomialsEq (n + 1) d)) :
    MvPolynomial (Fin (n + 1)) ℤ :=
  ∑ α ∈ monomialsEq (n + 1) d, monomial α (signOf ε α : ℤ)

/-- The coefficient of `f = ∑_{|α| = d} ε_α x^α` at a tuple of degree `d` is the sign `ε_α`. -/
@[simp]
theorem coeff_signForm {n d : ℕ} (ε : SignFamily (monomialsEq (n + 1) d)) {α : Fin (n + 1) →₀ ℕ}
    (hα : α.degree = d) : (signForm n d ε).coeff α = (signOf ε α : ℤ) := by
  classical
  rw [signForm, coeff_sum, Finset.sum_eq_single α (fun b _ hb => by simp [coeff_monomial, hb])
    (fun h => absurd (mem_monomialsEq.2 hα) h)]
  simp

/-! ### The affine sign polynomial and its coefficient blocks -/

/-- `g = ∑_{|β| ≤ d} ε_β y^β ∈ 𝔽ₚ[y₁,…,y_n]`, the dehomogenized random sign polynomial. -/
@[browning_sawin "def_affine_sign_poly"]
noncomputable def affineSignPoly (p n d : ℕ) (ε : SignFamily (monomialsLE n d)) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∑ β ∈ monomialsLE n d, monomial β ((signOf ε β : ℤ) : ZMod p)

/-- The coordinatewise reduction of an exponent tuple modulo `p`. -/
noncomputable def residueTuple (p : ℕ) {m : ℕ} (α : Fin m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.mapRange (· % p) (Nat.zero_mod p) α

/-- The tuples `0, e₁, …, e_m`: the residue classes modulo `p` singled out by the partition of the
coefficients of `g`. -/
noncomputable def specialTuples (m : ℕ) : Finset (Fin m →₀ ℕ) :=
  insert 0 (Finset.univ.image fun i : Fin m => Finsupp.single i 1)

/-- `H = ∑_{|β| ≤ t} ε_{pβ} y^β`, the block of coefficients whose exponent is `0` modulo `p`. -/
@[browning_sawin "def_block_H"]
noncomputable def blockH (p n d : ℕ) (ε : SignFamily (monomialsLE n d)) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∑ β ∈ monomialsLE n (upperBlockLength p d), monomial β ((signOf ε (p • β) : ℤ) : ZMod p)

/-- `G_i = ∑_{|β| ≤ s} ε_{pβ + e_i} y^β`, the block of coefficients whose exponent is `e_i`
modulo `p`. -/
@[browning_sawin "def_block_G"]
noncomputable def blockG (p n d : ℕ) (ε : SignFamily (monomialsLE n d)) (i : Fin n) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∑ β ∈ monomialsLE n (lowerBlockLength p d),
    monomial β ((signOf ε (p • β + Finsupp.single i 1) : ℤ) : ZMod p)

/-- `U = ∑_{α ≢ 0, e₁, …, e_n (p)} ε_α y^α`, the block of coefficients whose exponent avoids,
coordinatewise modulo `p`, each of the tuples `0, e₁, …, e_n`. -/
@[browning_sawin "def_block_U"]
noncomputable def blockU (p n d : ℕ) (ε : SignFamily (monomialsLE n d)) :
    MvPolynomial (Fin n) (ZMod p) :=
  ∑ α ∈ (monomialsLE n d).filter fun α => residueTuple p α ∉ specialTuples n,
    monomial α ((signOf ε α : ℤ) : ZMod p)

/-! ### The critical loci -/

/-- `W_i = Z(∂₁g, …, ∂_i g) ⊆ 𝔸ⁿ` over an algebraic closure of the base field; `W_0` is all of
`𝔸ⁿ`. -/
@[browning_sawin "def_critical_locus"]
def criticalLocus {k : Type*} [Field k] {n : ℕ} (g : MvPolynomial (Fin n) k) (i : ℕ) :
    Set (Fin n → AlgebraicClosure k) :=
  {a | ∀ j : Fin n, (j : ℕ) < i →
    eval a ((pderiv j g).map (algebraMap k (AlgebraicClosure k))) = 0}

/-- `W_0 = 𝔸ⁿ`: the critical locus of index `0` imposes no equation. -/
@[simp]
theorem criticalLocus_zero {k : Type*} [Field k] {n : ℕ} (g : MvPolynomial (Fin n) k) :
    criticalLocus g 0 = Set.univ := by
  ext a; simp [criticalLocus]

/-! ### Closed points and their local algebras

A closed point of `𝔸ⁿ_{𝔽ₚ}` is a maximal ideal of `S = 𝔽ₚ[y₁,…,y_n]`, that is an element of
`MaximalSpectrum S`. The definitions below are stated for an arbitrary commutative ring, which is
the generality they hold in. -/

section ClosedPoints

variable {R : Type*} [CommRing R]

/-- A **closed point** of `𝔸ⁿ_k`: a maximal ideal `𝔪_P` of `S = k[y₁,…,y_n]`. -/
@[browning_sawin "def_closed_point"]
abbrev ClosedPoint (k : Type*) [Field k] (n : ℕ) : Type _ :=
  MaximalSpectrum (MvPolynomial (Fin n) k)

/-- `κ(P) = S/𝔪_P`, the residue field at a closed point `P`. -/
@[browning_sawin "def_residue_field"]
abbrev residueFieldAt (P : MaximalSpectrum R) : Type _ := R ⧸ P.asIdeal

/-- `g(P)`, the image in `κ(P)` of an element `g` of `S`. -/
@[browning_sawin "def_residue_field"]
abbrev evalAt (P : MaximalSpectrum R) (g : R) : residueFieldAt P := Ideal.Quotient.mk P.asIdeal g

/-- `deg P = [κ(P) : k]`, the degree of a closed point of a `k`-algebra. -/
@[browning_sawin "def_point_degree"]
noncomputable def pointDegree (k : Type*) [Field k] [Algebra k R] (P : MaximalSpectrum R) : ℕ :=
  Module.finrank k (residueFieldAt P)

/-- `A_P = S/𝔪_P²`, the algebra of first-order jets at a closed point `P`. -/
@[browning_sawin "def_jet_algebra"]
abbrev jetAlgebra (P : MaximalSpectrum R) : Type _ := R ⧸ P.asIdeal ^ 2

end ClosedPoints

/-- `V_s`, the degree filtration of a `k`-algebra `A` with respect to a family of generators `y`:
the span of the monomials `y₁^{a₁} ⋯ y_m^{a_m}` with `a₁ + ⋯ + a_m ≤ s`. -/
@[browning_sawin "def_degree_filtration"]
def degreeFiltration (k : Type*) [Field k] {A : Type*} [CommRing A] [Algebra k A] {m : ℕ}
    (y : Fin m → A) (s : ℕ) : Submodule k A :=
  Submodule.span k {a | ∃ e : Fin m → ℕ, ∑ i, e i ≤ s ∧ a = ∏ i, y i ^ e i}

/-! ### Affine and projective algebraic sets -/

section AlgebraicSets

variable {K : Type*} [Field K] {n : ℕ}

/-- The ideal of polynomials vanishing on a set of affine points. -/
noncomputable def affineVanishingIdeal (V : Set (Fin n → K)) : Ideal (MvPolynomial (Fin n) K) :=
  ⨅ a ∈ V, RingHom.ker (MvPolynomial.eval a)

/-- A polynomial lies in the vanishing ideal of `V` exactly when it vanishes at every point of
`V`. -/
theorem mem_affineVanishingIdeal {V : Set (Fin n → K)} {F : MvPolynomial (Fin n) K} :
    F ∈ affineVanishingIdeal V ↔ ∀ a ∈ V, eval a F = 0 := by
  simp [affineVanishingIdeal, RingHom.mem_ker]

/-- `Z(h₁, …, h_j)`, the common geometric zero set, here as the zero locus in `𝔸ⁿ` of an ideal: the
zero set of a finite family of polynomials is this applied to the ideal the family spans, and
taking `K` to be an algebraic closure is what makes it geometric. -/
@[browning_sawin "def_zero_set"]
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

/-- The projective closure of an affine algebraic set, taken along the standard chart: the
projective zero locus of the forms vanishing on the cone over its image, which is exactly its
closure in the Zariski topology. -/
noncomputable def projectiveClosure (V : Set (Fin n → K)) :
    Set (Projectivization K (Fin (n + 1) → K)) :=
  projZeroLocus (coneVanishingIdeal (standardChart '' V))

/-- The distinct irreducible components of an affine algebraic set: the zero loci of the minimal
primes over its vanishing ideal. -/
noncomputable def irreducibleComponentsOf (V : Set (Fin n → K)) : Set (Set (Fin n → K)) :=
  affineZeroLocus '' (affineVanishingIdeal V).minimalPrimes

/-! ### Degrees of projective varieties -/

/-- The Hilbert function of a projective algebraic set `T`: the `K`-dimension of the degree-`q`
graded piece of the homogeneous coordinate ring of `T`. -/
noncomputable def projHilbertFunction (T : Set (Projectivization K (Fin (n + 1) → K)))
    (q : ℕ) : ℕ :=
  Module.finrank K (↥(homogeneousSubmodule (Fin (n + 1)) K q) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K q).subtype
      ((coneVanishingIdeal T).restrictScalars K))

open Classical in
/-- The Hilbert polynomial of a numerical function `H`: the polynomial that agrees with `H` at all
large arguments, and `0` when there is none. There is at most one such polynomial, so this is
well defined on the functions of interest; see `hilbertPolynomialOf_eq`. -/
noncomputable def hilbertPolynomialOf (H : ℕ → ℕ) : Polynomial ℚ :=
  if h : ∃ P : Polynomial ℚ, ∀ᶠ q : ℕ in atTop, P.eval (q : ℚ) = H q then h.choose else 0

/-- A polynomial agreeing with `H` at all large arguments is the Hilbert polynomial of `H`; in
particular there is at most one such polynomial. -/
theorem hilbertPolynomialOf_eq {H : ℕ → ℕ} {P : Polynomial ℚ}
    (hP : ∀ᶠ q : ℕ in atTop, P.eval (q : ℚ) = H q) : hilbertPolynomialOf H = P := by
  classical
  have hex : ∃ P : Polynomial ℚ, ∀ᶠ q : ℕ in atTop, P.eval (q : ℚ) = H q := ⟨P, hP⟩
  rw [hilbertPolynomialOf, dite_eq_left hex]
  obtain ⟨N, hN⟩ := (hex.choose_spec.and hP).exists_forall_of_atTop
  refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
  have hinj : Function.Injective fun m : ℕ => ((N + m : ℕ) : ℚ) := fun a b hab => by
    have h' : (N + a : ℕ) = (N + b : ℕ) := Nat.cast_injective hab
    omega
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro x ⟨m, rfl⟩
  exact (hN (N + m) (Nat.le_add_right _ _)).1.trans (hN (N + m) (Nat.le_add_right _ _)).2.symm

/-- `deg T` for an irreducible projective variety `T` of dimension `r`: the integer whose quotient
by `r !` is the leading coefficient of the Hilbert polynomial of the homogeneous coordinate ring of
`T`, so that the leading term of that polynomial is `(deg T) q^r / r !`. -/
@[browning_sawin "def_proj_degree"]
noncomputable def projDegree (T : Set (Projectivization K (Fin (n + 1) → K))) : ℕ :=
  ((Nat.factorial (hilbertPolynomialOf (projHilbertFunction T)).natDegree : ℚ) *
    (hilbertPolynomialOf (projHilbertFunction T)).leadingCoeff).num.toNat

/-- `δ(Z) = ∑_V deg V̄`, the sum of the degrees of the projective closures of the distinct
irreducible components of an affine algebraic set `Z`. The empty set has no components, so
`δ(∅) = 0`. -/
@[browning_sawin "def_delta"]
noncomputable def delta (V : Set (Fin n → K)) : ℕ :=
  ∑ᶠ W ∈ irreducibleComponentsOf V, projDegree (projectiveClosure W)

end AlgebraicSets

/-! ### Hypersurfaces and their singular loci -/

section Hypersurface

variable {k : Type*} [Field k] {n : ℕ}

/-- The reduction of a form to an algebraic closure of its field of coefficients. -/
noncomputable def toClosure (F : MvPolynomial (Fin (n + 1)) k) :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) := F.map (algebraMap k (AlgebraicClosure k))

/-- The coordinate ring of the affine cone `Z(F) ⊆ 𝔸ⁿ⁺¹` over an algebraic closure. Its scheme
structure retains repeated factors of `F`. -/
noncomputable abbrev coneRing (F : MvPolynomial (Fin (n + 1)) k) : Type _ :=
  MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) ⧸ Ideal.span {toClosure F}

/-- `X_F`, the hypersurface cut out by a nonzero homogeneous form `F` of positive degree, as the
set of its points over an algebraic closure of `k`. The scheme structure of `X_F` — in particular
the repeated factors of `F` — is carried by `F` itself, and it is what `singularLocus` sees. -/
@[browning_sawin "def_hypersurface"]
noncomputable def hypersurface (F : MvPolynomial (Fin (n + 1)) k) :
    Set (Projectivization (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k)) :=
  {P | eval P.rep (toClosure F) = 0}

/-- The generic point of `Spec k̄`: the zero ideal, prime because an algebraic closure is a
field. -/
noncomputable def genericPoint : PrimeSpectrum (AlgebraicClosure k) := ⟨⊥, Ideal.isPrime_bot⟩

/-- The point of the affine cone `Z(F)` cut out by a vector `a` on which `F` vanishes. -/
noncomputable def conePoint (F : MvPolynomial (Fin (n + 1)) k)
    (a : Fin (n + 1) → AlgebraicClosure k) (h : eval a (toClosure F) = 0) :
    PrimeSpectrum (coneRing F) :=
  PrimeSpectrum.comap
    (Ideal.Quotient.lift (Ideal.span {toClosure F}) (MvPolynomial.eval a) fun _ hx =>
      RingHom.mem_ker.mp
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 (RingHom.mem_ker.mpr h)) hx))
    genericPoint

/-- `Sing X_F`, the set of points of `X_F` over an algebraic closure of `k` at which `X_F` is not
smooth. Smoothness at a projective point is tested on the affine cone `Z(F) ⊆ 𝔸ⁿ⁺¹`: away from the
origin the cone is a `𝔾_m`-bundle over `X_F`, so it is smooth exactly over the smooth points
of `X_F`. -/
@[browning_sawin "def_singular_locus"]
noncomputable def singularLocus (F : MvPolynomial (Fin (n + 1)) k) :
    Set (Projectivization (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k)) :=
  {P | ∃ h : eval P.rep (toClosure F) = 0,
    conePoint F P.rep h ∉ Algebra.smoothLocus (AlgebraicClosure k) (coneRing F)}

/-- `Sing X_F ⊆ X_F`: a singular point of the hypersurface is a point of it. -/
theorem singularLocus_subset_hypersurface (F : MvPolynomial (Fin (n + 1)) k) :
    singularLocus F ⊆ hypersurface F := by
  intro P hP
  obtain ⟨h, -⟩ := hP
  exact h

/-- A nonzero homogeneous form of positive degree is *singular* when its hypersurface has a
singular point. -/
@[browning_sawin "def_singular_locus"]
def IsSingularForm (F : MvPolynomial (Fin (n + 1)) k) : Prop := (singularLocus F).Nonempty

end Hypersurface

/-! ### Closed points of projective space over a finite field -/

/-- The points of `ℙⁿ` over an algebraic closure of `𝔽ₚ`. -/
abbrev ProjPoint (p n : ℕ) [Fact p.Prime] : Type :=
  Projectivization (AlgebraicClosure (ZMod p)) (Fin (n + 1) → AlgebraicClosure (ZMod p))

/-- The `q`-power map on `ℙⁿ`, raising every homogeneous coordinate to the `q`-th power. For
`q = p` over `𝔽̄ₚ` this is the Frobenius map, whose orbits are the closed points. -/
noncomputable def projPowMap (q : ℕ) [NeZero q] {K : Type*} [Field K] {n : ℕ}
    (P : Projectivization K (Fin (n + 1) → K)) : Projectivization K (Fin (n + 1) → K) :=
  Projectivization.mk K (fun i => P.rep i ^ q) fun h =>
    P.rep_nonzero (funext fun i => by
      have := congrFun h i
      simpa [pow_eq_zero_iff (NeZero.ne q)] using this)

/-- `C_e`, the number of closed points `P` of `ℙⁿ_{𝔽ₚ}` with `deg P = e`. A closed point of degree
`e` is a Frobenius orbit of size `e` of points of `ℙⁿ(𝔽̄ₚ)`, its residue field being the degree-`e`
extension of `𝔽ₚ`; so the closed points of degree `e` are counted by the orbits of the `p`-power
map whose length is `e`. -/
@[browning_sawin "def_C_e"]
noncomputable def closedPointCount (p n e : ℕ) [Fact p.Prime] : ℕ :=
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  Nat.card {c : Cycle (ProjPoint p n) // ∃ P : ProjPoint p n,
    Function.minimalPeriod (projPowMap p) P = e ∧ c = Function.periodicOrbit (projPowMap p) P}

/-! ### The finite-field singularity probability -/

/-- `σ_{n,d}(p)`, the probability that the reduction modulo `p` of the random sign form `f` is
singular, the hypersurface being taken over `𝔽̄ₚ`. -/
@[browning_sawin "def_sigma"]
noncomputable def sigma (p n d : ℕ) [Fact p.Prime] : ℝ≥0∞ :=
  signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
    {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom (ZMod p)))}

end BrowningSawin
