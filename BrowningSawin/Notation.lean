/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import BrowningSawin.Attr
public import BrowningSawin.Defs.Definitions

/-!
# Notation and conventions for the Browning–Sawin conjecture

Most of the notation used in this development names operators that Mathlib already has. This file
records which Mathlib notion realises each of them, together with the facts about them the
estimates use, and gives in full the two conventions that are genuine definitions: the geometric
dimension of an algebraic set, with `dim ∅ = -1`, and the law of a family of independent uniform
signs.

## Conventions

* Exponent tuples are `Fin m →₀ ℕ`. For `α : Fin (n + 1) →₀ ℕ` the multi-index degree `|α|` is
  `Finsupp.degree α`, which is `α 0 + ⋯ + α n` by `Finsupp.degree_eq_sum`, and the monomial `x^α`
  is `MvPolynomial.monomial α 1`, which is `x₀ ^ α 0 ⋯ x_n ^ α n` by
  `MvPolynomial.monomial_eq_C_mul_prod_X_pow` below. Affine tuples `β : Fin n →₀ ℕ` are the same
  story in the variables `y₁, …, y_n`, and the standard basis vector `e_i` is `Finsupp.single i 1`,
  the exponent tuple of the variable `y_i` (`MvPolynomial.X_eq_monomial_single_one`) and of degree
  `1` (`Finsupp.degree_single`).
* `∂ᵢ` is `MvPolynomial.pderiv i`, in affine coordinates `y₁, …, y_n` (index type `Fin n`) and in
  homogeneous coordinates `x₀, …, x_n` (index type `Fin (n + 1)`) alike. It differentiates term by
  term (`MvPolynomial.pderiv_eq_sum_monomial`), commutes with reduction of the coefficients
  (`MvPolynomial.pderiv_map`, which is what makes `∂ᵢ` unambiguous along `ℤ → 𝔽ₚ → 𝔽̄ₚ`), drops the
  degree of a form by one (`MvPolynomial.IsHomogeneous.pderiv`), and satisfies Euler's identity
  (`MvPolynomial.IsHomogeneous.sum_X_mul_pderiv`).
* `a_d = O_n(b_d)` is `a =O[atTop] b` for `Asymptotics.IsBigO`: with `n` fixed, the implied
  constant depends on nothing else, and for a positive `b` this is exactly a bound valid for every
  `d` (`Asymptotics.isBigO_atTop_nat_iff_exists_forall`). Likewise `≪_n` is `IsBigO` and `o_n` is
  `Asymptotics.IsLittleO`. `log₂` is `Real.logb 2`.
* `dim` is `affineDim` on affine algebraic sets and `projDim` on projective ones, both valued in
  `ℤ` with `dim ∅ = -1`. Both are computed from the reduced coordinate ring —
  `affineVanishingIdeal` is radical (`isRadical_affineVanishingIdeal`), so the quotient is reduced
  with no further ado — and both are applied to sets of points over an algebraic closure, where the
  geometric objects of this development live.
* `𝐏` is a measure applied to a set. A family of independent uniform signs is the family of
  coordinate functions on `ι → ℤˣ` under `signMeasure ι`: they are independent
  (`iIndepFun_signMeasure`) and each takes each of the two values `1` and `-1` with probability
  `1/2` (`signMeasure_apply_eq`), the law of a single one being `signLaw`.
-/

@[expose] public section

open Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## Multi-index notation -/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- `x^α = x₀ ^ α₀ ⋯ x_n ^ α_n`: a monomial is the product, over *all* the variables, of the powers
prescribed by its exponent tuple. Mathlib's `MvPolynomial.monomial_eq` takes the product over the
support of `α` instead. -/
@[browning_sawin "not_multiindex_hom"]
theorem monomial_eq_C_mul_prod_X_pow [Fintype σ] (α : σ →₀ ℕ) (r : R) :
    monomial α r = C r * ∏ i, X i ^ α i := by
  rw [monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype]
  simp

/-- `e_i` is the exponent tuple of the variable `y_i`. -/
@[browning_sawin "not_multiindex_aff"]
theorem X_eq_monomial_single_one (i : σ) :
    (X i : MvPolynomial σ R) = monomial (Finsupp.single i 1) 1 := rfl

/-- `y^β` as a function of the point `y`: evaluating a monomial multiplies its coefficient by
`y₁ ^ β₁ ⋯ y_n ^ β_n`. Mathlib's `MvPolynomial.eval_monomial` takes the product over the support of
`β` instead. -/
@[browning_sawin "not_multiindex_aff"]
theorem eval_monomial_eq_mul_prod [Fintype σ] (y : σ → R) (β : σ →₀ ℕ) (r : R) :
    eval y (monomial β r) = r * ∏ i, y i ^ β i := by
  rw [eval_monomial, Finsupp.prod_fintype]
  simp

/-! ## Partial derivatives -/

/-- `∂ᵢ` differentiates term by term: this is the coefficientwise description of `pderiv i`,
written `∂g/∂y_i` in affine coordinates and `∂F/∂x_i` in homogeneous ones. -/
@[browning_sawin "not_derivative"]
theorem pderiv_eq_sum_monomial (i : σ) (g : MvPolynomial σ R) :
    pderiv i g = ∑ β ∈ g.support, monomial (β - Finsupp.single i 1) (g.coeff β * (β i : R)) := by
  conv_lhs => rw [g.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun β _ => by rw [pderiv_monomial]

/-- Evaluating a homogeneous polynomial of degree `e` at `c • a` scales the value by `c ^ e`. -/
theorem eval_smul_of_isHomogeneous [Finite σ] {e : ℕ} {G : MvPolynomial σ R}
    (hG : G.IsHomogeneous e) (c : R) (a : σ → R) :
    eval (c • a) G = c ^ e * eval a G := by
  cases nonempty_fintype σ
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdeg : ∑ i, α i = e := by
    have h := hG (mem_support_iff.1 hα)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simpa using h
  have hprod : ∏ i, (c • a) i ^ α i = c ^ e * ∏ i, a i ^ α i := by
    rw [← hdeg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [hprod]; ring

end MvPolynomial

/-! ## Asymptotic notation -/

namespace Asymptotics

/-- `a_d = O(b_d)` for a positive `b`, spelled out: the implied constant can be taken to work for
*every* `d`, not merely for all large `d`, because the finitely many small `d` can be absorbed into
it. The notation `O_n` is this statement with the ambient `n` fixed, so that the constant produced
depends on `n` alone. -/
@[browning_sawin "not_asymptotic"]
theorem isBigO_atTop_nat_iff_exists_forall {E : Type*} [SeminormedAddGroup E] {a : ℕ → E}
    {b : ℕ → ℝ} (hb : ∀ d, 0 < b d) : a =O[atTop] b ↔ ∃ C : ℝ, ∀ d, ‖a d‖ ≤ C * b d := by
  refine ⟨fun h => ?_, fun ⟨C, hC⟩ => isBigO_iff.2 ⟨C, .of_forall fun d => by
    simpa [abs_of_pos (hb d)] using hC d⟩⟩
  obtain ⟨c, hc, hcb⟩ := h.exists_pos
  obtain ⟨N, hN⟩ := hcb.bound.exists_forall_of_atTop
  refine ⟨c + ∑ d ∈ Finset.range N, ‖a d‖ / b d, fun d => ?_⟩
  have hsum : (0 : ℝ) ≤ ∑ d ∈ Finset.range N, ‖a d‖ / b d :=
    Finset.sum_nonneg fun d _ => div_nonneg (norm_nonneg _) (hb d).le
  rcases le_or_gt N d with hd | hd
  · calc ‖a d‖ ≤ c * ‖b d‖ := hN d hd
      _ = c * b d := by rw [Real.norm_eq_abs, abs_of_pos (hb d)]
      _ ≤ (c + ∑ d ∈ Finset.range N, ‖a d‖ / b d) * b d :=
          mul_le_mul_of_nonneg_right (by linarith) (hb d).le
  · have h1 : ‖a d‖ / b d ≤ ∑ e ∈ Finset.range N, ‖a e‖ / b e :=
      Finset.single_le_sum (f := fun e => ‖a e‖ / b e)
        (fun e _ => div_nonneg (norm_nonneg _) (hb e).le) (Finset.mem_range.2 hd)
    rw [div_le_iff₀ (hb d)] at h1
    nlinarith [hb d, hc]

end Asymptotics

/-! ## Measurability of the sign group -/

/-- Singletons of `Mˣ` are measurable as soon as singletons of `M` are: the measurable structure on
`Mˣ` is pulled back along the injection `Units.val`. -/
instance Units.measurableSingletonClass {M : Type*} [Monoid M] [MeasurableSpace M]
    [MeasurableSingletonClass M] : MeasurableSingletonClass Mˣ where
  measurableSet_singleton u :=
    ⟨{(u : M)}, measurableSet_singleton _, by ext v; simp [Units.ext_iff]⟩

namespace BrowningSawin

open MvPolynomial

/-! ## Geometric dimension

`dim` is geometric — every algebraic set it is applied to is a set of points over an algebraic
closure — and it gives the empty set dimension `-1`. A closed set is used only through its
dimension, so it may be given its reduced structure; concretely the coordinate ring below is the
quotient by the vanishing ideal, which is radical. -/

section Dimension

variable {K : Type*} [Field K] {n : ℕ}

/-- The vanishing ideal of a set of points is radical, so the coordinate ring
`K[y₁, …, y_n] ⧸ I(V)` used to compute `affineDim` is reduced. -/
theorem isRadical_affineVanishingIdeal (V : Set (Fin n → K)) :
    (affineVanishingIdeal V).IsRadical := by
  intro F hF
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.1 hF
  rw [mem_affineVanishingIdeal] at hm
  rw [mem_affineVanishingIdeal]
  intro a ha
  have h := hm a ha
  rw [map_pow] at h
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simp at h
  · exact (pow_eq_zero_iff hpos.ne').1 h

/-- Only the empty set has no nonzero polynomial functions on it. -/
theorem affineVanishingIdeal_eq_top_iff {V : Set (Fin n → K)} :
    affineVanishingIdeal V = ⊤ ↔ V = ∅ := by
  constructor
  · intro h
    by_contra hV
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 hV
    have h1 : (1 : MvPolynomial (Fin n) K) ∈ affineVanishingIdeal V := h ▸ Submodule.mem_top
    rw [mem_affineVanishingIdeal] at h1
    simpa using h1 a ha
  · rintro rfl
    rw [eq_top_iff]
    intro F _
    rw [mem_affineVanishingIdeal]
    simp

/-- `dim V`, the dimension of a set `V` of points of affine `n`-space: the Krull dimension of its
reduced coordinate ring `K[y₁, …, y_n] ⧸ I(V)`, with the empty set given dimension `-1`. It is
geometric when, as everywhere in this development, `K` is an algebraic closure. -/
@[browning_sawin "not_dimension"]
noncomputable def affineDim (V : Set (Fin n → K)) : ℤ :=
  (ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)).recBotCoe (-1)
    fun r => (r.toNat : ℤ)

/-- The empty affine algebraic set has dimension `-1`. -/
@[browning_sawin "not_dimension"]
theorem affineDim_empty : affineDim (∅ : Set (Fin n → K)) = -1 := by
  have hsub : Subsingleton (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal (∅ : Set (Fin n → K))) :=
    Ideal.Quotient.subsingleton_iff.2 (affineVanishingIdeal_eq_top_iff.2 rfl)
  rw [affineDim, ringKrullDim_eq_bot_of_subsingleton]
  rfl

/-- Every set of points of affine `n`-space has dimension at least `-1`. -/
theorem neg_one_le_affineDim (V : Set (Fin n → K)) : -1 ≤ affineDim V := by
  rw [affineDim]
  cases ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) with
  | bot => simp
  | coe r => simp

/-- A nonempty affine algebraic set has dimension at least `0`. -/
theorem zero_le_affineDim {V : Set (Fin n → K)} (hV : V.Nonempty) : 0 ≤ affineDim V := by
  have hnt : Nontrivial (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff,
      affineVanishingIdeal_eq_top_iff]
    exact Set.nonempty_iff_ne_empty.1 hV
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [affineDim]
  cases hcase : ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V) with
  | bot => rw [hcase] at h0; simp at h0
  | coe r => simp

/-- Dimension `-1` characterizes the empty set. -/
theorem affineDim_eq_neg_one_iff {V : Set (Fin n → K)} : affineDim V = -1 ↔ V = ∅ := by
  refine ⟨fun h => ?_, fun h => h ▸ affineDim_empty⟩
  by_contra hV
  have := zero_le_affineDim (Set.nonempty_iff_ne_empty.2 hV)
  omega

/-- An affine algebraic set in `n` variables has dimension at most `n`; in particular its dimension
is finite. -/
theorem affineDim_le (V : Set (Fin n → K)) : affineDim V ≤ n := by
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
      simp only [WithBot.recBotCoe_coe, Nat.cast_le]
      have hrn : r ≤ (n : ℕ∞) := by exact_mod_cast hle
      exact_mod_cast ENat.toNat_le_of_le_natCast hrn

/-- The affine cone over the empty set of projective points is empty. -/
theorem affineCone_empty :
    affineCone (∅ : Set (Projectivization K (Fin (n + 1) → K))) = ∅ := by
  ext a; simp [affineCone]

/-- The affine cone over a nonempty set of projective points is nonempty. -/
theorem affineCone_nonempty {T : Set (Projectivization K (Fin (n + 1) → K))} (hT : T.Nonempty) :
    (affineCone T).Nonempty := by
  obtain ⟨P, hP⟩ := hT
  exact ⟨(1 : K) • P.rep, P, hP, 1, rfl⟩

/-- `dim T`, the dimension of a set `T` of points of projective `n`-space: one less than the
dimension of its affine cone, the cone over a nonempty `T` being a bundle of punctured lines over
`T` together with the origin. The empty set is given dimension `-1`. -/
@[browning_sawin "not_dimension"]
noncomputable def projDim (T : Set (Projectivization K (Fin (n + 1) → K))) : ℤ :=
  max (-1) (affineDim (affineCone T) - 1)

/-- The empty projective algebraic set has dimension `-1`. -/
@[browning_sawin "not_dimension"]
theorem projDim_empty : projDim (∅ : Set (Projectivization K (Fin (n + 1) → K))) = -1 := by
  rw [projDim, affineCone_empty, affineDim_empty]
  norm_num

/-- For a nonempty projective algebraic set the truncation in the definition of `projDim` is
inactive: the dimension is that of the affine cone, less one. -/
theorem projDim_eq_affineDim_cone_sub_one {T : Set (Projectivization K (Fin (n + 1) → K))}
    (hT : T.Nonempty) : projDim T = affineDim (affineCone T) - 1 := by
  have h := zero_le_affineDim (affineCone_nonempty hT)
  rw [projDim, max_eq_right (by omega)]

/-- Every set of points of projective `n`-space has dimension at least `-1`. -/
theorem neg_one_le_projDim (T : Set (Projectivization K (Fin (n + 1) → K))) : -1 ≤ projDim T :=
  le_max_left _ _

/-- A set of points of projective `n`-space has dimension at most `n`. -/
theorem projDim_le (T : Set (Projectivization K (Fin (n + 1) → K))) : projDim T ≤ n := by
  have h := affineDim_le (affineCone T)
  rw [projDim]
  push_cast at h ⊢
  omega

end Dimension

/-! ## Probability

`𝐏` is a measure applied to a set, the measure being a probability measure. A family of independent
uniform signs is an indexed family of `ℤˣ`-valued random variables; it is realized as the family of
coordinate functions on `ι → ℤˣ` under `signMeasure ι`, and the two results below are exactly the
two clauses of the convention: the coordinates are independent, and each is a uniform sign. -/

section Probability

/-- The law of a uniform sign: the uniform probability measure on `ℤˣ = {1, -1}`. -/
@[browning_sawin "not_probability"]
noncomputable def signLaw : Measure ℤˣ := (PMF.uniformOfFintype ℤˣ).toMeasure

/-- The law of a uniform sign is a probability measure. -/
instance : IsProbabilityMeasure signLaw := by unfold signLaw; infer_instance

/-- A uniform sign takes each of the two values `1` and `-1` with probability `1/2`. -/
@[browning_sawin "not_probability"]
theorem signLaw_apply_singleton (u : ℤˣ) : signLaw {u} = 2⁻¹ := by
  rw [signLaw, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton u),
    PMF.uniformOfFintype_apply, Fintype.card_units_int]
  norm_num

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- `signMeasure ι` is the product of `ι` copies of the law of a uniform sign. -/
theorem signMeasure_eq_pi : signMeasure ι = Measure.pi fun _ : ι => signLaw := by
  refine Measure.ext_of_singleton fun ε => ?_
  have h1 : signMeasure ι {ε} = ((2 : ℝ≥0∞) ^ Fintype.card ι)⁻¹ := by
    rw [signMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton ε),
      PMF.uniformOfFintype_apply, Fintype.card_pi]
    simp [Fintype.card_units_int]
  have h2 : Measure.pi (fun _ : ι => signLaw) {ε} = ((2 : ℝ≥0∞) ^ Fintype.card ι)⁻¹ := by
    rw [← Set.univ_pi_singleton ε, Measure.pi_pi]
    simp [signLaw_apply_singleton, ENNReal.inv_pow]
  rw [h1, h2]

/-- The signs of a family of independent uniform signs are independent random variables. -/
@[browning_sawin "not_probability"]
theorem iIndepFun_signMeasure :
    iIndepFun (fun (i : ι) (ε : ι → ℤˣ) => ε i) (signMeasure ι) := by
  rw [signMeasure_eq_pi]
  exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id

/-- Each sign of a family of independent uniform signs is a uniform sign: it equals each of `1` and
`-1` with probability `1/2`. -/
@[browning_sawin "not_probability"]
theorem signMeasure_apply_eq (i : ι) (u : ℤˣ) : signMeasure ι {ε | ε i = u} = 2⁻¹ := by
  have hset : {ε : ι → ℤˣ | ε i = u} = Set.univ.pi fun j => if j = i then {u} else Set.univ := by
    ext ε
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine ⟨fun h j => ?_, fun h => by simpa using h i⟩
    by_cases hj : j = i <;> simp [hj, h]
  rw [signMeasure_eq_pi, hset, Measure.pi_pi,
    Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simpa using signLaw_apply_singleton u

end Probability

end BrowningSawin
