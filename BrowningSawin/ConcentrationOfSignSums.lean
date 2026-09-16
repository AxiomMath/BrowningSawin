/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import BrowningSawin.Attr
public import BrowningSawin.Defs.Definitions
public import BrowningSawin.Notation

/-!
# Concentration of sign sums

A sum `∑ ε_j v_j` of vectors with independent uniform sign coefficients does not concentrate on any
single value. Two bounds make this quantitative: a rank bound over any ring in which `2 ≠ 0`, and a
Fourier–Hölder bound over `𝔽ₚ`, expressed through the cosine average `Θ_K(p)`.

## Main results

* `log_cos_le_neg_sq_div_two`: `log cos x ≤ -x²/2` for `0 ≤ x < π/2`.
* `theta_le_inv_add_sqrt`: `Θ_K(p) ≤ 1/p + √(2/(πK))` for odd `p` and `K ≥ 1`.
* `signMeasure_sign_sum_le_inv_two_pow`: if `r` of the vectors `v_j` are linearly independent over
  a ring in which `2 ≠ 0`, then `∑ ε_j v_j` takes any prescribed value with probability at most
  `2 ^ (-r)`.
* `signMeasure_sign_sum_le_theta_pow`: if among the vectors `v_j ∈ 𝔽ₚ^L` there are `K` pairwise
  disjoint groups, each indexing a basis of `𝔽ₚ^L`, then `∑ ε_j v_j` takes any prescribed value
  with probability at most `Θ_K(p)^L`.
-/

@[expose] public section

namespace BrowningSawin

open scoped ENNReal Real

/-! ### A logarithmic cosine bound -/

/-- `log cos x ≤ -x²/2` for `0 ≤ x < π/2`. -/
@[browning_sawin "lem_log_cos"]
theorem log_cos_le_neg_sq_div_two {x : ℝ} (hx : 0 ≤ x) (hx2 : x < π / 2) :
    Real.log (Real.cos x) ≤ -x ^ 2 / 2 := by
  have hcos : ∀ y ∈ Set.Icc (0 : ℝ) x, 0 < Real.cos y := fun y hy =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hy.1, Real.pi_pos], lt_of_le_of_lt hy.2 hx2⟩
  have key : ∀ y ∈ Set.Ioo (0 : ℝ) x,
      HasDerivAt (fun z : ℝ => Real.log (Real.cos z) + z ^ 2 / 2) (-Real.tan y + y) y := by
    intro y hy
    have hcy : Real.cos y ≠ 0 := (hcos y ⟨hy.1.le, hy.2.le⟩).ne'
    have h1 : HasDerivAt (fun z : ℝ => Real.log (Real.cos z)) (-Real.sin y / Real.cos y) y :=
      (Real.hasDerivAt_cos y).log hcy
    have h2 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
      simpa using (hasDerivAt_pow 2 y).div_const 2
    have h3 := h1.add h2
    rwa [show -Real.tan y + y = -Real.sin y / Real.cos y + y by
      rw [Real.tan_eq_sin_div_cos]; ring]
  have hanti : AntitoneOn (fun z : ℝ => Real.log (Real.cos z) + z ^ 2 / 2) (Set.Icc 0 x) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 x) (fun y hy => ?_) ?_ ?_
    · exact ((Real.continuous_cos.continuousAt.log (hcos y hy).ne').add
        ((continuous_pow 2).continuousAt.div_const 2)).continuousWithinAt
    · rw [interior_Icc]
      exact fun y hy => (key y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro y hy
      rw [(key y hy).deriv]
      have := Real.lt_tan hy.1 (hy.2.trans hx2)
      linarith
  have h0 := hanti (Set.left_mem_Icc.2 hx) (Set.right_mem_Icc.2 hx) hx
  norm_num at h0
  linarith

/-! ### The cosine average -/

/-- Taking absolute values makes `cos` periodic with period `π`. -/
theorem abs_cos_add_intCast_mul_pi (x : ℝ) (k : ℤ) : |Real.cos (x + k * π)| = |Real.cos x| := by
  have h : Real.cos (2 * (x + (k : ℝ) * π)) = Real.cos (2 * x) := by
    rw [show 2 * (x + (k : ℝ) * π) = 2 * x + (k : ℝ) * (2 * π) by ring]
    exact Real.cos_add_int_mul_two_pi (2 * x) k
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, Real.cos_sq, Real.cos_sq, h]

/-- A sum over `ZMod p` of a function of the representative `a.val` is a sum over `range p`. -/
theorem sum_zmod_val_eq_sum_range {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ a : ZMod p, g a.val = ∑ i ∈ Finset.range p, g i :=
  Finset.sum_nbij' (i := fun a : ZMod p => a.val) (j := fun i : ℕ => (i : ZMod p))
    (fun a _ => Finset.mem_range.2 (ZMod.val_lt a)) (fun _ _ => Finset.mem_univ _)
    (fun a _ => by simp) (fun i hi => ZMod.val_cast_of_lt (Finset.mem_range.mp hi))
    (fun _ _ => rfl)

/-- `Θ_K(p) ≤ 1/p + √(2/(πK))` for odd `p` and `K ≥ 1`. -/
@[browning_sawin "lem_theta_bound"]
theorem theta_le_inv_add_sqrt {p K : ℕ} [NeZero p] (hp : Odd p) (hK : 0 < K) :
    theta p K ≤ 1 / p + Real.sqrt (2 / (π * K)) := by
  have hppos : (0 : ℝ) < p := Nat.cast_pos.2 (NeZero.pos p)
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set f : ℕ → ℝ := fun i => |Real.cos (π * i / p)| ^ K with hf
  have h2unit : IsUnit (2 : ZMod p) := by
    have h : ((2 : ℕ) : ZMod p) = (2 : ZMod p) := by push_cast; ring
    rw [← h, ZMod.isUnit_iff_coprime]
    refine Nat.prime_two.coprime_iff_not_dvd.2 fun hdvd => ?_
    obtain ⟨m, hm⟩ := hdvd
    obtain ⟨n, hn⟩ := hp
    omega
  have hbij : Function.Bijective (fun a : ZMod p => 2 * a) :=
    Finite.injective_iff_bijective.1 fun a b hab => h2unit.mul_left_cancel hab
  have hsum : ∑ a : ZMod p, |Real.cos (2 * π * (a.val : ℝ) / p)| ^ K
      = ∑ i ∈ Finset.range p, f i := by
    rw [← sum_zmod_val_eq_sum_range (p := p) f]
    refine Fintype.sum_bijective (fun a : ZMod p => 2 * a) hbij _ _ fun a => ?_
    obtain ⟨k, hk⟩ : (p : ℤ) ∣ 2 * (a.val : ℤ) - ((2 * a).val : ℤ) := by
      refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
      push_cast
      simp [ZMod.natCast_val, ZMod.cast_id]
    have hval : (((2 * a).val : ℕ) : ℝ) = 2 * (a.val : ℝ) - (p : ℝ) * (k : ℝ) := by
      have h : (2 * (a.val : ℤ) - ((2 * a).val : ℤ) : ℤ) = (p : ℤ) * k := hk
      have h' : (2 * (a.val : ℝ) - (((2 * a).val : ℕ) : ℝ)) = (p : ℝ) * (k : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h
      linarith
    have hangle : π * ((((2 * a).val : ℕ) : ℝ)) / p
        = 2 * π * (a.val : ℝ) / p + ((-k : ℤ) : ℝ) * π := by
      rw [hval]
      push_cast
      field_simp
      ring
    simp only [hf, hangle, abs_cos_add_intCast_mul_pi]
  obtain ⟨q, hq'⟩ := hp
  have hq : p = 2 * q + 1 := by omega
  have hpair : ∀ r : ℕ, r ≤ p → f (p - r) = f r := by
    intro r hr
    have h : π * (((p - r : ℕ) : ℝ)) / p = π - π * (r : ℝ) / p := by
      rw [Nat.cast_sub hr]
      field_simp
    simp only [hf, h, Real.cos_pi_sub, abs_neg]
  have hfold : ∑ i ∈ Finset.range p, f i = 1 + 2 * ∑ i ∈ Finset.range q, f (i + 1) := by
    have hrefl : ∑ i ∈ Finset.range q, f (q + i + 1) = ∑ i ∈ Finset.range q, f (i + 1) := by
      rw [← Finset.sum_range_reflect (fun i => f (q + i + 1)) q]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < q := Finset.mem_range.mp hj
      rw [show q + (q - 1 - j) + 1 = p - (j + 1) by omega, hpair (j + 1) (by omega)]
    have h0 : f 0 = 1 := by simp [hf]
    rw [show Finset.range p = Finset.range (2 * q + 1) by rw [hq],
      Finset.sum_range_succ' f (2 * q), show 2 * q = q + q from by ring,
      Finset.sum_range_add (fun i => f (i + 1)) q q, hrefl, h0]
    ring
  set c : ℝ := K * π ^ 2 / (2 * p ^ 2) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hterm : ∀ i ∈ Finset.range q, f (i + 1) ≤ Real.exp (-c * ((i : ℝ) + 1) ^ 2) := by
    intro i hi
    have hi' : i < q := Finset.mem_range.mp hi
    have hnum : 2 * ((i : ℝ) + 1) < p := by
      have h : (2 * (i + 1) : ℕ) < p := by omega
      calc 2 * ((i : ℝ) + 1) = ((2 * (i + 1) : ℕ) : ℝ) := by push_cast; ring
        _ < p := Nat.cast_lt.2 h
    have hxeq : π * (((i + 1 : ℕ) : ℝ)) / p = π * ((i : ℝ) + 1) / p := by push_cast; ring
    have hx0 : 0 ≤ π * ((i : ℝ) + 1) / p := by positivity
    have hxlt : π * ((i : ℝ) + 1) / p < π / 2 := by
      rw [div_lt_div_iff₀ hppos two_pos]
      nlinarith [Real.pi_pos]
    have hcospos : 0 < Real.cos (π * ((i : ℝ) + 1) / p) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxlt⟩
    have hlog := log_cos_le_neg_sq_div_two hx0 hxlt
    have hsq : (π * ((i : ℝ) + 1) / p) ^ 2 = π ^ 2 * ((i : ℝ) + 1) ^ 2 / p ^ 2 := by
      field_simp
    have hexp : (K : ℝ) * Real.log (Real.cos (π * ((i : ℝ) + 1) / p)) ≤ -c * ((i : ℝ) + 1) ^ 2 := by
      have h1 : (K : ℝ) * Real.log (Real.cos (π * ((i : ℝ) + 1) / p))
          ≤ (K : ℝ) * (-(π * ((i : ℝ) + 1) / p) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg K)
      have h2 : (K : ℝ) * (-(π * ((i : ℝ) + 1) / p) ^ 2 / 2) = -c * ((i : ℝ) + 1) ^ 2 := by
        rw [hc, hsq]
        field_simp
      linarith
    calc f (i + 1) = Real.cos (π * ((i : ℝ) + 1) / p) ^ K := by
          simp only [hf, hxeq, abs_of_pos hcospos]
      _ = Real.exp ((K : ℝ) * Real.log (Real.cos (π * ((i : ℝ) + 1) / p))) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos hcospos K)]
      _ ≤ Real.exp (-c * ((i : ℝ) + 1) ^ 2) := Real.exp_le_exp.2 hexp
  have hsumint : ∑ i ∈ Finset.range q, Real.exp (-c * ((i : ℝ) + 1) ^ 2)
      ≤ Real.sqrt (π / c) / 2 := by
    have hanti : AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Set.Icc 0 (0 + (q : ℝ))) := by
      intro y hy z hz hyz
      refine Real.exp_le_exp.2 ?_
      have hy2 : y ^ 2 ≤ z ^ 2 := by nlinarith [hy.1]
      nlinarith [hcpos.le]
    have h1 := hanti.sum_le_integral
    have h2 : ∫ x in (0 : ℝ)..(0 + (q : ℝ)), Real.exp (-c * x ^ 2) ≤ Real.sqrt (π / c) / 2 := by
      rw [← integral_gaussian_Ioi c, intervalIntegral.integral_of_le (by positivity)]
      exact MeasureTheory.setIntegral_mono_set (integrable_exp_neg_mul_sq hcpos).integrableOn
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
        (LE.le.eventuallyLE Set.Ioc_subset_Ioi_self)
    refine le_trans (le_of_eq ?_) (le_trans h1 h2)
    exact Finset.sum_congr rfl fun i _ => by norm_num
  have hsqrt : Real.sqrt (π / c) = p * Real.sqrt (2 / (π * K)) := by
    rw [show π / c = (p : ℝ) ^ 2 * (2 / (π * K)) by rw [hc]; field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hppos.le]
  have hfinal : ∑ a : ZMod p, |Real.cos (2 * π * (a.val : ℝ) / p)| ^ K
      ≤ 1 + (p : ℝ) * Real.sqrt (2 / (π * K)) := by
    rw [hsum, hfold]
    have := Finset.sum_le_sum hterm
    rw [← hsqrt]
    linarith [hsumint, this]
  rw [theta, div_le_iff₀ hppos]
  calc ∑ a : ZMod p, |Real.cos (2 * π * (a.val : ℝ) / p)| ^ K
      ≤ 1 + (p : ℝ) * Real.sqrt (2 / (π * K)) := hfinal
    _ = (1 / p + Real.sqrt (2 / (π * K))) * p := by field_simp

/-! ### The rank bound -/

/-- The law of a family of independent uniform signs is uniform: the measure of a finite set of
sign families is its cardinality divided by `2 ^ #ι`. -/
theorem signMeasure_coe_finset {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset (ι → ℤˣ)) :
    signMeasure ι s = s.card / 2 ^ Fintype.card ι := by
  rw [signMeasure, PMF.toMeasure_apply_finset]
  simp [PMF.uniformOfFintype_apply, Fintype.card_pi, Fintype.card_units_int,
    ENNReal.div_eq_inv_mul, mul_comm]

/-- If `r` of the vectors `v_j` are linearly independent over a ring in which `2 ≠ 0`, then a sum
`∑ ε_j v_j` with independent uniform sign coefficients takes any prescribed value with probability
at most `2 ^ (-r)`. -/
@[browning_sawin "lem_rank"]
theorem signMeasure_sign_sum_le_inv_two_pow {k V ι : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (h2 : (2 : k) ≠ 0) {v : ι → V} {J : Finset ι}
    (hJ : LinearIndependent k fun j : J => v j) (u : V) :
    signMeasure ι {ε | ∑ j, (ε j : ℤ) • v j = u} ≤ (2 ^ J.card)⁻¹ := by
  classical
  set S : Finset (ι → ℤˣ) := {ε | ∑ j, (ε j : ℤ) • v j = u} with hS
  have hset : {ε : ι → ℤˣ | ∑ j, (ε j : ℤ) • v j = u} = ↑S := by
    rw [hS]; ext ε; simp
  have hinj : Set.InjOn (fun (ε : ι → ℤˣ) (j : {j : ι // j ∉ J}) => ε j.1) S := by
    intro ε hε ε' hε' hg
    have hout : ∀ j ∉ J, ε j = ε' j := fun j hj => congrFun hg ⟨j, hj⟩
    have hsum : ∑ j, ((ε j : ℤ) - (ε' j : ℤ)) • v j = 0 := by
      have h1 : ∑ j, (ε j : ℤ) • v j = u := by simpa [hS] using hε
      have h2 : ∑ j, (ε' j : ℤ) • v j = u := by simpa [hS] using hε'
      simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]
    have hJsum : ∑ j ∈ J, (((ε j : ℤ) - (ε' j : ℤ) : ℤ) : k) • v j = 0 := by
      rw [Finset.sum_congr rfl fun j _ => Int.cast_smul_eq_zsmul k _ (v j)]
      rw [Finset.sum_subset (Finset.subset_univ J) fun j _ hj => by
        rw [hout j hj]; simp]
      exact hsum
    have hcoeff : ∀ j ∈ J, (((ε j : ℤ) - (ε' j : ℤ) : ℤ) : k) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hJ)
        (fun j : J => (((ε j.1 : ℤ) - (ε' j.1 : ℤ) : ℤ) : k)) (by
          rw [← Finset.sum_coe_sort J fun j => (((ε j : ℤ) - (ε' j : ℤ) : ℤ) : k) • v j] at hJsum
          exact hJsum)
      exact fun j hj => this ⟨j, hj⟩
    funext j
    by_cases hj : j ∈ J
    · have h0 := hcoeff j hj
      rcases Int.units_eq_one_or (ε j) with h | h <;> rcases Int.units_eq_one_or (ε' j) with h' | h'
      · rw [h, h']
      · rw [h, h'] at h0
        norm_num at h0
        exact absurd h0 h2
      · rw [h, h'] at h0
        norm_num at h0
        exact absurd h0 h2
      · rw [h, h']
    · exact hout j hj
  have hcard : S.card ≤ 2 ^ (Fintype.card ι - J.card) := by
    have h1 : S.card ≤ Fintype.card ({j : ι // j ∉ J} → ℤˣ) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
    calc S.card ≤ Fintype.card ({j : ι // j ∉ J} → ℤˣ) := h1
      _ = 2 ^ (Fintype.card ι - J.card) := by
          rw [Fintype.card_fun, Fintype.card_units_int, Fintype.card_subtype_compl,
            Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hJle : J.card ≤ Fintype.card ι := by
    simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [hset, signMeasure_coe_finset]
  calc (S.card : ℝ≥0∞) / 2 ^ Fintype.card ι
      ≤ (2 : ℝ≥0∞) ^ (Fintype.card ι - J.card) / 2 ^ Fintype.card ι :=
        ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ = ((2 : ℝ≥0∞) ^ J.card)⁻¹ := by
        rw [show (2 : ℝ≥0∞) ^ Fintype.card ι
            = 2 ^ (Fintype.card ι - J.card) * 2 ^ J.card by
          rw [← pow_add]; congr 1; omega]
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (by simp) (by simp),
          mul_comm ((2 : ℝ≥0∞) ^ (Fintype.card ι - J.card))⁻¹, mul_assoc,
          ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-! ### The Fourier–Hölder point bound -/

/-- An additive character turns a finite sum into a product. -/
theorem addChar_map_sum_eq_prod {A M ι : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, ψ.map_add_eq_mul, ih]

/-- The standard additive character of `ZMod p` is `ψ(a) = exp(2πi a/p)`, a residue being
represented by `a.val`. -/
theorem coe_stdAddChar_apply {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a = Complex.exp (2 * π * Complex.I * a.val / p) := by
  have h : ((a.val : ℕ) : ZMod p) = a := by simp
  rw [ZMod.stdAddChar_apply]
  conv_lhs => rw [← h]
  exact ZMod.toCircle_natCast a.val

/-- The expectation of `ψ(ε a)` over a uniform sign `ε` is `cos(2π a/p)`. -/
theorem stdAddChar_add_stdAddChar_neg {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a + ZMod.stdAddChar (-a) = 2 * (Real.cos (2 * π * a.val / p) : ℂ) := by
  have hθ : (2 * (π : ℂ) * Complex.I * (a.val : ℂ) / p)
      = ((2 * π * (a.val : ℝ) / p : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [Complex.ofReal_cos, Complex.two_cos, AddChar.map_neg_eq_inv, coe_stdAddChar_apply, hθ,
    ← Complex.exp_neg, neg_mul]

/-- Character orthogonality on `𝔽ₚ^L`: the sum of `ψ⟨ξ, w⟩` over `ξ` is `p^L` for `w = 0` and
vanishes otherwise. -/
theorem sum_stdAddChar_dotProduct {p L : ℕ} [Fact p.Prime] (w : Fin L → ZMod p) :
    ∑ ξ : Fin L → ZMod p, ZMod.stdAddChar (ξ ⬝ᵥ w) = if w = 0 then (p : ℂ) ^ L else 0 := by
  classical
  have hchar : ∀ ξ : Fin L → ZMod p,
      ZMod.stdAddChar (ξ ⬝ᵥ w) = ∏ i, ZMod.stdAddChar (ξ i * w i) :=
    fun ξ => addChar_map_sum_eq_prod _ _ _
  have hone : ∀ i, ∑ a : ZMod p, ZMod.stdAddChar (a * w i) = if w i = 0 then (p : ℂ) else 0 := by
    intro i
    rw [AddChar.sum_mulShift (w i) (ZMod.isPrimitive_stdAddChar p)]
    simp [ZMod.card, apply_ite (Nat.cast : ℕ → ℂ)]
  have hprod : ∑ ξ ∈ Fintype.piFinset fun _ : Fin L => (Finset.univ : Finset (ZMod p)),
      ∏ i, ZMod.stdAddChar (ξ i * w i) = ∏ i, ∑ a : ZMod p, ZMod.stdAddChar (a * w i) :=
    (Finset.prod_univ_sum (fun _ : Fin L => (Finset.univ : Finset (ZMod p)))
      fun (i : Fin L) (a : ZMod p) => ZMod.stdAddChar (a * w i)).symm
  rw [Finset.sum_congr rfl fun ξ _ => hchar ξ,
    ← Fintype.piFinset_univ (α := Fin L) (β := fun _ => ZMod p), hprod,
    Finset.prod_congr rfl fun i _ => hone i]
  by_cases hw : w = 0
  · simp [hw]
  · rw [ite_eq_right hw]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (by simpa using hi))

/-- **Fourier–Hölder point bound.** If among the coefficient vectors `v_j ∈ 𝔽ₚ^L` there are `K`
pairwise disjoint groups, each indexing a basis of `𝔽ₚ^L`, then a sum `∑ ε_j v_j` with independent
uniform sign coefficients takes any prescribed value with probability at most `Θ_K(p)^L`. -/
@[browning_sawin "lem_fourier"]
theorem signMeasure_sign_sum_le_theta_pow {p L K : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hK : 0 < K) {v : ι → Fin L → ZMod p} {b : Fin K → Fin L → ι}
    (hbinj : Function.Injective fun q : Fin K × Fin L => b q.1 q.2)
    (hbasis : ∀ h : Fin K, LinearIndependent (ZMod p) fun ℓ => v (b h ℓ))
    (u : Fin L → ZMod p) :
    signMeasure ι {ε | ∑ j, (ε j : ℤ) • v j = u} ≤ ENNReal.ofReal (theta p K ^ L) := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out (p := p.Prime)).pos
  set S : Finset (ι → ℤˣ) := Finset.univ.filter fun ε => ∑ j, (ε j : ℤ) • v j = u with hS
  have hset : {ε : ι → ℤˣ | ∑ j, (ε j : ℤ) • v j = u} = ↑S := by
    rw [hS]; ext ε; simp
  set C : (Fin L → ZMod p) → ι → ℝ := fun ξ j => Real.cos (2 * π * (ξ ⬝ᵥ v j).val / p) with hC
  set G : ZMod p → ℝ := fun a => |Real.cos (2 * π * a.val / p)| ^ K with hG
  have habs1 : ∀ ξ j, |C ξ j| ≤ 1 := fun ξ j => by
    simp only [hC]; exact Real.abs_cos_le_one _
  have hGsum : ∑ a : ZMod p, G a = p * theta p K := by
    rw [theta, hG]
    field_simp
  have hdot : ∀ (ξ : Fin L → ZMod p) (ε : ι → ℤˣ),
      ξ ⬝ᵥ (∑ j, (ε j : ℤ) • v j) = ∑ j, (ε j : ℤ) • (ξ ⬝ᵥ v j) := by
    intro ξ ε
    simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.smul_sum.symm
  have hsign : ∀ w : ℤˣ → ℂ, ∑ s : ℤˣ, w s = w 1 + w (-1) := by
    intro w
    rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from by decide]
    simp
  have hinner : ∀ ξ : Fin L → ZMod p,
      ∑ ε : ι → ℤˣ, ZMod.stdAddChar (ξ ⬝ᵥ ((∑ j, (ε j : ℤ) • v j) - u))
        = ZMod.stdAddChar (-(ξ ⬝ᵥ u)) * ∏ j, (2 * (C ξ j : ℂ)) := by
    intro ξ
    have h1 : ∀ ε : ι → ℤˣ, ZMod.stdAddChar (ξ ⬝ᵥ ((∑ j, (ε j : ℤ) • v j) - u))
        = ZMod.stdAddChar (-(ξ ⬝ᵥ u)) * ∏ j, ZMod.stdAddChar ((ε j : ℤ) • (ξ ⬝ᵥ v j)) := fun ε => by
      rw [dotProduct_sub, hdot, sub_eq_add_neg, AddChar.map_add_eq_mul,
        addChar_map_sum_eq_prod, mul_comm]
    have hpi : ∑ ε ∈ Fintype.piFinset fun _ : ι => (Finset.univ : Finset ℤˣ),
        ∏ j, ZMod.stdAddChar ((ε j : ℤ) • (ξ ⬝ᵥ v j))
        = ∏ j, ∑ s : ℤˣ, ZMod.stdAddChar ((s : ℤ) • (ξ ⬝ᵥ v j)) :=
      (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset ℤˣ))
        fun (j : ι) (s : ℤˣ) => ZMod.stdAddChar ((s : ℤ) • (ξ ⬝ᵥ v j))).symm
    rw [Finset.sum_congr rfl fun ε _ => h1 ε, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.piFinset_univ (α := ι) (β := fun _ => ℤˣ), hpi]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hsign fun s : ℤˣ => ZMod.stdAddChar ((s : ℤ) • (ξ ⬝ᵥ v j))]
    simpa [hC] using stdAddChar_add_stdAddChar_neg (ξ ⬝ᵥ v j)
  have hdouble : ∑ ε : ι → ℤˣ, ∑ ξ : Fin L → ZMod p,
      ZMod.stdAddChar (ξ ⬝ᵥ ((∑ j, (ε j : ℤ) • v j) - u)) = (S.card : ℂ) * (p : ℂ) ^ L := by
    have h1 : ∀ ε : ι → ℤˣ,
        (if (∑ j, (ε j : ℤ) • v j) - u = 0 then (p : ℂ) ^ L else 0)
          = if ε ∈ S then (p : ℂ) ^ L else 0 := by
      intro ε
      by_cases hε : ε ∈ S
      · rw [ite_eq_left hε, ite_eq_left (by simpa [hS, sub_eq_zero] using hε)]
      · rw [ite_eq_right hε, ite_eq_right (by simpa [hS, sub_eq_zero] using hε)]
    rw [Finset.sum_congr rfl fun ε _ => sum_stdAddChar_dotProduct _,
      Finset.sum_congr rfl fun ε _ => h1 ε, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
  have hnorm : (S.card : ℝ) * (p : ℝ) ^ L
      ≤ 2 ^ Fintype.card ι * ∑ ξ : Fin L → ZMod p, ∏ j, |C ξ j| := by
    have hkey : (S.card : ℂ) * (p : ℂ) ^ L
        = ∑ ξ : Fin L → ZMod p, ZMod.stdAddChar (-(ξ ⬝ᵥ u)) * ∏ j, (2 * (C ξ j : ℂ)) := by
      rw [← hdouble, Finset.sum_comm]
      exact Finset.sum_congr rfl fun ξ _ => hinner ξ
    calc (S.card : ℝ) * (p : ℝ) ^ L = ‖(S.card : ℂ) * (p : ℂ) ^ L‖ := by simp
      _ = ‖∑ ξ : Fin L → ZMod p, ZMod.stdAddChar (-(ξ ⬝ᵥ u)) * ∏ j, (2 * (C ξ j : ℂ))‖ := by
          rw [hkey]
      _ ≤ ∑ ξ : Fin L → ZMod p, ‖ZMod.stdAddChar (-(ξ ⬝ᵥ u)) * ∏ j, (2 * (C ξ j : ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ ξ : Fin L → ZMod p, ∏ j, (2 * |C ξ j|) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [norm_mul, AddChar.norm_apply, one_mul, norm_prod]
          exact Finset.prod_congr rfl fun j _ => by rw [norm_mul]; simp
      _ = 2 ^ Fintype.card ι * ∑ ξ : Fin L → ZMod p, ∏ j, |C ξ j| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ξ _ => by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have hdrop : ∀ ξ : Fin L → ZMod p, ∏ j, |C ξ j| ≤ ∏ h : Fin K, ∏ ℓ, |C ξ (b h ℓ)| := by
    intro ξ
    calc ∏ j, |C ξ j|
        ≤ ∏ j ∈ Finset.univ.image fun q : Fin K × Fin L => b q.1 q.2, |C ξ j| :=
          Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _)
            (fun i _ => abs_nonneg _) (fun i _ _ => habs1 ξ i)
      _ = ∏ q : Fin K × Fin L, |C ξ (b q.1 q.2)| :=
          Finset.prod_image fun x _ y _ hxy => hbinj hxy
      _ = ∏ h : Fin K, ∏ ℓ, |C ξ (b h ℓ)| := Fintype.prod_prod_type _
  have hFnn : ∀ (ξ : Fin L → ZMod p) (h : Fin K), 0 ≤ ∏ ℓ, |C ξ (b h ℓ)| :=
    fun ξ h => Finset.prod_nonneg fun ℓ _ => abs_nonneg _
  have hamgm : ∀ ξ : Fin L → ZMod p,
      ∏ h : Fin K, ∏ ℓ, |C ξ (b h ℓ)| ≤ (∑ h : Fin K, (∏ ℓ, |C ξ (b h ℓ)|) ^ K) / K := by
    intro ξ
    have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 hK
    have hw : ∑ _h : Fin K, ((K : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have h1 := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ : Fin K => ((K : ℝ))⁻¹)
      (fun h => (∏ ℓ, |C ξ (b h ℓ)|) ^ K) (fun _ _ => by positivity) hw
      (fun h _ => pow_nonneg (hFnn ξ h) K)
    calc ∏ h : Fin K, ∏ ℓ, |C ξ (b h ℓ)|
        = ∏ h : Fin K, ((∏ ℓ, |C ξ (b h ℓ)|) ^ K) ^ ((K : ℝ))⁻¹ :=
          Finset.prod_congr rfl fun h _ =>
            (Real.pow_rpow_inv_natCast (hFnn ξ h) hK.ne').symm
      _ ≤ ∑ h : Fin K, ((K : ℝ))⁻¹ * (∏ ℓ, |C ξ (b h ℓ)|) ^ K := h1
      _ = (∑ h : Fin K, (∏ ℓ, |C ξ (b h ℓ)|) ^ K) / K := by
          rw [← Finset.mul_sum]; ring
  have hgroup : ∀ h : Fin K,
      ∑ ξ : Fin L → ZMod p, (∏ ℓ, |C ξ (b h ℓ)|) ^ K = ((p : ℝ) * theta p K) ^ L := by
    intro h
    have hmat : IsUnit (Matrix.of fun ℓ i => v (b h ℓ) i : Matrix (Fin L) (Fin L) (ZMod p)) := by
      rw [← Matrix.linearIndependent_rows_iff_isUnit]
      exact hbasis h
    have hTinj : Function.Injective fun (ξ : Fin L → ZMod p) ℓ => ξ ⬝ᵥ v (b h ℓ) := by
      intro ξ ξ' hξ
      refine Matrix.mulVec_injective_iff_isUnit.2 hmat ?_
      funext ℓ
      simpa [Matrix.mulVec, dotProduct_comm] using congrFun hξ ℓ
    calc ∑ ξ : Fin L → ZMod p, (∏ ℓ, |C ξ (b h ℓ)|) ^ K
        = ∑ ξ : Fin L → ZMod p, ∏ ℓ, G (ξ ⬝ᵥ v (b h ℓ)) := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [← Finset.prod_pow]
      _ = ∑ η : Fin L → ZMod p, ∏ ℓ, G (η ℓ) :=
          Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hTinj) _ _ fun ξ => rfl
      _ = ∏ _ℓ : Fin L, ∑ a : ZMod p, G a := by
          rw [Finset.prod_univ_sum (fun _ : Fin L => (Finset.univ : Finset (ZMod p)))
            fun (_ : Fin L) (a : ZMod p) => G a, Fintype.piFinset_univ]
      _ = ((p : ℝ) * theta p K) ^ L := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hGsum]
  have hthetann : 0 ≤ theta p K :=
    div_nonneg (Finset.sum_nonneg fun a _ => pow_nonneg (abs_nonneg _) K) hp0.le
  have hSbound : (S.card : ℝ) ≤ 2 ^ Fintype.card ι * theta p K ^ L := by
    have h1 : ∑ ξ : Fin L → ZMod p, ∏ j, |C ξ j| ≤ ((p : ℝ) * theta p K) ^ L := by
      calc ∑ ξ : Fin L → ZMod p, ∏ j, |C ξ j|
          ≤ ∑ ξ : Fin L → ZMod p, (∑ h : Fin K, (∏ ℓ, |C ξ (b h ℓ)|) ^ K) / K :=
            Finset.sum_le_sum fun ξ _ => le_trans (hdrop ξ) (hamgm ξ)
        _ = (∑ h : Fin K, ∑ ξ : Fin L → ZMod p, (∏ ℓ, |C ξ (b h ℓ)|) ^ K) / K := by
            rw [← Finset.sum_div, Finset.sum_comm]
        _ = ((p : ℝ) * theta p K) ^ L := by
            rw [Finset.sum_congr rfl fun h _ => hgroup h, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            field_simp
    have h2 : (S.card : ℝ) * (p : ℝ) ^ L ≤ 2 ^ Fintype.card ι * ((p : ℝ) * theta p K) ^ L :=
      le_trans hnorm (mul_le_mul_of_nonneg_left h1 (by positivity))
    refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < (p : ℝ) ^ L by positivity)
    calc (S.card : ℝ) * (p : ℝ) ^ L ≤ 2 ^ Fintype.card ι * ((p : ℝ) * theta p K) ^ L := h2
      _ = 2 ^ Fintype.card ι * theta p K ^ L * (p : ℝ) ^ L := by rw [mul_pow]; ring
  rw [hset, signMeasure_coe_finset]
  calc (S.card : ℝ≥0∞) / 2 ^ Fintype.card ι
      = ENNReal.ofReal ((S.card : ℝ) / 2 ^ Fintype.card ι) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_pow (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (theta p K ^ L) :=
        ENNReal.ofReal_le_ofReal (by
          rw [div_le_iff₀ (show (0 : ℝ) < 2 ^ Fintype.card ι by positivity)]
          linarith [hSbound])

end BrowningSawin
