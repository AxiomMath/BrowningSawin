/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import BrowningSawin.Attr
public import BrowningSawin.External
public import BrowningSawin.Cited
public import BrowningSawin.Defs.Definitions
public import BrowningSawin.Notation
public import BrowningSawin.ConcentrationOfSignSums
public import BrowningSawin.ReductionModuloAPrime
public import BrowningSawin.SingularityAtAPrescribedClosedPoint
public import BrowningSawin.ClosedPointsOfLargeDegree

/-!
# The finite-field estimate

This file bounds `σ_{n,d}(p)`, the probability that the reduction modulo `p` of the random sign
form is singular, by splitting the singular closed points of `ℙⁿ_{𝔽ₚ}` according to their degree.

## Main results

* `sigma_le`: for `0 ≤ R ≤ ⌊(d+1)/(n+1)⌋`,
  `σ_{n,d}(p) ≤ (p/(p-1)) ∑_{e=1}^R (p^{ne}/e) Θ_{K_e}(p)^{(n+1)e}
     + (n+1) {(∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}}`.
* `signMeasure_exists_affineClosedPoint_mem_affineSingularLocus_le`: the affine large-degree bound
  `P(∃ closed point P of 𝔸ⁿ_{𝔽ₚ}, deg P > R, singular on g = 0)
     ≤ (∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}`.
* `signMeasure_pow_aeval_blockH_le`: at a closed point `P` of degree `e` a prescribed value of
  `H(P)^p` has probability at most `2^{-min(t+1,e)}`, the counterpart for the block `H` of
  `signMeasure_pow_restrictToFunctionField_blockG_le`.
* `finite_of_affineDim_le_zero` and `ncard_le_delta_of_affineDim_le_zero`: an affine algebraic
  set of dimension at most `0` over an algebraically closed field is finite with at most `δ`
  points, because the map sending a point to the maximal ideal of functions vanishing there is an
  injection into the minimal primes of its vanishing ideal.
-/

@[expose] public section

namespace BrowningSawin

open MvPolynomial MeasureTheory
open scoped ENNReal

universe u

/-! ## Algebraic sets of dimension zero

An affine algebraic set of dimension at most `0` is finite, and its points are counted by the
minimal primes of its vanishing ideal: distinct points give distinct maximal ideals, and a maximal
ideal over `I(V)` that were not minimal over it would exhibit a chain of primes of length one,
contradicting `dim V ≤ 0`. -/

section DimensionZero

/-- **A prime over an ideal whose quotient has Krull dimension zero is maximal among primes.**
A strict inclusion of primes over `I` is a chain of length one in `Spec (R ⧸ I)`. -/
theorem eq_of_le_of_ringKrullDim_quotient_le_zero {R : Type*} [CommRing R] {I : Ideal R}
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

variable {K : Type u} [Field K] {n : ℕ}

/-- Distinct points have distinct maximal ideals: the coordinate functions `y_i - a_i` vanish at
`a` alone. -/
theorem injective_ker_eval :
    Function.Injective fun a : Fin n → K => RingHom.ker (eval a) := by
  intro a a' h
  have h' : RingHom.ker (eval (R := K) (σ := Fin n) a)
      = RingHom.ker (eval (R := K) (σ := Fin n) a') := h
  funext i
  have hmem : X i - C (a i) ∈ RingHom.ker (eval (R := K) (σ := Fin n) a) := by
    rw [RingHom.mem_ker]; simp
  rw [h', RingHom.mem_ker] at hmem
  simp only [map_sub, eval_X, eval_C, sub_eq_zero] at hmem
  exact hmem.symm

/-- At a point of an algebraic set of dimension at most `0`, the maximal ideal of functions
vanishing there is a minimal prime of the vanishing ideal of the set. -/
theorem ker_eval_mem_minimalPrimes_of_affineDim_le_zero {V : Set (Fin n → K)}
    (hdim : affineDim V ≤ 0) {a : Fin n → K} (ha : a ∈ V) :
    RingHom.ker (eval a) ∈ (affineVanishingIdeal V).minimalPrimes := by
  have hmax : (RingHom.ker (eval (R := K) (σ := Fin n) a)).IsMaximal := isMaximal_ker_eval a
  have hIle : affineVanishingIdeal V ≤ RingHom.ker (eval a) := fun F hF =>
    RingHom.mem_ker.2 (mem_affineVanishingIdeal.1 hF a ha)
  have hdim' : ringKrullDim (MvPolynomial (Fin n) K ⧸ affineVanishingIdeal V)
      ≤ ((0 : ℕ∞) : WithBot ℕ∞) := affineDim_le_iff.1 (by simpa using hdim)
  refine ⟨⟨hmax.isPrime, hIle⟩, fun Q hQ hQle => ?_⟩
  exact le_of_eq (eq_of_le_of_ringKrullDim_quotient_le_zero (by simpa using hdim') hQ.1 hmax.isPrime
    hQ.2 hQle).symm

/-- **An affine algebraic set of dimension at most `0` is finite.** -/
theorem finite_of_affineDim_le_zero {V : Set (Fin n → K)} (hdim : affineDim V ≤ 0) : V.Finite := by
  refine Set.Finite.of_finite_image (f := fun a : Fin n → K => RingHom.ker (eval a)) ?_
    (injective_ker_eval.injOn)
  refine Set.Finite.subset
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (affineVanishingIdeal V)) ?_
  rintro I ⟨a, ha, rfl⟩
  exact ker_eval_mem_minimalPrimes_of_affineDim_le_zero hdim ha

/-- **An affine algebraic set of dimension at most `0` has at most `δ` points.** -/
theorem ncard_le_delta_of_affineDim_le_zero (hhs : HilbertSerre.{u}) [IsAlgClosed K]
    {V : Set (Fin n → K)} (hdim : affineDim V ≤ 0) : V.ncard ≤ delta V := by
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun a => RingHom.ker (eval a))
    (fun a ha => ker_eval_mem_minimalPrimes_of_affineDim_le_zero hdim ha)
    injective_ker_eval.injOn (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)) ?_
  exact ncard_minimalPrimes_le_delta hhs V

end DimensionZero

/-! ## Independent monomials of bounded degree at a closed point

The block `H` is the sign sum of the monomials `y^β` with `|β| ≤ t`. To bound the probability that
it takes a prescribed value at a closed point `P` of degree `e`, the rank bound
`signMeasure_sign_sum_le_inv_two_pow` needs `min (t+1, e)` of those monomials to have `𝔽ₚ`-linearly
independent values at `P`. Their values span the degree filtration `V_t` of `κ(P)`, whose dimension
`min_le_finrank_degreeFiltration` bounds below by `min (t+1, e)`; a spanning family contains a
linearly independent subfamily of that size, and the residue field embeds in `𝔽̄ₚ` along a
geometric point above `P`, which carries the independence over to the values at that point. -/

section IndependentMonomials

variable {k K : Type*} [Field k] {m : ℕ}

/-- Evaluating the reduction of `f` at a point of a `k`-algebra is `aeval`. -/
theorem aeval_eq_eval_map [CommRing K] [Algebra k K] (a : Fin m → K)
    (f : MvPolynomial (Fin m) k) : aeval a f = eval a (f.map (algebraMap k K)) := by
  rw [aeval_def, eval₂_eq_eval_map]

variable {p n : ℕ} [Fact p.Prime]

/-- **Independent monomials of bounded degree at a closed point.** Let `Q` be a closed point of
`𝔸ⁿ_{𝔽ₚ}` and `a` a geometric point above it. Then among the monomials `y^β` with `|β| ≤ s` there
are `min (s+1) (deg Q)` whose values at `a` are `𝔽ₚ`-linearly independent. -/
theorem exists_finset_linearIndependent_aeval_monomial
    {Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p))}
    {a : Fin n → AlgebraicClosure (ZMod p)}
    (ha : ∀ f ∈ Q.asIdeal, eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0)
    (s : ℕ) :
    ∃ J : Finset (Fin n →₀ ℕ), (∀ β ∈ J, β.degree ≤ s) ∧
      min (s + 1) (pointDegree (ZMod p) Q) ≤ J.card ∧
      LinearIndependent (ZMod p) fun β : J =>
        aeval a (monomial (β : Fin n →₀ ℕ) 1 : MvPolynomial (Fin n) (ZMod p)) := by
  classical
  have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
  let : Field (residueFieldAt Q) := Ideal.Quotient.field _
  have : Module.Finite (ZMod p) (residueFieldAt Q) := module_finite_residueFieldAt Q
  set ψ : residueFieldAt Q →ₐ[ZMod p] AlgebraicClosure (ZMod p) :=
    Ideal.Quotient.liftₐ Q.asIdeal (aeval a)
      (fun f hf => by rw [aeval_eq_eval_map]; exact ha f hf) with hψdef
  have hψmk : ∀ f, ψ (evalAt Q f) = aeval a f := fun f => rfl
  have hψinj : Function.Injective ψ :=
    (ψ : residueFieldAt Q →+* AlgebraicClosure (ZMod p)).injective
  set y : Fin n → residueFieldAt Q := fun i => evalAt Q (X i) with hy
  set w : (Fin n →₀ ℕ) → residueFieldAt Q := fun β => evalAt Q (monomial β 1) with hw
  have hwprod : ∀ β : Fin n →₀ ℕ, w β = ∏ i, y i ^ β i := fun β => mk_monomial_eq_prod _ β
  set T : Set (Fin n →₀ ℕ) := {β | β.degree ≤ s} with hT
  have hTfin : T.Finite := by
    refine Set.Finite.subset (monomialsLE n s).finite_toSet fun β hβ => ?_
    exact mem_monomialsLE.2 hβ
  have hspanT : degreeFiltration (ZMod p) y s = Submodule.span (ZMod p) (w '' T) := by
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
    exists_linearIndepOn_extension (K := ZMod p) (v := w) (linearIndepOn_empty (ZMod p) w)
      (Set.empty_subset T)
  have hbfin : b.Finite := hTfin.subset hbT
  have : Fintype ↥b := hbfin.fintype
  have hspanb : Submodule.span (ZMod p) (w '' b) = degreeFiltration (ZMod p) y s := by
    refine le_antisymm ?_ ?_
    · rw [hspanT]
      exact Submodule.span_mono (Set.image_mono hbT)
    · rw [hspanT]
      exact Submodule.span_le.2 hbspan
  have hrange : Set.range (fun x : ↥b => w x) = w '' b := by
    rw [Set.image_eq_range]
  have hcard : Module.finrank (ZMod p) (degreeFiltration (ZMod p) y s) = b.ncard := by
    rw [← hspanb, ← hrange, finrank_span_eq_card hbli, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
  have hmin : min (s + 1) (pointDegree (ZMod p) Q)
      ≤ Module.finrank (ZMod p) (degreeFiltration (ZMod p) y s) :=
    min_le_finrank_degreeFiltration (ZMod p) (adjoin_range_mk_X Q.asIdeal) s
  refine ⟨hbfin.toFinset, fun β hβ => hbT (hbfin.mem_toFinset.1 hβ), ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hbfin, ← hcard]
    exact hmin
  · have h9 : LinearIndependent (ZMod p) fun x : ↥b => ψ (w x) :=
      hbli.map' ψ.toLinearMap (LinearMap.ker_eq_bot_of_injective hψinj)
    refine (linearIndependent_equiv'
      (e := Equiv.subtypeEquivRight fun β => (hbfin.mem_toFinset (a := β)).symm)
      (f := fun β : hbfin.toFinset =>
        aeval a (monomial (β : Fin n →₀ ℕ) 1 : MvPolynomial (Fin n) (ZMod p)))
      (g := fun x : ↥b => ψ (w x)) (funext fun x => ?_)).1 h9
    simp only [hw, Function.comp_apply, hψmk, Equiv.subtypeEquivRight_apply_coe]

end IndependentMonomials

/-! ## A prescribed value of the block `H` at a closed point -/

section BlockH

variable {p n d : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- Dividing out `p` recovers `β` from the exponent tuple `pβ`. -/
theorem mapRange_div_nsmul (hp : 1 < p) (β : Fin n →₀ ℕ) :
    Finsupp.mapRange (· / p) (Nat.zero_div p) (p • β) = β :=
  Finsupp.ext fun j => by
    simp only [Finsupp.mapRange_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Nat.mul_div_cancel_left _ (by omega)

/-- **A prescribed value of `H` at a closed point is unlikely.** Let `Q` be a closed point of
`𝔸ⁿ_{𝔽ₚ}` of degree `e`, let `a` be a geometric point above it, and let `p` be odd. Then for every
`v` the value of the block `H` at `a` has `p`-th power `v` with probability at most
`2^{-min(t+1,e)}`, where `t = ⌊d/p⌋` is the length of that block.

At most one element of `𝔽̄ₚ` has `p`-th power `v` (`subsingleton_setOf_pow_eq`), so the event is
contained in the event that `H(a)` takes one prescribed value. That value is the sign sum
`∑_α ε_α W_α`, where `W_α` is the value of `y^β` at `a` when `α = pβ` and `0` otherwise;
`exists_finset_linearIndependent_aeval_monomial` makes `min (t+1,e)` of those values `𝔽ₚ`-linearly
independent, and `signMeasure_sign_sum_le_inv_two_pow` bounds the probability of a prescribed value
of such a sum. -/
theorem signMeasure_pow_aeval_blockH_le (hodd : Odd p)
    {Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p))}
    {a : Fin n → AlgebraicClosure (ZMod p)}
    (ha : ∀ f ∈ Q.asIdeal, eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0)
    (v : AlgebraicClosure (ZMod p)) :
    signMeasure ↥(monomialsLE n d) {ε | aeval a (blockH p n d ε) ^ p = v}
      ≤ ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (pointDegree (ZMod p) Q))⁻¹ := by
  classical
  have hp1 : 1 < p := (Fact.out (p := p.Prime)).one_lt
  set W : (Fin n →₀ ℕ) → AlgebraicClosure (ZMod p) := fun α =>
    if residueTuple p α = 0 then
      aeval a (monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) α) 1
        : MvPolynomial (Fin n) (ZMod p))
    else 0 with hW
  have hWzero : ∀ α : Fin n →₀ ℕ, residueTuple p α ≠ 0 → W α = 0 := fun α hα => by
    simp only [hW]; rw [ite_eq_right hα]
  have hWnsmul : ∀ β : Fin n →₀ ℕ,
      W (p • β) = aeval a (monomial β 1 : MvPolynomial (Fin n) (ZMod p)) := fun β => by
    simp only [hW]
    rw [ite_eq_left (residueTuple_nsmul β), mapRange_div_nsmul hp1]
  have hrep : ∀ ε : SignFamily (monomialsLE n d),
      aeval a (blockH p n d ε) = ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) := by
    intro ε
    have hzsmul : ∀ (β : Fin n →₀ ℕ) (z : ℤˣ),
        (monomial β (((z : ℤ) : ZMod p)) : MvPolynomial (Fin n) (ZMod p))
          = (z : ℤ) • monomial β 1 := fun β z => by
      rw [zsmul_eq_mul, ← map_intCast (C : ZMod p →+* MvPolynomial (Fin n) (ZMod p)) (z : ℤ),
        C_mul_monomial, mul_one]
    have hlhs : aeval a (blockH p n d ε)
        = ∑ β ∈ monomialsLE n (upperBlockLength p d),
            (signOf ε (p • β) : ℤ) • aeval a (monomial β 1 : MvPolynomial (Fin n) (ZMod p)) := by
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
            (signOf ε (p • β) : ℤ) • aeval a (monomial β 1 : MvPolynomial (Fin n) (ZMod p)) := by
      rw [filter_residueTuple_eq_zero, Finset.sum_image fun β _ γ _ h =>
        nsmul_left_injective (Fact.out (p := p.Prime)).ne_zero h]
      exact Finset.sum_congr rfl fun β _ => by rw [hWnsmul]
    rw [hlhs, hrhs, hsplit, himage]
  obtain ⟨J₀, hJ₀deg, hJ₀card, hJ₀li⟩ :=
    exists_finset_linearIndependent_aeval_monomial ha (upperBlockLength p d)
  have hmem : ∀ β : Fin n →₀ ℕ, β.degree ≤ upperBlockLength p d → p • β ∈ monomialsLE n d := by
    intro β hβ
    have hpt : p * upperBlockLength p d ≤ d := by
      rw [upperBlockLength, mul_comm]; exact Nat.div_mul_le_self _ _
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
      (g := fun β : ↥J₀ =>
        aeval a (monomial (β : Fin n →₀ ℕ) 1 : MvPolynomial (Fin n) (ZMod p)))
      (funext fun β => ?_)).1 hJ₀li
    exact hWnsmul _
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hp2 : p ≠ 2 := by rintro rfl; simp [Nat.odd_iff] at hodd
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by push_cast; ring, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p 2]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have : CharP (AlgebraicClosure (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective p
  have : ExpChar (AlgebraicClosure (ZMod p)) p := ExpChar.prime Fact.out
  have hfinal : signMeasure ↥(monomialsLE n d) {ε | aeval a (blockH p n d ε) ^ p = v}
      ≤ ((2 : ℝ≥0∞) ^ J.card)⁻¹ := by
    by_cases hex : ∃ c : AlgebraicClosure (ZMod p), c ^ p = v
    · obtain ⟨c, hc⟩ := hex
      have hsub : {ε : SignFamily (monomialsLE n d) | aeval a (blockH p n d ε) ^ p = v}
          ⊆ {ε | ∑ α : ↥(monomialsLE n d), (ε α : ℤ) • W (α : Fin n →₀ ℕ) = c} := by
        intro ε hε
        rw [Set.mem_ofPred_eq, ← hrep ε]
        exact subsingleton_setOf_pow_eq v hε hc
      exact le_trans (measure_mono hsub) (signMeasure_sign_sum_le_inv_two_pow (k := ZMod p)
        (V := AlgebraicClosure (ZMod p))
        (v := fun α : ↥(monomialsLE n d) => W (α : Fin n →₀ ℕ)) (J := J) h2 hJli c)
    · have hempty : {ε : SignFamily (monomialsLE n d) | aeval a (blockH p n d ε) ^ p = v} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun ε hε => hex ⟨_, hε⟩
      rw [hempty, measure_empty]
      exact zero_le
  refine le_trans hfinal (ENNReal.inv_le_inv.2 ?_)
  exact pow_le_pow_right₀ one_le_two (le_trans hJ₀card hJcard)

end BlockH

/-! ## The contribution of the closed points of large degree -/

section HighDegree

variable {p n d : ℕ} [Fact p.Prime]

/-- The critical loci are functions of the blocks `U, G_1, …, G_n` alone: two sign families
agreeing outside the block `H` have the same critical loci, because `∂ᵢ g = ∂ᵢ U + G_i^p`. -/
theorem criticalLocus_eq_of_agree_off_blockH (hd : 1 ≤ d) {ε ω : SignFamily (monomialsLE n d)}
    (h : ∀ α : ↥(monomialsLE n d), blockOf p n α.1 ≠ BlockIndex.h → ε α = ω α) (j : ℕ) :
    criticalLocus (affineSignPoly p n d ε) j = criticalLocus (affineSignPoly p n d ω) j := by
  have hp : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hU : blockU p n d ε = blockU p n d ω :=
    block_congr hp .u fun α hα => h α (by rw [hα]; exact fun hh => by cases hh)
  have key : ∀ i : Fin n,
      pderiv i (affineSignPoly p n d ε) = pderiv i (affineSignPoly p n d ω) := by
    intro i
    have hG : blockG p n d ε i = blockG p n d ω i :=
      block_congr hp (.g i) fun α hα => h α (by rw [hα]; exact fun hh => by cases hh)
    rw [pderiv_affineSignPoly hd, pderiv_affineSignPoly hd, hU, hG]
  ext a
  simp only [criticalLocus, Set.mem_ofPred_eq]
  exact forall_congr' fun i => forall_congr' fun _ => by rw [key i]

set_option maxHeartbeats 1000000 in
-- The conditioning lemma is applied with the points of `W_n` indexing the covering family, so the
-- elaborator carries the whole affine geometry of `W_n` through the union bound; that does not fit
-- the default budget.
/-- **Contribution of the closed points of large degree.** For every `R` the probability that the
hypersurface `g = 0` cut out by the affine sign polynomial is singular at some closed point of
`𝔸ⁿ_{𝔽ₚ}` of degree greater than `R` is at most
`(∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}`.

Exclude the event `dim W_n > 0`, whose probability `signMeasure_zero_lt_affineDim_criticalLocus_le`
bounds by the first term. On its complement `W_n` is finite with at most `D^n` points
(`finite_of_affineDim_le_zero`, `ncard_le_delta_of_affineDim_le_zero` and the affine Bézout bound
`delta_criticalLocus_le`), and a singular point lies in `W_n` and satisfies `g = 0` besides.
Condition on the blocks `U, G_1, …, G_n`, which determine `W_n`
(`criticalLocus_eq_of_agree_off_blockH`) and leave the signs of `H` independent and uniform: by
`affineSignPoly_eq_blockU_add_sum_add_blockH_pow` the remaining equation `g = 0` prescribes `H^p`
at the point, and `signMeasure_pow_aeval_blockH_le` bounds the probability of that by
`2^{-min(t+1,R+1)}` at a point of degree greater than `R`. A union bound over the at most `D^n`
points gives the second term. -/
theorem signMeasure_exists_affineClosedPoint_mem_affineSingularLocus_le
    (hbez : AffineBezout.{0}) (hdrop : DimensionDrop.{0})
    (hjac : AffineJacobianCriterion.{0}) (hhs : HilbertSerre.{0})
    (hodd : Odd p) (hn : 1 ≤ n) (hd : 3 ≤ d) (R : ℕ) :
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
        finite_of_affineDim_le_zero hdimω
      have hncard : hfin.toFinset.card ≤ pderivDegBound d ^ n := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact le_trans (ncard_le_delta_of_affineDim_le_zero hhs hdimω)
          (delta_criticalLocus_le hbez (by omega) (totalDegree_affineSignPoly_le ω) le_rfl)
      refine ⟨hfin.toFinset.filter fun a => ∃ Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p)),
        R < pointDegree (ZMod p) Q ∧ ∀ f ∈ Q.asIdeal,
          eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0,
        B, le_trans (Finset.card_filter_le _ _) hncard, fun a _ => hBmem a, fun a haS => ?_,
        fun ε hε hfib => ?_⟩
      · obtain ⟨Q, hQdeg, hQa⟩ := (Finset.mem_filter.1 haS).2
        refine le_trans (signMeasure_pow_aeval_blockH_le hodd hQa (c a))
          (ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two ?_))
        omega
      · obtain ⟨⟨Q, a, hQdeg, hQa, hsing⟩, hεdim⟩ := hε
        have hWeq : criticalLocus (affineSignPoly p n d ε) n
            = criticalLocus (affineSignPoly p n d ω) n :=
          criticalLocus_eq_of_agree_off_blockH hd1 (fun α hα => hfib α hα) n
        obtain ⟨hg0, hgi⟩ :=
          (mem_affineSingularLocus_iff hjac (affineSignPoly_ne_zero ε) a).1 hsing
        have haW : a ∈ criticalLocus (affineSignPoly p n d ω) n := by
          rw [← hWeq]
          exact fun i _ => hgi i
        refine ⟨a, Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 haW, ⟨Q, hQdeg, hQa⟩⟩, ?_⟩
        have hU : blockU p n d ε = blockU p n d ω :=
          block_congr hp .u fun α hα => hfib α (by rw [hα]; exact fun hh => by cases hh)
        have hG : ∀ i, blockG p n d ε i = blockG p n d ω i := fun i =>
          block_congr hp (.g i) fun α hα => hfib α (by rw [hα]; exact fun hh => by cases hh)
        have haeval : aeval a (affineSignPoly p n d ε) = 0 := by
          rw [aeval_eq_eval_map]; exact hg0
        rw [affineSignPoly_eq_blockU_add_sum_add_blockH_pow hd1, map_add, map_add, map_sum,
          map_pow, hU] at haeval
        rw [hB, Set.mem_ofPred_eq, hc, eq_neg_iff_add_eq_zero, add_comm]
        rw [← haeval]
        refine congrArg₂ _ (congrArg₂ _ rfl (Finset.sum_congr rfl fun i _ => ?_)) rfl
        rw [map_mul, aeval_X, map_pow, hG i]
    · refine ⟨∅, B, by simp, fun a _ => hBmem a, by simp, fun ε hε hfib => ?_⟩
      have hWeq : criticalLocus (affineSignPoly p n d ε) n
          = criticalLocus (affineSignPoly p n d ω) n :=
        criticalLocus_eq_of_agree_off_blockH hd1 (fun α hα => hfib α hα) n
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

end HighDegree

/-! ## The finite-field estimate -/

section Finite

variable {p n d : ℕ} [Fact p.Prime]

/-- **Every geometric point of `ℙⁿ` lies in a closed point.** The Frobenius orbit of a point of
`ℙⁿ(𝔽̄ₚ)` is finite, so its length is a positive integer — the degree of the closed point
containing it. Normalizing a nonvanishing homogeneous coordinate to `1`, the remaining coordinates
generate a finite subfield `𝔽_{p^m}` of `𝔽̄ₚ` — finite because `𝔽̄ₚ/𝔽ₚ` is algebraic and the
subalgebra is generated by finitely many elements — and every element of it satisfies
`x^{p^m} = x`, so the point is fixed by the `p^m`-power map. -/
theorem zero_lt_minimalPeriod_projPowMap (P : ProjPoint p n) :
    0 < Function.minimalPeriod (projPowMap p) P := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), P.rep i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact P.rep_nonzero (funext hcon)
  set v : Fin (n + 1) → AlgebraicClosure (ZMod p) := (P.rep i)⁻¹ • P.rep with hvdef
  have hvi : v i = 1 := inv_mul_cancel₀ hi
  have hv0 : v ≠ 0 := fun h => one_ne_zero (hvi ▸ congrFun h i)
  have hmkv : Projectivization.mk (AlgebraicClosure (ZMod p)) v hv0 = P := by
    rw [← Projectivization.mk_rep P]
    refine (Projectivization.mk_eq_mk_iff (AlgebraicClosure (ZMod p)) _ _ _ _).2
      ⟨Units.mk0 _ (inv_ne_zero hi), ?_⟩
    exact funext fun l => rfl
  set A := Algebra.adjoin (ZMod p) (Set.range v) with hAdef
  have : Module.Finite (ZMod p) A :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range v)
      fun x _ => Algebra.IsIntegral.isIntegral x
  have : Finite A := Module.finite_of_finite (ZMod p)
  have hAfield : IsField A := Finite.isField_of_domain A
  let : Field A := hAfield.toField
  have : Fintype A := Fintype.ofFinite A
  set m := Module.finrank (ZMod p) A with hm
  have hcard : Fintype.card A = p ^ m := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := A), ZMod.card]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (Fintype.card_le_one_iff_subsingleton.1 (by rw [hcard, h0, pow_zero]))
        (not_subsingleton A)
    · exact h0
  have h3 : Function.IsPeriodicPt (projPowMap p) m P := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, iterate_projPowMap, ← hmkv]
    refine (projPowMap_mk_eq_self_iff hv0 hvi).2 fun l => ?_
    have hmem : v l ∈ A := Algebra.subset_adjoin ⟨l, rfl⟩
    have h1 : (⟨v l, hmem⟩ : A) ^ p ^ m = ⟨v l, hmem⟩ := by
      rw [← hcard]; exact FiniteField.pow_card _
    simpa using congrArg (fun x : A => (x : AlgebraicClosure (ZMod p))) h1
  exact h3.minimalPeriod_pos hm0

/-- **The large-degree contribution on one standard chart.** The probability that `X_{f̄}` is
singular at some closed point of `ℙⁿ_{𝔽ₚ}` of degree greater than `R` lying on the chart `x_i ≠ 0`
and not the `i`-th coordinate vertex is at most `(∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}`.

By `exists_measurePreserving_dehomogenize_map_signForm` the dehomogenization of `f̄` on that chart
has the distribution of the affine sign polynomial, the identity in distribution being the
measure-preserving reindexing of the signs along `chartTupleEquiv`; and
`exists_affineClosedPoint_of_projPoint` presents the point as a closed point of `𝔸ⁿ_{𝔽ₚ}` of the
same degree, singular on `g = 0` because dehomogenizing only rescales the values of `f̄` and its
derivatives at the normalized representative. -/
theorem signMeasure_exists_projClosedPoint_gt_le (hbez : AffineBezout.{0})
    (hdrop : DimensionDrop.{0}) (hjac : AffineJacobianCriterion.{0}) (hhs : HilbertSerre.{0})
    (hodd : Odd p) (hn : 1 ≤ n) (hd : 3 ≤ d) (R : ℕ)
    (i : Fin (n + 1)) :
    signMeasure ↥(monomialsEq (n + 1) d)
        {ε | ∃ P : ProjPoint p n, R < Function.minimalPeriod (projPowMap p) P ∧ P.rep i ≠ 0 ∧
          (∃ j, j ≠ i ∧ P.rep j ≠ 0) ∧
          P ∈ singularLocus ((signForm n d ε).map (Int.castRingHom (ZMod p)))}
      ≤ (∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
            * ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹
        + (pderivDegBound d : ℝ≥0∞) ^ n
            * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹ := by
  classical
  set Φ := (chartTupleEquiv d i).arrowCongr (Equiv.refl ℤˣ) with hΦdef
  have hΦ : MeasurePreserving Φ (signMeasure ↥(monomialsEq (n + 1) d))
      (signMeasure ↥(monomialsLE n d)) := measurePreserving_signFamilyCongr _
  have hsub : {ε : SignFamily (monomialsEq (n + 1) d) |
        ∃ P : ProjPoint p n, R < Function.minimalPeriod (projPowMap p) P ∧ P.rep i ≠ 0 ∧
          (∃ j, j ≠ i ∧ P.rep j ≠ 0) ∧
          P ∈ singularLocus ((signForm n d ε).map (Int.castRingHom (ZMod p)))}
      ⊆ Φ ⁻¹' {δ : SignFamily (monomialsLE n d) |
        ∃ (Q : MaximalSpectrum (MvPolynomial (Fin n) (ZMod p)))
          (a : Fin n → AlgebraicClosure (ZMod p)),
        R < pointDegree (ZMod p) Q ∧
        (∀ f ∈ Q.asIdeal,
          eval a (f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0) ∧
        a ∈ affineSingularLocus (affineSignPoly p n d δ)} := by
    rintro ε ⟨P, hPR, hi, ⟨j, hj, hjne⟩, hP⟩
    obtain ⟨a, Q, i₀, hins, hdeg, hi₀, ha⟩ :=
      exists_affineClosedPoint_of_projPoint (e := Function.minimalPeriod (projPowMap p) P) rfl
        (by omega) hi hj hjne
    rw [mem_singularLocus_iff hjac (map_signForm_ne_zero ε)] at hP
    have hhom : ((signForm n d ε).map (Int.castRingHom (ZMod p))).IsHomogeneous d := by
      refine IsHomogeneous.map ?_ _
      rw [signForm]
      refine (mem_homogeneousSubmodule _ _).1 (Submodule.sum_mem _ fun α hα => ?_)
      exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (mem_monomialsEq.1 hα))
    have hscale : ∀ (mm : ℕ) (G : MvPolynomial (Fin (n + 1)) (ZMod p)), G.IsHomogeneous mm →
        eval P.rep (toClosure G) = 0 →
        eval (Fin.insertNth i 1 a)
          (G.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) = 0 := by
      intro mm G hG h
      rw [hins, eval_smul_of_isHomogeneous
        (hG.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))]
      rw [toClosure] at h
      rw [h, mul_zero]
    have hgne : dehomogenize (ZMod p) i ((signForm n d ε).map (Int.castRingHom (ZMod p))) ≠ 0 := by
      rw [dehomogenize_map_signForm i ε]
      exact affineSignPoly_ne_zero _
    have hmem : a ∈ affineSingularLocus
        (dehomogenize (ZMod p) i ((signForm n d ε).map (Int.castRingHom (ZMod p)))) := by
      rw [mem_affineSingularLocus_iff hjac hgne]
      refine ⟨?_, fun j' => ?_⟩
      · rw [eval_map_dehomogenize]
        exact hscale d _ hhom hP.1
      · rw [← dehomogenize_pderiv, eval_map_dehomogenize]
        exact hscale (d - 1) _ hhom.pderiv (hP.2 _)
    rw [Set.mem_preimage, Set.mem_ofPred_eq, ← dehomogenize_map_signForm i ε]
    exact ⟨Q, a, by omega, ha, hmem⟩
  refine le_trans (measure_mono hsub) ?_
  rw [hΦ.measure_preimage (MeasurableSet.of_discrete).nullMeasurableSet]
  exact signMeasure_exists_affineClosedPoint_mem_affineSingularLocus_le hbez hdrop hjac hhs
    hodd hn hd R

/-- **Singularity probability over a finite field.** For `0 ≤ R ≤ ⌊(d+1)/(n+1)⌋`,
`σ_{n,d}(p) ≤ (p/(p-1)) ∑_{e=1}^R (p^{ne}/e) Θ_{K_e}(p)^{(n+1)e}
  + (n+1) {(∑_{i<n} D^i) 2^{-(s+1)} + D^n 2^{-min(t+1,R+1)}}`.

If `f̄` is singular then `Sing X_{f̄}` contains a closed point `P` of `ℙⁿ_{𝔽ₚ}`: a geometric
singular point exists by definition, and it has finite Frobenius orbit by
`zero_lt_minimalPeriod_projPowMap`, since it is defined over a finite extension of `𝔽ₚ`. Its degree
is either at most `R`, and then `signMeasure_exists_closedPoint_mem_singularLocus_le` gives the
first sum, or greater than `R`. In the latter case `notMem_hypersurface_map_signForm` says `P` is
not a coordinate vertex, so it lies on at least one of the `n + 1` standard affine charts, where
`signMeasure_exists_projClosedPoint_gt_le` bounds its contribution; a union bound over the charts
costs the factor `n + 1`. Adding the two contributions, by a union bound over the two degree
ranges, gives the asserted inequality. -/
@[browning_sawin "thm_finite"]
theorem sigma_le (hbez : AffineBezout.{0}) (hdrop : DimensionDrop.{0})
    (hjac : AffineJacobianCriterion.{0}) (hhs : HilbertSerre.{0})
    (hodd : Odd p) (hn : 1 ≤ n) (hd : 3 ≤ d) {R : ℕ} (hR : R ≤ (d + 1) / (n + 1)) :
    sigma p n d
      ≤ ENNReal.ofReal ((p : ℝ) / (p - 1) * ∑ e ∈ Finset.Icc 1 R,
            (p : ℝ) ^ (n * e) / e * theta p (basisCount n d e) ^ ((n + 1) * e))
        + ((n : ℝ≥0∞) + 1) * ((∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
              * ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹
            + (pderivDegBound d : ℝ≥0∞) ^ n
              * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹) := by
  classical
  set Alow : Set (SignFamily (monomialsEq (n + 1) d)) :=
    {ε | ∃ P : ProjPoint p n, 1 ≤ Function.minimalPeriod (projPowMap p) P ∧
      Function.minimalPeriod (projPowMap p) P ≤ R ∧
      P ∈ singularLocus ((signForm n d ε).map (Int.castRingHom (ZMod p)))} with hAlow
  set Ahigh : Fin (n + 1) → Set (SignFamily (monomialsEq (n + 1) d)) := fun i =>
    {ε | ∃ P : ProjPoint p n, R < Function.minimalPeriod (projPowMap p) P ∧ P.rep i ≠ 0 ∧
      (∃ j, j ≠ i ∧ P.rep j ≠ 0) ∧
      P ∈ singularLocus ((signForm n d ε).map (Int.castRingHom (ZMod p)))} with hAhigh
  have hcover : {ε : SignFamily (monomialsEq (n + 1) d) |
        IsSingularForm ((signForm n d ε).map (Int.castRingHom (ZMod p)))}
      ⊆ Alow ∪ ⋃ i, Ahigh i := by
    intro ε hε
    obtain ⟨P, hP⟩ := hε
    have hmp : 0 < Function.minimalPeriod (projPowMap p) P := zero_lt_minimalPeriod_projPowMap P
    by_cases hle : Function.minimalPeriod (projPowMap p) P ≤ R
    · exact Or.inl ⟨P, hmp, hle, hP⟩
    · have hvert : ¬ ∃ i : Fin (n + 1), ∀ j, j ≠ i → P.rep j = 0 := by
        rintro ⟨i, hi⟩
        exact notMem_hypersurface_map_signForm ε hi (singularLocus_subset_hypersurface _ hP)
      push Not at hvert
      obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), P.rep i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact P.rep_nonzero (funext hcon)
      obtain ⟨j, hj, hjne⟩ := hvert i
      exact Or.inr (Set.mem_iUnion.2 ⟨i, P, not_le.1 hle, hi, ⟨j, hj, hjne⟩, hP⟩)
  have hsum : ∑ _i : Fin (n + 1), ((∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
          * ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹
        + (pderivDegBound d : ℝ≥0∞) ^ n
          * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹)
      = ((n : ℝ≥0∞) + 1) * ((∑ i ∈ Finset.range n, (pderivDegBound d : ℝ≥0∞) ^ i)
            * ((2 : ℝ≥0∞) ^ (lowerBlockLength p d + 1))⁻¹
          + (pderivDegBound d : ℝ≥0∞) ^ n
            * ((2 : ℝ≥0∞) ^ min (upperBlockLength p d + 1) (R + 1))⁻¹) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  calc sigma p n d
      ≤ signMeasure ↥(monomialsEq (n + 1) d) (Alow ∪ ⋃ i, Ahigh i) := measure_mono hcover
    _ ≤ signMeasure ↥(monomialsEq (n + 1) d) Alow
          + signMeasure ↥(monomialsEq (n + 1) d) (⋃ i, Ahigh i) := measure_union_le _ _
    _ ≤ signMeasure ↥(monomialsEq (n + 1) d) Alow
          + ∑ i : Fin (n + 1), signMeasure ↥(monomialsEq (n + 1) d) (Ahigh i) :=
        add_le_add le_rfl (measure_iUnion_fintype_le _ _)
    _ ≤ _ := by
        refine add_le_add
          (signMeasure_exists_closedPoint_mem_singularLocus_le hjac p n d R hR) ?_
        rw [← hsum]
        exact Finset.sum_le_sum fun i _ =>
          signMeasure_exists_projClosedPoint_gt_le hbez hdrop hjac hhs hodd hn hd R i

end Finite

end BrowningSawin
