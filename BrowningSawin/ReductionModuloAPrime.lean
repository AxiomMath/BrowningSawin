/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import BrowningSawin.Attr
public import BrowningSawin.External
public import BrowningSawin.Cited
public import BrowningSawin.Defs.Definitions
public import BrowningSawin.Notation

/-!
# Reduction modulo a prime

How the singularities of a projective hypersurface `X_F` behave when the coefficients of `F` are
reduced modulo a prime. The singular locus is cut out by the Jacobian ideal `(F, ∂₀F, …, ∂ₙF)`,
reduction of the coefficients commutes with formal differentiation, and the sign forms of `𝓑_{d,n}`
have primitive coefficients, so their reductions are nonzero at every prime; together these give
the specialisation bound `dim Sing X_F̄ ≥ dim Sing X_F` and the corresponding bound on the
probability that a random sign form is singular. Differentiation is computed on the standard affine
charts `x₀ = 1`, where Euler's identity recovers the zeroth derivative from the others.

## Main definitions

* `dehomogenizeChart`: the dehomogenization `g(y) = F(1, y₁, …, y_n)` along the chart `x₀ = 1`.
* `jacobianGens` and `jacobianIdeal`: the family `F, ∂₀F, …, ∂ₙF` and the ideal `I_F` it generates.

## Main results

* `dehomogenizeChart_pderiv_succ`: `∂ᵢF(1, y) = ∂ᵢg(y)` for `1 ≤ i ≤ n`.
* `dehomogenizeChart_pderiv_zero`: `∂₀F(1, y) = d g(y) - ∑_{i=1}^n y_i ∂ᵢg(y)` for `F` homogeneous
  of degree `d`.
* `mem_singularLocus_iff` and `singularLocus_eq_projZeroLocus`: over a perfect field, `Sing X_F` is
  the common zero locus of `F, ∂₀F, …, ∂ₙF`, equivalently the projective zero locus of `I_F`.
* `projDim_projZeroLocus_map`: the dimension of a projective zero locus is unchanged by an
  isomorphism of the coefficient field.
* `gcd_coeff_eq_one_of_mem_signFormSet` and `map_intCast_ne_zero_of_mem_signFormSet`: the
  coefficients of an element of `𝓑_{d,n}` have greatest common divisor `1`, and its reduction
  modulo every prime is nonzero.
* `projDim_singularLocus_complex_le_zmod`: `dim Sing X_F̄ ≥ dim Sing X_F` for primitive homogeneous
  `F ∈ ℤ[x₀, …, x_n]`, the hypersurfaces being taken over `𝔽̄ₚ` and over `ℂ`.
* `zero_le_projDim_of_nonempty`: a nonempty projective algebraic set has dimension at least `0`.
* `measure_isSingularForm_complex_le_sigma`: the probability that the random sign form is singular
  over `ℂ` is at most `σ_{n,d}(p)`.
-/

@[expose] public section

namespace BrowningSawin

open MvPolynomial

universe u

/-! ### Derivatives on the standard chart -/

section Chart

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- `g(y) = F(1, y₁, …, y_n)`, the dehomogenization of `F ∈ R[x₀, …, x_n]` along the standard chart
`x₀ = 1`: the algebra map substituting `1` for `x₀` and `y_i` for `x_{i+1}`. -/
noncomputable def dehomogenizeChart :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (Fin.cons 1 X)

/-- Dehomogenizing along the chart `x₀ = 1` sends `x₀` to `1`. -/
@[simp]
theorem dehomogenizeChart_X_zero :
    dehomogenizeChart (R := R) (n := n) (X 0) = 1 := by
  simp [dehomogenizeChart]

/-- Dehomogenizing along the chart `x₀ = 1` sends `x_{i+1}` to `y_i`. -/
@[simp]
theorem dehomogenizeChart_X_succ (i : Fin n) :
    dehomogenizeChart (R := R) (X i.succ) = X i := by
  simp [dehomogenizeChart]

/-- Evaluating the dehomogenization at `y` is evaluating `F` at `(1, y₁, …, y_n)`. -/
@[simp]
theorem eval_dehomogenizeChart (y : Fin n → R) (F : MvPolynomial (Fin (n + 1)) R) :
    eval y (dehomogenizeChart F) = eval (Fin.cons 1 y) F := by
  have hcomp : (eval y).comp (dehomogenizeChart (R := R) (n := n)).toRingHom
      = eval (Fin.cons 1 y) := by
    refine MvPolynomial.ringHom_ext (fun r => by simp [dehomogenizeChart]) fun j => ?_
    induction j using Fin.cases with
    | zero => simp
    | succ m => simp
  exact congrFun (congrArg (fun f : MvPolynomial (Fin (n + 1)) R →+* R => (f : _ → R)) hcomp) F

/-- Dehomogenizing along the chart `x₀ = 1` commutes with differentiation in the variables
`x₁, …, x_n`: with `g(y) = F(1, y₁, …, y_n)` we have `∂ᵢF(1, y) = ∂ᵢg(y)` for `1 ≤ i ≤ n`, as an
identity of polynomials in `y`. -/
@[browning_sawin "lem_deriv_affine_chart"]
theorem dehomogenizeChart_pderiv_succ (i : Fin n) (F : MvPolynomial (Fin (n + 1)) R) :
    dehomogenizeChart (pderiv i.succ F) = pderiv i (dehomogenizeChart F) := by
  have hX : ∀ j : Fin (n + 1),
      dehomogenizeChart (R := R) (pderiv i.succ (X j))
        = pderiv i (dehomogenizeChart (R := R) (X j)) := by
    intro j
    induction j using Fin.cases with
    | zero => simp [pderiv_X_of_ne (Fin.succ_ne_zero i).symm]
    | succ m =>
        rcases eq_or_ne m i with rfl | hm
        · simp
        · rw [dehomogenizeChart_X_succ, pderiv_X_of_ne hm,
            pderiv_X_of_ne (by simpa using hm), map_zero]
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      rw [pderiv_mul, map_add, map_mul, map_mul, hp, hX j, map_mul, pderiv_mul]

end Chart

section EulerChart

variable {R : Type*} [CommRing R] {n d : ℕ}

/-- The zeroth derivative on the chart `x₀ = 1`: for `F` homogeneous of degree `d` and
`g(y) = F(1, y₁, …, y_n)`,
`∂₀F(1, y) = d g(y) - ∑_{i=1}^n y_i ∂ᵢg(y)`.
This is Euler's identity `∑_i x_i ∂ᵢF = d F`, dehomogenized. -/
@[browning_sawin "lem_deriv_zeroth"]
theorem dehomogenizeChart_pderiv_zero {F : MvPolynomial (Fin (n + 1)) R}
    (hF : F.IsHomogeneous d) :
    dehomogenizeChart (pderiv 0 F) =
      d • dehomogenizeChart F - ∑ i : Fin n, X i * pderiv i (dehomogenizeChart F) := by
  have h := congrArg (dehomogenizeChart (R := R)) hF.sum_X_mul_pderiv
  rw [map_sum, map_nsmul, Fin.sum_univ_succ] at h
  simp only [map_mul, dehomogenizeChart_X_zero, dehomogenizeChart_X_succ, one_mul,
    dehomogenizeChart_pderiv_succ] at h
  rw [eq_sub_iff_add_eq]
  exact h

end EulerChart

/-! ### The singular locus as a zero set -/

/-- **The projective singular locus is a zero set.** For a nonzero `F ∈ k[x₀, …, x_n]` over a
perfect field `k`, a point of `ℙⁿ` over an algebraic closure of `k` lies in `Sing X_F` if and only
if it is a common zero of `F, ∂₀F, …, ∂ₙF`. Conditional on `AffineJacobianCriterion`. -/
@[browning_sawin "lem_proj_sing_equations"]
theorem mem_singularLocus_iff (hjac : AffineJacobianCriterion.{u}) {k : Type u} [Field k]
    [PerfectField k] {n : ℕ} {F : MvPolynomial (Fin (n + 1)) k} (hF : F ≠ 0)
    (P : Projectivization (AlgebraicClosure k) (Fin (n + 1) → AlgebraicClosure k)) :
    P ∈ singularLocus F ↔
      eval P.rep (toClosure F) = 0 ∧ ∀ i, eval P.rep (toClosure (pderiv i F)) = 0 := by
  constructor
  · rintro ⟨h0, hns⟩
    exact ⟨h0, (hjac hF h0).1 hns⟩
  · rintro ⟨h0, hpd⟩
    exact ⟨h0, (hjac hF h0).2 hpd⟩

/-! ### Homogeneous ideals and their zero loci -/

section Homogeneous

variable {R : Type*} [CommSemiring R] {σ : Type*}

/-- Every homogeneous component of a multiple of a homogeneous element of an ideal again lies in
that ideal. -/
theorem homogeneousComponent_mul_mem {I : Ideal (MvPolynomial σ R)} {G : MvPolynomial σ R} {m : ℕ}
    (hG : G.IsHomogeneous m) (hGI : G ∈ I) (c : MvPolynomial σ R) (e : ℕ) :
    homogeneousComponent e (c * G) ∈ I := by
  classical
  have key : homogeneousComponent e (c * G)
      = ∑ β ∈ c.support, homogeneousComponent e (monomial β (coeff β c) * G) := by
    rw [← map_sum, ← Finset.sum_mul, ← c.as_sum]
  rw [key]
  refine Ideal.sum_mem _ fun β _ => ?_
  rw [homogeneousComponent_of_mem
    ((mem_homogeneousSubmodule _ _).2 ((isHomogeneous_monomial _ rfl).mul hG))]
  split_ifs
  · exact Ideal.mul_mem_left _ _ hGI
  · exact Ideal.zero_mem _

/-- An ideal generated by homogeneous elements is closed under taking homogeneous components. -/
theorem homogeneousComponent_mem_span_range {ι : Type*} [Finite ι] {v : ι → MvPolynomial σ R}
    {m : ι → ℕ} (hv : ∀ i, (v i).IsHomogeneous (m i)) {G : MvPolynomial σ R}
    (hG : G ∈ Ideal.span (Set.range v)) (e : ℕ) :
    homogeneousComponent e G ∈ Ideal.span (Set.range v) := by
  cases nonempty_fintype ι
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hG
  rw [← hc, map_sum]
  exact Ideal.sum_mem _ fun i _ =>
    homogeneousComponent_mul_mem (hv i) (Ideal.subset_span (Set.mem_range_self i)) _ _

/-- The zero locus of an ideal closed under taking homogeneous components is a cone: if every
element of the ideal vanishes at `a`, then every element vanishes at `c a`. -/
theorem eval_smul_eq_zero_of_forall [Finite σ] {I : Ideal (MvPolynomial σ R)}
    (hI : ∀ G ∈ I, ∀ e, homogeneousComponent e G ∈ I) {a : σ → R}
    (ha : ∀ G ∈ I, eval a G = 0) (c : R) {G : MvPolynomial σ R} (hG : G ∈ I) :
    eval (c • a) G = 0 := by
  calc eval (c • a) G
      = eval (c • a) (∑ i ∈ Finset.range (G.totalDegree + 1), homogeneousComponent i G) := by
        rw [sum_homogeneousComponent]
    _ = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous i G),
          ha _ (hI G hG i), mul_zero]

end Homogeneous

/-! ### Transport along an isomorphism of the coefficient field

Complex hypersurfaces live over `ℂ`, while `singularLocus` takes its points over an algebraic
closure of the field of coefficients. The two are related by the isomorphism
`ℂ ≃+* AlgebraicClosure ℂ`, and the dimension of a projective zero locus is transported along any
isomorphism of the coefficient field. -/

section Transport

variable {K L : Type*} [Field K] [Field L] {n : ℕ}

/-- Evaluating the image of `G` under an isomorphism of coefficients at the transported point. -/
theorem eval_map_ringEquiv {σ : Type*} (φ : K ≃+* L) (a : σ → K) (G : MvPolynomial σ K) :
    eval (fun i => φ (a i)) (MvPolynomial.map (φ : K →+* L) G) = φ (eval a G) := by
  have h := eval₂_comp_left (φ : K →+* L) (RingHom.id K) a G
  rw [RingHom.comp_id] at h
  rw [eval_map]
  exact h.symm

/-- Mapping the coefficients of a polynomial over `K` along `φ` and then along `φ.symm` returns the
original polynomial. -/
theorem map_symm_map {σ : Type*} (φ : K ≃+* L) (H : MvPolynomial σ K) :
    MvPolynomial.map (φ.symm : L →+* K) (MvPolynomial.map (φ : K →+* L) H) = H := by
  ext α; simp [coeff_map]

/-- Mapping the coefficients of a polynomial over `L` along `φ.symm` and then along `φ` returns the
original polynomial. -/
theorem map_map_symm {σ : Type*} (φ : K ≃+* L) (H : MvPolynomial σ L) :
    MvPolynomial.map (φ : K →+* L) (MvPolynomial.map (φ.symm : L →+* K) H) = H := by
  ext α; simp [coeff_map]

/-- A polynomial over `L` lies in the ideal transported along `φ` exactly when the polynomial
obtained by mapping its coefficients along `φ.symm` lies in the original ideal. -/
theorem mem_map_map_iff {σ : Type*} (φ : K ≃+* L) {J : Ideal (MvPolynomial σ K)}
    {G : MvPolynomial σ L} :
    G ∈ J.map (MvPolynomial.map (φ : K →+* L)) ↔ MvPolynomial.map (φ.symm : L →+* K) G ∈ J := by
  constructor
  · intro h
    obtain ⟨H, hH, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ (map_surjective _ φ.surjective)).1 h
    rwa [map_symm_map]
  · intro h
    rw [← map_map_symm φ G]
    exact Ideal.mem_map_of_mem _ h

/-- Evaluating at `b` the polynomial obtained from `H` by mapping its coefficients along `φ` is `φ`
applied to the value of `H` at the point `φ.symm ∘ b`. -/
theorem eval_map_eq_apply_eval {σ : Type*} (φ : K ≃+* L) (b : σ → L) (H : MvPolynomial σ K) :
    eval b (MvPolynomial.map (φ : K →+* L) H) = φ (eval (fun i => φ.symm (b i)) H) := by
  simpa using eval_map_ringEquiv φ (fun i => φ.symm (b i)) H

/-- The transported ideal vanishes at a point of affine space over `L` exactly when the original
ideal vanishes at the corresponding point over `K`. -/
theorem forall_eval_map_eq_zero_iff {σ : Type*} (φ : K ≃+* L) (J : Ideal (MvPolynomial σ K))
    (b : σ → L) :
    (∀ G ∈ J.map (MvPolynomial.map (φ : K →+* L)), eval b G = 0)
      ↔ ∀ H ∈ J, eval (fun i => φ.symm (b i)) H = 0 := by
  constructor
  · intro h H hH
    refine (RingEquiv.map_eq_zero_iff φ).1 ?_
    rw [← eval_map_eq_apply_eval φ b H]
    exact h _ (Ideal.mem_map_of_mem _ hH)
  · intro h G hG
    rw [← map_map_symm φ G, eval_map_eq_apply_eval, h _ ((mem_map_map_iff φ).1 hG), map_zero]

/-- The isomorphism of polynomial rings induced by an isomorphism `φ` of the coefficients is
mapping the coefficients along `φ`. -/
theorem coe_mapEquiv {σ : Type*} (φ : K ≃+* L) :
    ((MvPolynomial.mapEquiv σ φ : MvPolynomial σ K ≃+* MvPolynomial σ L) :
        MvPolynomial σ K →+* MvPolynomial σ L) = MvPolynomial.map (φ : K →+* L) :=
  RingHom.ext fun p => by simp

/-- The dimension of an affine algebraic set is unchanged by an isomorphism of the coefficient
field. -/
theorem affineDim_image_of_ringEquiv (φ : K ≃+* L) (V : Set (Fin n → K)) :
    affineDim ((fun (a : Fin n → K) (i : Fin n) => φ (a i)) '' V) = affineDim V := by
  have hvan : affineVanishingIdeal ((fun (a : Fin n → K) (i : Fin n) => φ (a i)) '' V)
      = (affineVanishingIdeal V).map (MvPolynomial.map (φ : K →+* L)) := by
    ext G
    rw [mem_affineVanishingIdeal, mem_map_map_iff, mem_affineVanishingIdeal]
    constructor
    · intro h a ha
      refine (RingEquiv.map_eq_zero_iff φ).1 ?_
      rw [← eval_map_ringEquiv φ a (MvPolynomial.map (φ.symm : L →+* K) G), map_map_symm]
      exact h _ (Set.mem_image_of_mem _ ha)
    · rintro h b ⟨a, ha, rfl⟩
      rw [← map_map_symm φ G, eval_map_eq_apply_eval]
      simp only [RingEquiv.symm_apply_apply]
      rw [h a ha, map_zero]
  rw [affineDim, affineDim, hvan, ← coe_mapEquiv φ,
    ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv (affineVanishingIdeal V) _
      (MvPolynomial.mapEquiv (Fin n) φ) rfl)]

/-- The affine cone over the projective zero locus of an ideal closed under taking homogeneous
components is transported by an isomorphism of the coefficient field. -/
theorem affineCone_projZeroLocus_map (φ : K ≃+* L) {J : Ideal (MvPolynomial (Fin (n + 1)) K)}
    (hJ : ∀ G ∈ J, ∀ e, homogeneousComponent e G ∈ J) :
    affineCone (projZeroLocus (J.map (MvPolynomial.map (φ : K →+* L))))
      = (fun (a : Fin (n + 1) → K) (i : Fin (n + 1)) => φ (a i)) ''
          affineCone (projZeroLocus J) := by
  ext b
  constructor
  · rintro ⟨Q, hQ, c, rfl⟩
    have haJ : ∀ H ∈ J, eval (fun i => φ.symm (Q.rep i)) H = 0 :=
      (forall_eval_map_eq_zero_iff φ J Q.rep).1 hQ
    have ha0 : (fun i => φ.symm (Q.rep i)) ≠ 0 := by
      intro h
      refine Q.rep_nonzero (funext fun i => ?_)
      simpa using congrArg φ (congrFun h i)
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep K _ ha0
    set P := Projectivization.mk K (fun i => φ.symm (Q.rep i)) ha0 with hPdef
    have hP : P ∈ projZeroLocus J := by
      intro H hH
      rw [← hu, Units.smul_def]
      exact eval_smul_eq_zero_of_forall hJ haJ (u : K) hH
    refine ⟨(φ.symm c * (u : K)⁻¹) • P.rep, ⟨P, hP, _, rfl⟩, ?_⟩
    have hstep : (φ.symm c * (u : K)⁻¹) • P.rep = φ.symm c • fun i => φ.symm (Q.rep i) := by
      rw [← hu, Units.smul_def, smul_smul, mul_assoc, inv_mul_cancel₀ u.ne_zero, mul_one]
    rw [hstep]
    funext i
    simp
  · rintro ⟨a, ⟨P, hP, c, rfl⟩, rfl⟩
    have hv0 : (fun i => φ (P.rep i)) ≠ 0 := by
      intro h
      refine P.rep_nonzero (funext fun i => ?_)
      simpa using congrArg φ.symm (congrFun h i)
    obtain ⟨w, hw⟩ := Projectivization.exists_smul_eq_mk_rep L _ hv0
    set Q := Projectivization.mk L (fun i => φ (P.rep i)) hv0 with hQdef
    have hQ : Q ∈ projZeroLocus (J.map (MvPolynomial.map (φ : K →+* L))) := by
      rw [projZeroLocus, Set.mem_ofPred_eq, forall_eval_map_eq_zero_iff]
      intro H hH
      have hrep : (fun i => φ.symm (Q.rep i)) = φ.symm (w : L) • P.rep := by
        funext i
        rw [← hw]
        simp [Units.smul_def]
      rw [hrep]
      exact eval_smul_eq_zero_of_forall hJ hP _ hH
    refine ⟨Q, hQ, φ c * (w : L)⁻¹, ?_⟩
    have hstep : (φ c * (w : L)⁻¹) • Q.rep = φ c • fun i => φ (P.rep i) := by
      rw [← hw, Units.smul_def, smul_smul, mul_assoc, inv_mul_cancel₀ w.ne_zero, mul_one]
    rw [hstep]
    funext i
    simp

/-- The dimension of the projective zero locus of an ideal closed under taking homogeneous
components is unchanged by an isomorphism of the coefficient field. -/
theorem projDim_projZeroLocus_map (φ : K ≃+* L) {J : Ideal (MvPolynomial (Fin (n + 1)) K)}
    (hJ : ∀ G ∈ J, ∀ e, homogeneousComponent e G ∈ J) :
    projDim (projZeroLocus (J.map (MvPolynomial.map (φ : K →+* L))))
      = projDim (projZeroLocus J) := by
  rw [projDim, projDim, affineCone_projZeroLocus_map φ hJ, affineDim_image_of_ringEquiv]

end Transport

/-! ### The Jacobian ideal -/

section Jacobian

variable {R : Type*} [CommRing R] {n : ℕ}

/-- `F, ∂₀F, …, ∂ₙF`: the form together with its first partial derivatives. -/
noncomputable def jacobianGens (F : MvPolynomial (Fin (n + 1)) R) :
    Fin (n + 2) → MvPolynomial (Fin (n + 1)) R :=
  Fin.cons F fun i => pderiv i F

/-- `I_F = (F, ∂₀F, …, ∂ₙF)`, the ideal cutting out the singular locus of the hypersurface
`X_F`. -/
noncomputable def jacobianIdeal (F : MvPolynomial (Fin (n + 1)) R) :
    Ideal (MvPolynomial (Fin (n + 1)) R) :=
  Ideal.span (Set.range (jacobianGens F))

/-- A point is a zero of the Jacobian ideal exactly when it is a common zero of `F` and of all its
first partial derivatives. -/
theorem forall_eval_jacobianIdeal_iff (F : MvPolynomial (Fin (n + 1)) R) (b : Fin (n + 1) → R) :
    (∀ G ∈ jacobianIdeal F, eval b G = 0)
      ↔ eval b F = 0 ∧ ∀ i, eval b (pderiv i F) = 0 := by
  constructor
  · intro h
    refine ⟨h _ (Ideal.subset_span ⟨0, rfl⟩), fun i => h _ (Ideal.subset_span ⟨i.succ, ?_⟩)⟩
    simp [jacobianGens]
  · rintro ⟨h0, hi⟩ G hG
    have hsub : Set.range (jacobianGens F)
        ⊆ (RingHom.ker (eval b) : Set (MvPolynomial (Fin (n + 1)) R)) := by
      rintro G' ⟨j, rfl⟩
      induction j using Fin.cases with
      | zero => exact RingHom.mem_ker.2 (by simpa [jacobianGens] using h0)
      | succ m => exact RingHom.mem_ker.2 (by simpa [jacobianGens] using hi m)
    exact RingHom.mem_ker.1 (Ideal.span_le.2 hsub hG)

/-- Reduction of the coefficients commutes with forming the Jacobian ideal. -/
theorem jacobianIdeal_map {S : Type*} [CommRing S] (f : R →+* S)
    (F : MvPolynomial (Fin (n + 1)) R) :
    (jacobianIdeal F).map (MvPolynomial.map f) = jacobianIdeal (F.map f) := by
  have hfun : MvPolynomial.map f ∘ jacobianGens F = jacobianGens (F.map f) := by
    funext j
    induction j using Fin.cases with
    | zero => simp [jacobianGens]
    | succ m => simp [jacobianGens, pderiv_map]
  rw [jacobianIdeal, jacobianIdeal, Ideal.map_span, ← Set.range_comp, hfun]

/-- The Jacobian ideal of a homogeneous form is closed under taking homogeneous components. -/
theorem homogeneousComponent_mem_jacobianIdeal {d : ℕ} {F : MvPolynomial (Fin (n + 1)) R}
    (hF : F.IsHomogeneous d) {G : MvPolynomial (Fin (n + 1)) R} (hG : G ∈ jacobianIdeal F)
    (e : ℕ) : homogeneousComponent e G ∈ jacobianIdeal F := by
  refine homogeneousComponent_mem_span_range (m := Fin.cons d fun _ => d - 1) ?_ hG e
  intro j
  induction j using Fin.cases with
  | zero => simpa [jacobianGens] using hF
  | succ m => simpa [jacobianGens] using hF.pderiv

/-- **The projective singular locus is a zero set**, in ideal-theoretic form: `Sing X_F` is the
projective zero locus of the Jacobian ideal of `F` over an algebraic closure. Conditional on
`AffineJacobianCriterion`. -/
theorem singularLocus_eq_projZeroLocus (hjac : AffineJacobianCriterion.{u}) {k : Type u} [Field k]
    [PerfectField k] {F : MvPolynomial (Fin (n + 1)) k} (hF : F ≠ 0) :
    singularLocus F = projZeroLocus (jacobianIdeal (toClosure F)) := by
  ext P
  rw [mem_singularLocus_iff hjac hF, projZeroLocus, Set.mem_ofPred_eq,
    forall_eval_jacobianIdeal_iff]
  refine and_congr Iff.rfl (forall_congr' fun i => ?_)
  rw [toClosure, toClosure, pderiv_map]

end Jacobian

/-! ### Sign forms are primitive -/

/-- An integral polynomial whose coefficients have greatest common divisor `1` has nonzero
reduction modulo every `p ≠ 1`. -/
theorem map_intCast_ne_zero_of_gcd_coeff_eq_one {σ : Type*} {F : MvPolynomial σ ℤ}
    (hF : F.support.gcd F.coeff = 1) {p : ℕ} (hp : p ≠ 1) :
    F.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro h
  have hdvd : ∀ α ∈ F.support, (p : ℤ) ∣ F.coeff α := by
    intro α _
    have := congrArg (coeff α) h
    rw [coeff_map, coeff_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using this)
  have h1 : (p : ℤ) ∣ 1 := hF ▸ Finset.dvd_gcd hdvd
  exact hp (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h1)

/-- **Sign forms are primitive.** The coefficients of an element of `𝓑_{d,n}` have greatest common
divisor `1`. -/
@[browning_sawin "lem_sign_form_primitive"]
theorem gcd_coeff_eq_one_of_mem_signFormSet {n d : ℕ} {F : MvPolynomial (Fin (n + 1)) ℤ}
    (hF : F ∈ signFormSet n d) : F.support.gcd F.coeff = 1 := by
  set α : Fin (n + 1) →₀ ℕ := Finsupp.single 0 d with hα
  have hdeg : α.degree = d := by rw [hα, Finsupp.degree_single]
  have hcoeff : F.coeff α = 1 ∨ F.coeff α = -1 := hF.2 α hdeg
  have hmem : α ∈ F.support := by
    rw [mem_support_iff]
    rcases hcoeff with h | h <;> simp [h]
  have hunit : IsUnit (F.support.gcd F.coeff) :=
    isUnit_of_dvd_unit (Finset.gcd_dvd hmem) (Int.isUnit_iff.2 hcoeff)
  rw [← Finset.normalize_gcd, normalize_eq_one]
  exact hunit

/-- **Sign forms are primitive**, second half: an element of `𝓑_{d,n}` has nonzero reduction modulo
every prime. -/
@[browning_sawin "lem_sign_form_primitive"]
theorem map_intCast_ne_zero_of_mem_signFormSet {n d : ℕ} {F : MvPolynomial (Fin (n + 1)) ℤ}
    (hF : F ∈ signFormSet n d) {p : ℕ} (hp : p.Prime) :
    F.map (Int.castRingHom (ZMod p)) ≠ 0 :=
  map_intCast_ne_zero_of_gcd_coeff_eq_one (gcd_coeff_eq_one_of_mem_signFormSet hF) hp.ne_one

/-! ### The singular dimension does not drop -/

/-- Reducing the coefficients of an integral polynomial in two steps is reducing them in one. -/
theorem map_map_intCast {A B : Type*} [CommRing A] [CommRing B] {σ : Type*} (f : ℤ →+* A)
    (g : A →+* B) (F : MvPolynomial σ ℤ) : (F.map f).map g = F.map (Int.castRingHom B) := by
  rw [MvPolynomial.map_map, RingHom.ext_int (g.comp f) (Int.castRingHom B)]

/-- **The singular dimension does not drop.** For a homogeneous `F ∈ ℤ[x₀, …, x_n]` whose
coefficients have greatest common divisor `1` and a prime `p`,
`dim Sing X_F̄ ≥ dim Sing X_F`, the hypersurfaces being taken over `𝔽̄ₚ` and over `ℂ`. Conditional
on `FiberDimensionSemicontinuity` and `AffineJacobianCriterion`. -/
@[browning_sawin "lem_sing_specialization"]
theorem projDim_singularLocus_complex_le_zmod (hsemi : FiberDimensionSemicontinuity)
    (hjac : AffineJacobianCriterion.{0}) {n d : ℕ} {F : MvPolynomial (Fin (n + 1)) ℤ}
    (hF : F.IsHomogeneous d) (hgcd : F.support.gcd F.coeff = 1) (p : ℕ) [Fact p.Prime] :
    projDim (singularLocus (F.map (Int.castRingHom ℂ)))
      ≤ projDim (singularLocus (F.map (Int.castRingHom (ZMod p)))) := by
  have hp : p.Prime := Fact.out
  have hF0 : F ≠ 0 := by
    intro h
    rw [h] at hgcd
    simp at hgcd
  have hC0 : F.map (Int.castRingHom ℂ) ≠ 0 := by
    intro h
    exact hF0 (map_injective (Int.castRingHom ℂ) Int.cast_injective (by simpa using h))
  have hZ0 : F.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_intCast_ne_zero_of_gcd_coeff_eq_one hgcd hp.ne_one
  set φ : ℂ ≃+* AlgebraicClosure ℂ := RingEquiv.ofBijective (algebraMap ℂ (AlgebraicClosure ℂ))
    IsAlgClosed.algebraMap_bijective_of_isIntegral with hφ
  have hclosZ : toClosure (F.map (Int.castRingHom (ZMod p)))
      = F.map (Int.castRingHom (AlgebraicClosure (ZMod p))) := map_map_intCast _ _ F
  have hclosC : toClosure (F.map (Int.castRingHom ℂ))
      = F.map (Int.castRingHom (AlgebraicClosure ℂ)) := map_map_intCast _ _ F
  have hmapφ : (F.map (Int.castRingHom ℂ)).map (φ : ℂ →+* AlgebraicClosure ℂ)
      = F.map (Int.castRingHom (AlgebraicClosure ℂ)) := map_map_intCast _ _ F
  have hlhs : projDim (singularLocus (F.map (Int.castRingHom ℂ)))
      = projDim (projZeroLocus (jacobianIdeal (F.map (Int.castRingHom ℂ)))) := by
    rw [singularLocus_eq_projZeroLocus hjac hC0, hclosC, ← hmapφ, ← jacobianIdeal_map]
    exact projDim_projZeroLocus_map φ
      fun G hG e => homogeneousComponent_mem_jacobianIdeal (hF.map _) hG e
  have hrhs : singularLocus (F.map (Int.castRingHom (ZMod p)))
      = projZeroLocus (jacobianIdeal (F.map (Int.castRingHom (AlgebraicClosure (ZMod p))))) := by
    rw [singularLocus_eq_projZeroLocus hjac hZ0, hclosZ]
  rw [hlhs, hrhs, ← jacobianIdeal_map, ← jacobianIdeal_map]
  exact hsemi (jacobianIdeal F)
    (fun G hG e => homogeneousComponent_mem_jacobianIdeal hF hG e) p

/-! ### A nonempty projective algebraic set has dimension at least zero -/

section Nonempty

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}

/-- Evaluation after a substitution is evaluation at the substituted values. -/
theorem eval_aeval {R : Type*} [CommSemiring R] {σ τ : Type*} (f : σ → MvPolynomial τ R)
    (y : τ → R) (G : MvPolynomial σ R) :
    eval y (aeval f G) = eval (fun i => eval y (f i)) G := by
  have h : (eval y).comp (aeval f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R).toRingHom
      = eval (fun i => eval y (f i)) :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun i => by simp
  exact congrFun (congrArg (fun F : MvPolynomial σ R →+* R => (F : _ → R)) h) G

/-- The affine cone over a nonempty projective algebraic set has dimension at least `1`. -/
theorem one_le_affineDim_affineCone {T : Set (Projectivization K (Fin (n + 1) → K))}
    (hT : T.Nonempty) : 1 ≤ affineDim (affineCone T) := by
  obtain ⟨P, hP⟩ := hT
  obtain ⟨j, hj⟩ : ∃ j, P.rep j ≠ 0 := by
    by_contra h
    exact P.rep_nonzero (funext fun i => by simpa using not_exists.1 h i)
  set Ψ : MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin 1) K :=
    aeval fun i => C (P.rep i) * X 0 with hΨ
  have hker : ∀ G ∈ affineVanishingIdeal (affineCone T), Ψ G = 0 := by
    intro G hG
    rw [mem_affineVanishingIdeal] at hG
    refine MvPolynomial.funext fun y => ?_
    rw [map_zero, hΨ]
    have hpt : (fun i => eval y (C (P.rep i) * X (0 : Fin 1))) = y 0 • P.rep := by
      funext i
      simp [mul_comm]
    rw [eval_aeval, hpt]
    exact hG _ ⟨P, hP, y 0, rfl⟩
  have hsurj : Function.Surjective Ψ := by
    have hrange : Ψ.range = ⊤ := by
      rw [← top_le_iff, ← MvPolynomial.adjoin_range_X]
      refine Algebra.adjoin_le ?_
      rintro q ⟨i, rfl⟩
      refine ⟨C (P.rep j)⁻¹ * X j, ?_⟩
      rw [Subsingleton.elim i 0]
      change Ψ (C (P.rep j)⁻¹ * X j) = X 0
      rw [hΨ, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ hj, C_1, one_mul]
    intro q
    exact (AlgHom.mem_range Ψ).1 (hrange ▸ Algebra.mem_top)
  have hlift : Function.Surjective
      (Ideal.Quotient.lift (affineVanishingIdeal (affineCone T)) Ψ.toRingHom hker) := by
    intro q
    obtain ⟨x, hx⟩ := hsurj q
    exact ⟨Ideal.Quotient.mk _ x, hx⟩
  have hdim := ringKrullDim_le_of_surjective _ hlift
  have hone : ringKrullDim (MvPolynomial (Fin 1) K) = ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hle : ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ affineVanishingIdeal (affineCone T))
      ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    have hpoly : ringKrullDim (MvPolynomial (Fin (n + 1)) K)
        = (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    exact hpoly ▸ ringKrullDim_quotient_le _
  rw [affineDim]
  cases hcase :
      ringKrullDim (MvPolynomial (Fin (n + 1)) K ⧸ affineVanishingIdeal (affineCone T)) with
  | bot =>
      rw [hcase, hone] at hdim
      simp at hdim
  | coe r =>
      rw [hcase, hone] at hdim
      rw [hcase] at hle
      simp only [WithBot.recBotCoe_coe]
      have hr1 : (1 : ℕ∞) ≤ r := by exact_mod_cast hdim
      have hle' : r ≤ ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast hle
      have hrne : r ≠ ⊤ :=
        ne_top_of_le_ne_top (by exact_mod_cast ENat.natCast_ne_top (n + 1)) hle'
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hrne
      subst hk
      have : 1 ≤ k := by exact_mod_cast hr1
      simpa using this

/-- A nonempty projective algebraic set has dimension at least `0`. -/
theorem zero_le_projDim_of_nonempty {T : Set (Projectivization K (Fin (n + 1) → K))}
    (hT : T.Nonempty) : 0 ≤ projDim T := by
  have h := one_le_affineDim_affineCone hT
  rw [projDim_eq_affineDim_cone_sub_one hT]
  omega

end Nonempty

/-! ### The singularity probability passes to a prime -/

private theorem signForm_mem_signFormSet {n d : ℕ} (ε : SignFamily (monomialsEq (n + 1) d)) :
    signForm n d ε ∈ signFormSet n d := by
  refine ⟨fun α hα => ?_, fun α hα => ?_⟩
  · rw [signForm, coeff_sum]
    refine Finset.sum_eq_zero fun β hβ => ?_
    rw [coeff_monomial, ite_eq_right]
    rintro rfl
    exact hα (mem_monomialsEq.1 hβ)
  · rw [coeff_signForm _ hα]
    rcases Int.units_eq_one_or (signOf ε α) with h | h <;> simp [h]

private theorem signForm_isHomogeneous {n d : ℕ} (ε : SignFamily (monomialsEq (n + 1) d)) :
    (signForm n d ε).IsHomogeneous d := by
  rw [signForm]
  refine (mem_homogeneousSubmodule _ _).1 (Submodule.sum_mem _ fun α hα => ?_)
  exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_monomial _ (mem_monomialsEq.1 hα))

/-- **The singularity probability passes to a prime.** The probability that the random sign form
`f` is singular over `ℂ` is at most `σ_{n,d}(p)`, the probability that its reduction modulo `p` is
singular over `𝔽̄ₚ`. Conditional on `FiberDimensionSemicontinuity` and
`AffineJacobianCriterion`. -/
@[browning_sawin "lem_prob_specialization"]
theorem measure_isSingularForm_complex_le_sigma (hsemi : FiberDimensionSemicontinuity)
    (hjac : AffineJacobianCriterion.{0}) (n d p : ℕ) [Fact p.Prime] :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
      ≤ sigma p n d := by
  rw [sigma]
  refine MeasureTheory.measure_mono fun ε hε => ?_
  have hle := projDim_singularLocus_complex_le_zmod hsemi hjac (signForm_isHomogeneous ε)
    (gcd_coeff_eq_one_of_mem_signFormSet (signForm_mem_signFormSet ε)) p
  have h0 := zero_le_projDim_of_nonempty hε
  by_contra hcon
  rw [Set.mem_ofPred_eq, IsSingularForm, Set.not_nonempty_iff_eq_empty] at hcon
  rw [hcon, projDim_empty] at hle
  omega

end BrowningSawin
