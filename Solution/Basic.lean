/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import BrowningSawin

/-! # Solutions to the formal challenge

Each statement of the challenge file, proved from the library.
-/

@[expose] public section

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
  signMeasure_one_le_projDim_singularLocus_le hcited hn hd

/-- **`thm_absolute_irred` — the reducibility bound.** For `n ≥ 3` and `d ≥ 3`, the probability
that `f` is reducible over `ℂ` obeys the same bound. -/
theorem thm_absolute_irred (hcited : CitedResults.{0}) {n d : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) :
    signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
        {ε | ¬ Irreducible ((signForm n d ε).map (Int.castRingHom ℂ))}
      ≤ (n : ℝ≥0∞) * ((n : ℝ≥0∞) + 1) * (d : ℝ≥0∞) ^ (n - 1)
          * ((2 : ℝ≥0∞) ^ ((d - 1) / 3 + 1))⁻¹ :=
  signMeasure_not_irreducible_complex_le hcited hn hd

/-- **`thm_main` — the main theorem.** For each `n ≥ 1` there is a `C_n > 0` with
`𝐏(f is singular over ℂ) ≤ C_n d^{-1/2}` for every `d ≥ 3`. -/
theorem thm_main (hcited : CitedResults.{0}) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      signMeasure {α : Fin (n + 1) →₀ ℕ // α ∈ monomialsEq (n + 1) d}
          {ε | IsSingularForm ((signForm n d ε).map (Int.castRingHom ℂ))}
        ≤ ENNReal.ofReal (C / Real.sqrt d) :=
  exists_measure_isSingularForm_complex_le hcited hn

/-- **`thm_bs_conjecture` — the Browning–Sawin conjecture.** For each `n ≥ 2`, the proportion of
nonsingular forms in `𝓑_{d,n}` is `1 + O_n(d^{-1/2})`. -/
theorem thm_bs_conjecture (hcited : CitedResults.{0}) {n : ℕ} (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 3 ≤ d →
      |(Nat.card {F : MvPolynomial (Fin (n + 1)) ℤ // F ∈ signFormSet n d ∧
            ¬ IsSingularForm (F.map (Int.castRingHom ℂ))} : ℝ)
          / 2 ^ monomialCount n d - 1| ≤ C / Real.sqrt d :=
  exists_forall_abs_card_notSingular_div_sub_one_le hcited hn

end BrowningSawin.Challenge
