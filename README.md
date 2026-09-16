[![](logo.svg)](https://axiommath.ai/)

# Random Hypersurfaces with Sign Coefficients

This is a Lean formalization of the theorem that a random hypersurface with sign coefficients is nonsingular with probability `1 - O_n(d^{-1/2})`.

## Main Results

* For each `n ≥ 1` there is a `C_n > 0` with `P(f is singular over ℂ) ≤ C_n d^{-1/2}` for every `d ≥ 3`.
* For `n ≥ 1` and `d ≥ 3`, `P(dim Sing X_f ≥ 1) ≤ n(n+1) d^{n-1} 2^{-⌊(d-1)/3⌋-1}` over `ℂ`.
* For `n ≥ 3` and `d ≥ 3`, `P(f is reducible over ℂ)` obeys the same bound.
* The Browning–Sawin conjecture: for `n ≥ 2`, `#{F ∈ 𝓑_{d,n} : F is not singular}/2^{N_{d,n}} = 1 + O_n(d^{-1/2})`.

Each is conditional on the five classical results the source defers to the literature: affine Bézout, dimension drop under a nonvanishing equation, semicontinuity of fiber dimension, the affine hypersurface Jacobian criterion, and Hilbert–Serre. They are stated with their citations in [BrowningSawin/Cited.lean](BrowningSawin/Cited.lean) and taken as an **explicit hypothesis**, so nothing here is assumed by fiat: the library declares no axioms, and the permitted axioms of [Comparator/comparator.json](Comparator/comparator.json) are only `propext`, `Quot.sound` and `Classical.choice`.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on the dependency above. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
