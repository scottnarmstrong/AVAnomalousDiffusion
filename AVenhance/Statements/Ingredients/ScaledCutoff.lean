-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib.Basic.Real.Basic

/-! Statement file: `scaledCutoff` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

/-- `e.zeta.mk.def` (1246), `e.xi.mk.def` (1283): `f_{m,k}(t) = f((t - kτ)/τ)`. -/
def scaledCutoff (f : ℝ → ℝ) (τ : ℝ) (k : ℤ) : ℝ → ℝ := fun t => f ((t - k * τ) / τ)

end AVenhance
