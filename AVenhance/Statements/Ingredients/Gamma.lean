-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.Nstar

/-! Statement file: `gamma` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.gamma` (1025): `γ := (q-1)β/(q+1)`. -/
def gamma (β : ℝ) : ℝ := ((q β - 1) * β) / (q β + 1)

end AVenhance
