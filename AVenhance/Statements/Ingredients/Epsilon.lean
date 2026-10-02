-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.Gamma

/-! Statement file: `epsilon` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization

/-- `e.epm.choice` (1041-1052): `ε_0 := 1`, `ε_m⁻¹ := ⌈Λ^{q^m/(q-1)}⌉` for `m ≥ 1`. -/
def epsilon (β : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  if m = 0 then 1
  else ((⌈(Λ : ℝ) ^ ((q β) ^ m / (q β - 1))⌉₊ : ℕ) : ℝ)⁻¹

end AVenhance
