-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.GradNormSq
public import AVenhance.Statements.Roots.IsZ2Periodic
public import AVenhance.Statements.Roots.SpaceGrad
public import Mathlib.Order.CompletePartialOrder

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `‖h‖_{Ḣ⁻¹(𝕋²)} = sup { ∫_{(0,1)²} h φ : φ ∈ C^∞ periodic, ‖∇φ‖_{L²} ≤ 1 }` (the source
uses the norm in `e.bigbound` (7017-7021) and 7047-7078 without a formula).  `ℝ≥0∞`-valued: `⊤` if `h` has nonzero
mean (constants are admissible `φ`), so no junk value. -/
def hMinusOneNorm (h : Vec 2 → ℝ) : ENNReal :=
  ⨆ φ : {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsZ2Periodic φ ∧ gradNormSq (spaceGrad φ) ≤ 1},
    ENNReal.ofReal |∫ x in unitCube, h x * φ.1 x|

end AVenhance
