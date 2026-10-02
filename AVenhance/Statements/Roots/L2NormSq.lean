-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.TimeCube

/-! Statement file: `l2NormSq` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- `∫_{(0,1)²} f²`. -/
noncomputable def l2NormSq (f : Vec 2 → ℝ) : ℝ := ∫ x in unitCube, f x ^ 2

end AVenhance
