-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.IsPeriodicH1With

/-! Statement file: `IsPeriodicH1` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Periodic `H¹(𝕋²)`. -/
def IsPeriodicH1 (u : Vec 2 → ℝ) : Prop := ∃ Du : Vec 2 → Vec 2, IsPeriodicH1With u Du

end AVenhance
