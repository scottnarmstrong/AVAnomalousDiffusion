-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.LatticeShift

/-! Statement file: `IsZ2Periodic` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- ℤ²-periodicity: `f (x + n) = f x` for all `n ∈ ℤ²`, `x ∈ ℝ²`. -/
def IsZ2Periodic {β : Type*} (f : Vec 2 → β) : Prop :=
  ∀ (n : Fin 2 → ℤ) (x : Vec 2), f (x + latticeShift n) = f x

end AVenhance
