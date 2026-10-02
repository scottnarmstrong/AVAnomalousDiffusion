-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.Flux

/-! Statement file: `Khom` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `e.Kbarm.def` (label 2983): `K̄^κ_m := ∫_0^1 J^κ_m(t) dt`, as a matrix. -/
def Khom (κ : ℝ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  timeAvgMat fun t => I.flux κ m t

end Ingredients
end AVenhance
