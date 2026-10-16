-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.KappaAt

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `κ_m` of `e.kappa.sequence` for the chain topped at `M` (convention of the
`kappaAt`): `κ_m = kappaAt I κ m (M - m)`, `0 ≤ m ≤ M`; `κ_M = κ`. -/
def kappaSeq (κ : ℝ) (M m : ℕ) : ℝ := I.kappaAt κ m (M - m)

end Ingredients
end AVenhance
