-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.L2NormSq

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance
/-- Time-Hölder seminorm bound on `[0,1]` with values in `L²(𝕋²)` (unit cell):
`‖θ(t) − θ(s)‖_{L²} ≤ H |t − s|^μ` for all `s, t ∈ [0,1]`. -/
def IsHolderTimeL2 (μ H : ℝ) (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤ H * |t - s| ^ μ

end AVenhance
