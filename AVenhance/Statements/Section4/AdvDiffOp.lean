-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.SpaceLap

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `(∂_t - κ Δ + b · ∇) u`, classical derivatives (source order of `e.theta.m`, label 3856). -/
def advDiffOp (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (u : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  deriv (fun s => u s x) t - κ * spaceLap (u t) x + vecDot (b t x) (spaceGrad (u t) x)

end AVenhance
