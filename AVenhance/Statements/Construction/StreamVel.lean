-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.SigmaMat
public import AVenhance.Statements.Roots.SpaceGrad

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- `e.phim.bm` (1405-1407) with `e.sigma` (919): `∇^⊥ φ (t,x) = σ ∇_x φ (t,x)`. -/
def streamVel (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  sigmaMat.mulVec (spaceGrad (φ t) x)

end AVenhance
