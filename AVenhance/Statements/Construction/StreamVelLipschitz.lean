-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

import AVenhance.Infra.Flow.SmoothField
public import AVenhance.Statements.Construction.IsAdmissibleStream
public import AVenhance.Statements.Construction.StreamVel
import AVenhance.Infra.Construction.StreamAdmissible

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Uniform Lipschitz hypothesis of the `flow`, for the velocity of an admissible stream. -/
theorem IsAdmissibleStream.vel_lipschitz {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) :
    ∃ L : ℝ, ∀ t x y, ‖streamVel φ t x - streamVel φ t y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, _, hL⟩ := Infra.Flow.exists_global_spatial_lipschitz
    (Infra.Construction.smoothPeriodic_streamVel h)
  exact ⟨L, hL⟩

end AVenhance
