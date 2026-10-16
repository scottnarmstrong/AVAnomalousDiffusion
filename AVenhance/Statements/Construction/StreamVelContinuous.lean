-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

import AVenhance.Infra.Construction.StreamAdmissible
public import AVenhance.Statements.Construction.IsAdmissibleStream
public import AVenhance.Statements.Construction.StreamVel

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Joint continuity hypothesis of the `flow`, for the velocity of an admissible stream. -/
theorem IsAdmissibleStream.vel_continuous {φ : ℝ → Vec 2 → ℝ} (h : IsAdmissibleStream φ) :
    Continuous (fun p : ℝ × Vec 2 => streamVel φ p.1 p.2) :=
  (Infra.Construction.smoothPeriodic_streamVel h).smooth.continuous

end AVenhance
