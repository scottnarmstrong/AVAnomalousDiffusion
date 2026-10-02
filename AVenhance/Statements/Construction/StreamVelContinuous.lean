-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.FlowDefs.FlowInv
public import AVenhance.Statements.Section3.SigmaMat
public import AVenhance.Statements.Ingredients.HatZetaML
public import AVenhance.Statements.Ingredients.ZetaMK
public import AVenhance.Statements.Ingredients.Psi
public import AVenhance.Statements.Ingredients.LIdx
public import AVenhance.Statements.Roots.IsHolderClass
public import AVenhance.Statements.Roots.IsDivFree
public import AVenhance.Infra.Flow.SmoothField
public import AVenhance.Infra.Ingredients.LIdxConsequences
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import AVenhance.Infra.Construction.StreamAdmissible

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
