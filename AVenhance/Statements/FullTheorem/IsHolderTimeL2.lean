-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.IsWeakSolution
public import AVenhance.Statements.Roots.IsHolderClass
public import AVenhance.Statements.Roots.IsDivFree
public import AVenhance.Statements.Roots.IsPeriodicH1With
public import AVenhance.Statements.Roots.TimeCube
public import AVenhance.Statements.Roots.IsTestFunction
public import AVenhance.Statements.Roots.SpaceTimeGradNormSq
public import AVenhance.Statements.Section3.PermissibleSet
public import AVenhance.Statements.Section4.KappaSeq
public import AVenhance.Statements.Section4.IsClassicalSol
public import AVenhance.Statements.Section4.IsThetaAnalytic
public import AVenhance.Statements.Section4.MTheta0
public import AVenhance.Statements.Construction.IsStreamSeq
public import AVenhance.Statements.Construction.StreamVel

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
