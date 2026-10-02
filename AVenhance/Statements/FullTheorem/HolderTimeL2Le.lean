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
public import AVenhance.Statements.FullTheorem.IsHolderTimeL2

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance
/-- `‖θ‖_{C^{0,μ}([0,1];L²)} ≤ H`, the norm being `sup_{t∈[0,1]} ‖θ(t)‖_{L²}` plus the
`μ`-Hölder seminorm. -/
def HolderTimeL2Le (μ H : ℝ) (θ : ℝ → Vec 2 → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ t)) ∧
  ∃ A B : ℝ, A + B ≤ H ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (θ t)) ≤ A) ∧
    IsHolderTimeL2 μ B θ

end AVenhance
