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
public import AVenhance.Statements.FullTheorem.HolderTimeL2Le
public import AVenhance.Statements.FullTheorem.IsTransportWeakSolution

/-! # Statement of Lemma r.LeBron (`lebron_step`)

`LebronStepStatement β C₀` is the proposition of `AVenhance.lebron_step`, with the
binders `(β C₀ : ℝ)` turned into arguments. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- The conclusion of Lemma r.LeBron, `AVenhance.lebron_step (β C₀ : ℝ)`. -/
def LebronStepStatement (β : ℝ) (C₀ : ℝ) : Prop :=
    ∃ μ C : ℝ, 0 < μ ∧
      ∀ I : Ingredients β, I.Czeta ≤ C₀ → I.Cxi ≤ C₀ → I.Chat ≤ C₀ → C ≤ (I.Λ : ℝ) →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsStreamSeq I Φ →
      ∀ κ : ℝ, κ ∈ permissibleSet β I.Λ →
      ∀ M : ℕ, 1 ≤ M → κ ∈ permittedInterval β I.Λ M →
      ∀ R : ℝ, 0 < R →
      ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ → MeanZeroOn unitCube θ₀ →
        IsThetaAnalytic R θ₀ →
      ∀ m : ℕ, mTheta0 β I.Λ R ≤ m → m ≤ M →
      ∀ θm θprev : ℝ → Vec 2 → ℝ,
        IsClassicalSol (streamVel (Φ m)) (I.kappaSeq κ M m) (fun _ _ => 0) θ₀ θm →
        IsClassicalSol (streamVel (Φ (m - 1))) (I.kappaSeq κ M (m - 1)) (fun _ _ => 0) θ₀ θprev →
        HolderTimeL2Le μ
          (C * epsilon β I.Λ (m - 1) ^ (delta β / 2) *
            Real.sqrt (l2NormSq θ₀ + gradNormSq (spaceGrad θ₀)))
          (fun t x => θm t x - θprev t x)

end AVenhance.Infra.FullTheorem
