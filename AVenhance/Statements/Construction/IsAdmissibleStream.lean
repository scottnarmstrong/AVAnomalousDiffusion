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
public import AVenhance.Statements.Construction.BarNorm

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

/-- Admissible stream functions of the construction (source 1398-1414, 1457-1461): `C^∞`
in `(t,x)` and `ℤ × ℤ²`-periodic (`φ (t + n) (x + k) = φ t x`). The normalization
`⟨φ_m⟩ = 0` of `e.phim.bm` is deliberately not part of admissibility (see proposal). -/
def IsAdmissibleStream (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry φ) ∧
  ∀ (n : ℤ) (k : Fin 2 → ℤ) (t : ℝ) (x : Vec 2),
    φ (t + (n : ℝ)) (x + latticeShift k) = φ t x

end AVenhance
