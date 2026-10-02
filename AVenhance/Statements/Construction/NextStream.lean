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
public import AVenhance.Statements.Construction.NextStreamTerm

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `e.psi.recursion` (1436-1455), second form: `φ_m := φ_{m-1} + Σ_{k ∈ ℤ} (term_k)`.
The `tsum` over `k ∈ ℤ` is not junk: for each `(t,x)` only finitely many `k` contribute
(`nextStream_summable`). -/
def nextStream (m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) : ℝ → Vec 2 → ℝ :=
  fun t x => φ t x + ∑' k : ℤ, I.nextStreamTerm m φ hφ t x k

end Ingredients

end AVenhance
