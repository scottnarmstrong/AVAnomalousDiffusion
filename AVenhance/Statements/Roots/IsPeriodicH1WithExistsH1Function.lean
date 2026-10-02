-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.IsWeakSolution
public import AVenhance.Proofs.Roots.IsPeriodicH1WithExistsH1Function

/-! Statement file: `IsPeriodicH1With.exists_h1Function` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace AVenhance

/-- Bridge to CoarseGraining's `H1Function` on the open unit cube. -/
theorem IsPeriodicH1With.exists_h1Function {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : IsPeriodicH1With u Du) :
    ∃ v : H1Function unitCube, v.toFun = u ∧ v.grad = Du := by
  exact AVenhance.Proofs.IsPeriodicH1With.exists_h1Function h

end AVenhance
