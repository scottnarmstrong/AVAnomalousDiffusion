-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.IsCorrectorSol
public import AVenhance.Proofs.Section3.KhomEqScalar

/-! Statement file: `Khom_eq_scalar` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `Khom` is a scalar matrix with positive scalar (source line 2994: "it follows that `K̄^κ_m`
is a scalar matrix", "the positive scalar constant `a`"). -/
theorem Khom_eq_scalar (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) :
    I.Khom κ m = I.KhomScalar κ m • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧ 0 < I.KhomScalar κ m := by
  exact AVenhance.Proofs.Ingredients.Khom_eq_scalar I κ hκ m hm

end Ingredients
end AVenhance
