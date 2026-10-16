-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.GradMatrix
public import AVenhance.Statements.Section4.XFlowInv
public import AVenhance.Statements.Section4.XFlow

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `∇X_{m-1,l} ∘ X⁻¹_{m-1,l}` (`e.sm`, `e.chainrule.Tm1`): the matrix whose `(i,j)` entry is
`∂_i X^j_{m-1,l}` evaluated at `X⁻¹_{m-1,l}(t,x)`; row vectors for vector-valued functions and
column vectors for gradients, exactly the convention of `e.gradcorrmatrix` (`gradMatrix`), so
`∇(T∘X_l)∘X_l⁻¹ = (∇X_l∘X_l⁻¹) ∇T`. -/
def flowGrad (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  gradMatrix (fun y => I.xFlow hΦ m l t y) (I.xFlowInv hΦ m l t x)

end Ingredients
end AVenhance
