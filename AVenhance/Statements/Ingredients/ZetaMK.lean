-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.Ingredients

/-! Statement file: `zetaMK` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `ζ_{m,k}`, `e.zeta.mk.def` (1246). -/
def zetaMK (m : ℕ) (k : ℤ) : ℝ → ℝ := scaledCutoff I.zeta (tau β I.Λ m) k

end Ingredients
end AVenhance
