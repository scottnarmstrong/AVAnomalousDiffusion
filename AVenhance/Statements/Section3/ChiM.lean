-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.ChiMK

/-! Statement file: `chiM` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `Χ^κ_m := ∑_{k ∈ ℤ} ξ_{m,k} Χ^κ_{m,k}`, `e.Chim` (label 2909). -/
def chiM (κ : ℝ) (m : ℕ) (t : ℝ) (x : Vec 2) : Vec 2 :=
  ∑' k : ℤ, I.xiMK m k t • I.chiMK κ m k t x

end Ingredients
end AVenhance
