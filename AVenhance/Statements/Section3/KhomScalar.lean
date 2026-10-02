-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.Khom

/-! Statement file: `KhomScalar` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- The scalar `a` with `K̄^κ_m = a I` (line 2994): the `(1,1)` entry. That `K̄` is scalar and
`a > 0` is the theorem `Khom_eq_scalar`; the abuse of notation of the source is `KhomScalar`. -/
def KhomScalar (κ : ℝ) (m : ℕ) : ℝ := I.Khom κ m 0 0

end Ingredients
end AVenhance
