-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section3.UShear

/-! Statement file: `zetaProd` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- The coefficient `ζ̂_{m,l_k}(s) ζ_{m,k}(s)` in `e.parabcorr.k`, `e.Chimk.formula`, `e.psi.m`. -/
def zetaProd (m : ℕ) (k : ℤ) (s : ℝ) : ℝ :=
  I.hatZetaML m (lIdx β I.Λ m k) s * I.zetaMK m k s

end Ingredients
end AVenhance
