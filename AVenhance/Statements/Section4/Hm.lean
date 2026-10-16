-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section4.Hmr
public import AVenhance.Statements.Section4.Jcut

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `H̃_m := ∑_{r} H̃_{m,r}`, `e.Hm.def` (4241), summed over `r = 0,…,Jcut β - 1`. -/
def Hm (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (Tm1 : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑ r ∈ Finset.range (Jcut β), I.Hmr hΦ m κm Tm1 r t x

end Ingredients
end AVenhance
