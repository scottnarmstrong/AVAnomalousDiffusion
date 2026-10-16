-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.Nstar

/-! Public statement. -/

@[expose] public section

noncomputable section

namespace AVenhance

/-- The truncation index `N_*/2` of `e.Hm.def`, `e.dm` and `p.Amnr.bounds` (source `\nicefrac{N_*}{2}`),
read as `⌊(N_*-1)/2⌋` (`N_*` need not be even, and the derivative budget of
`p.Hm.bounds` Step 1 fails at the top index for `⌊N_*/2⌋` when `N_*` is even). The sum defining
`H̃_m` runs over `r = 0,…,Jcut-1` and the remainder in `d_m` is `A_{m,n,Jcut}`. -/
def Jcut (β : ℝ) : ℕ := (Nstar β - 1) / 2

end AVenhance
