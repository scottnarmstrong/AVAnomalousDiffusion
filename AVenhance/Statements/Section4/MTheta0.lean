-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.Epsilon
public import AVenhance.Statements.Ingredients.Gamma

/-! Public statement. -/

@[expose] public section

open Filter Topology

noncomputable section

namespace AVenhance

/-- `m_{θ₀} := min { m ∈ ℕ : m ≥ 2, ε_{m-1}^{1+γ/2} ≤ R_{θ₀} }` (`e.mtheta0.def` 8037-8041;
`e.m.restriction` 7010).  The set is nonempty for `R > 0` (`mTheta0_isLeast`). -/
def mTheta0 (β : ℝ) (Λ : ℕ) (R : ℝ) : ℕ :=
  sInf {m : ℕ | 2 ≤ m ∧ epsilon β Λ (m - 1) ^ (1 + gamma β / 2) ≤ R}

end AVenhance
