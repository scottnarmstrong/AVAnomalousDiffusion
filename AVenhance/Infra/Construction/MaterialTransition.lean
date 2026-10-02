-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Construction.MaterialComposition

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.Construction

theorem MaterialTransition.iteratedTimeDerivative_contDiff_local {q : ℝ → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (ell : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedTimeDerivative ell q) := by
  induction ell with
  | zero => exact hq
  | succ ell ih =>
      exact (contDiff_infty_iff_deriv.mp ih).2

end AVenhance.Infra.Construction

end
