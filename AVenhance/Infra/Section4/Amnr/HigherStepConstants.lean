-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.Amnr.HigherVelocitySourceStep

/-! Positivity and finite spatial uniformity of the higher source-step constants. -/

@[expose] public section

noncomputable section
namespace AVenhance.Infra.Section4

theorem amnrHigherVelocityStepConstant_nonneg {β K : ℝ} (I : AVenhance.Ingredients β)
    (hK : 0 ≤ K) (n k : ℕ) : 0 ≤ amnrHigherVelocityStepConstant I K n k := by
  have hD := amnrHigherFastConstant_one_le (K := K) I
  have hR := amnrNormalOrderConstant_one_le (N := AVenhance.Nstar β - 1) hK
    (AVenhance.Nstar β - 1)
  dsimp [amnrHigherVelocityStepConstant]
  positivity

theorem amnrHigherVelocityStepConstant_mono_spatial {β K : ℝ} (I : AVenhance.Ingredients β)
    (hK : 0 ≤ K) (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    amnrHigherVelocityStepConstant I K n k ≤ amnrHigherVelocityStepConstant I K n l := by
  have hD := amnrHigherFastConstant_one_le (K := K) I
  have hR := amnrNormalOrderConstant_one_le (N := AVenhance.Nstar β - 1) hK
    (AVenhance.Nstar β - 1)
  dsimp [amnrHigherVelocityStepConstant]
  simp only [Nat.cast_mul, Nat.cast_pow]
  gcongr
  exact_mod_cast (show 1 ≤ n + 1 by omega)

end AVenhance.Infra.Section4
