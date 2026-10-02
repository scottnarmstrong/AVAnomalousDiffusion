-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.Amnr.TemperatureCoefficientStepBounds

/-! Literal source coefficients through the terminal permitted scale. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

def amnrSourceRatioConstant (β C : ℝ) : ℝ :=
  1 + C + Section3.kappaPrimeEndpointExpratConstant β

theorem amnrSourceRatioConstant_nonneg {β C : ℝ} (I : AVenhance.Ingredients β) (hC : 0 ≤ C) :
    0 ≤ amnrSourceRatioConstant β C := by
  have ht : 0 ≤ Section3.kappaPrimeEndpointExpratConstant β := by
    have hq : 0 ≤ AVenhance.q β := le_trans (by norm_num)
      (AVenhance.Infra.Ingredients.one_lt_q I.one_lt_beta I.beta_lt).le
    unfold Section3.kappaPrimeEndpointExpratConstant
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by unfold AVenhance.Infra.Ingredients.supergeoConstant; positivity) _)
  dsimp [amnrSourceRatioConstant]
  positivity

end AVenhance.Infra.Section4
