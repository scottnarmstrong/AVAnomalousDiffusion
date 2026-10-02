-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.TUpgradeConsumersProfile

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem TUpgradeConsumersTraceFrequency.iterateSpatialWord_eq_classicalWordDerivative
    (w : List (Fin 2)) (f : Vec 2 → ℝ) :
    iterateSpatialWord w f = classicalWordDerivative w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [iterateSpatialWord, classicalWordDerivative, ih]

end AVenhance.Infra.Section4
