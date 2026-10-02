-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.Amnr.TemperatureBoundaryRegularity

/-! Spatial words of the actual temperature: diffusion and periodicity. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance

theorem amnrSpaceWord_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (w : List (Fin 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrSpaceWord w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact contDiff_pi.mp (amnr_energy_gradient_smooth ih) i

theorem amnrSpaceWord_periodic {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) (w : List (Fin 2)) :
    IsZ2Periodic (amnrSpaceWord w f) := by
  rw [amnrSpaceWord_eq_iteratedFDeriv hf w]
  intro k x
  exact congrArg (fun L => L (amnrSpatialDirections w)) (iteratedFDeriv_z2Periodic hp w.length k x)

end AVenhance.Infra.Section4
