-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section4.Amnr.DriftCommutatorPairing

/-! Absolute time-integrated spatial pairings and the actual product measure. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- The physical finite-time product is absolutely continuous on the full
positive-time domain, even when the terminal time is zero. -/
theorem amnr_time_cell_product_absolutelyContinuous {T : ℝ} (hT : 0 ≤ T) :
    (volume.restrict (uIoc (0 : ℝ) T)).prod (volume.restrict AVenhance.unitCube) ≪
      volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (Vec 2))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
  apply Measure.absolutelyContinuous_of_le
  apply Measure.restrict_mono_set
  intro z hz
  rw [uIoc_of_le hT] at hz
  exact ⟨hz.1.1, mem_univ z.2⟩

theorem amnr_time_cell_product_absolutelyContinuous_closed {T : ℝ} (hT : 0 ≤ T) :
    (volume.restrict (uIoc (0 : ℝ) T)).prod (volume.restrict AVenhance.unitCube) ≪
      volume.restrict (Ici (0 : ℝ) ×ˢ (univ : Set (Vec 2))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ (Vec 2)]
  apply Measure.absolutelyContinuous_of_le
  apply Measure.restrict_mono_set
  intro z hz
  rw [uIoc_of_le hT] at hz
  exact ⟨hz.1.1.le, mem_univ z.2⟩

end AVenhance.Infra.Section4
