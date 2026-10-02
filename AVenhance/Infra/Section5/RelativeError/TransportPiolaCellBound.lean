-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.RelativeError.TransportFlowCellIntegral
public import AVenhance.Infra.Section5.RelativeError.TransportVectorBounds
public import AVenhance.Infra.Classical.PeriodicCalculus
public import AVenhance.Infra.Classical.TimeEnergy
public import AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import AVenhance.Statements.Roots.SpaceGrad

/-! # RelativeError: the transported Piola vector has controlled cell L² norm -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus

theorem TransportPiolaCellBound.vecNorm_le_sqrt_vecNormSq (v : Vec 2) :
    ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  have hcomponent := Homogenization.sq_apply_le_vecNormSq v i
  have hsq : (‖v i‖) ^ 2 ≤ (Real.sqrt (vecNormSq v)) ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Homogenization.vecNormSq_nonneg v)] using hcomponent
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp hsq

end AVenhance.Infra.Section5.RelativeError

end
