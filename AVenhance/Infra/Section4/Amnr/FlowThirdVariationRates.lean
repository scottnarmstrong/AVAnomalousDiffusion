-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Quantitative actual third spatial flow operators. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4

instance FlowThirdVariationRates.amnrBilinearNorm :
    NormedAddCommGroup (Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2) := inferInstance
instance FlowThirdVariationRates.amnrBilinearSpace :
    NormedSpace ℝ (Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2) := inferInstance

end AVenhance.Infra.Section4
