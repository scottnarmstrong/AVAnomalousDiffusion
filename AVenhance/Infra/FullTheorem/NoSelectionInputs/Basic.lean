-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Roots.SpaceGrad
public import AVenhance.Statements.Roots.UnitCube
public import Homogenization.Sobolev.WeakDerivatives

/-! # Smoothness of partial derivatives (shared helpers of the no-selection inputs) -/

@[expose] public section

open Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSelectionInputs

open AVenhance

theorem smoothPartial {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x v) :=
  (hψ.fderiv_right (by simp)).clm_apply contDiff_const

theorem contDiff_spaceGrad_coord {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad ψ x i) :=
  smoothPartial hψ (basisVec i)

theorem contDiff_spaceGrad {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (spaceGrad ψ) :=
  contDiff_pi.2 (contDiff_spaceGrad_coord hψ)

end AVenhance.Infra.FullTheorem.NoSelectionInputs
