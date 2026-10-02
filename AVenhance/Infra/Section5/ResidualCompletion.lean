-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.ResidualMaterialBridge
public import AVenhance.Infra.Section5.NamedDiffusionExpansion
public import AVenhance.Infra.Section5.ResidualAssembly
public import AVenhance.Infra.Section5.ResidualR46
public import AVenhance.Infra.Section5.DivergenceLinearity
public import AVenhance.Infra.Section5.LeftJacobian.Residual

/-! Source-specific completion of the Section 5.1 ansatz residual (corrected form).

`FrozenResidualPointwiseData` is the corrected-form pointwise calculus record
`LeftJacobian.ResidualPointwiseData`, and `frozen_source_residual_identity` proves the named-slot
`sourceResidualIdentity` (ten slot names, §9.4 `sourceErrorD`) from it
(`LeftJacobian.frozen_variantA_source_residual_identity`). -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Pointwise calculus data for the residual proof (corrected form). -/
abbrev FrozenResidualPointwiseData
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) : Type :=
  LeftJacobian.ResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT t ht x ρ hρ

/-- The complete source-form Section 5.1 residual from the `T`-iterate and the
pointwise calculus data (corrected form, ten slot names). -/
theorem frozen_source_residual_identity
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (R : FrozenResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT t ht x ρ hρ) :
    sourceResidualIdentity I hΦ m κm κprev T t x :=
  LeftJacobian.frozen_variantA_source_residual_identity I hΦ m hm κm κprev θ₀ θprev T hT
    t ht x ρ hρ R

end AVenhance.Infra.Section5

end
