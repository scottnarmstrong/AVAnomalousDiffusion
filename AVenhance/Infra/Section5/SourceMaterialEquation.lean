-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.FlowAverageFluxIdentity
public import AVenhance.Infra.Section5.StreamFlowPiola
public import AVenhance.Infra.Section5.FrozenHmSourceTelescope
public import AVenhance.Infra.Section5.SourceErrors
public import AVenhance.Infra.Section5.TEquationRegularity
public import AVenhance.Infra.Section5.LeftJacobian.SourceMaterial

/-! The source transport assembly (corrected form).

The assembly `DT + DH = div(𝒥 Ḡ + d + e)` fails for the `sMat`/`Amnr`; the correct statement is
`LeftJacobian.variantA_source_material_equation`: `DT + DH = div(V_tr + d + e)` with the Piola transport
flux `V_tr = Σ_l ξ̂_l [κ F_l + F_lᵀ P F_l] ∇T` (`LeftJacobian.transportFluxPlus`, the corrected formulation (34)) and
the §9.4 `d = sourceErrorD` (`= LeftJacobian.sourceErrorDPlus` by `rfl`). -/

@[expose] public section

