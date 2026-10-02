-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.SourceMaterialEquation
public import AVenhance.Infra.Section5.FrozenAnsatzMaterial
public import AVenhance.Infra.Section5.TransportIdentities
public import AVenhance.Infra.Section5.PulledGradientMaterial
public import AVenhance.Infra.Section5.OddSupportTsum
public import AVenhance.Infra.Section5.MatrixFluxProduct
public import AVenhance.Infra.Section5.MatrixTransport
public import AVenhance.Infra.Section5.LeftJacobian.AnsatzMaterial

/-! The ansatz material equation (corrected form).

The ansatz material expansion with an arbitrary source right-hand side is
`LeftJacobian.variantA_ansatz_material_equation_of_source`. A source of the form
`div(𝒥 Ḡ + d + e)` would not hold for `sMat`/`Amnr`. -/

@[expose] public section

