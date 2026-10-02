-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.FrozenShearDiffusionOperator
public import AVenhance.Infra.Section5.CorrectorDiffusionDivergence
public import AVenhance.Infra.Section5.ResidualAlgebra
public import AVenhance.Infra.Section5.ResidualR46
public import AVenhance.Infra.Section5.OddSupportTsum
public import AVenhance.Infra.Section5.LeftJacobian.Assembly
public import AVenhance.Infra.Section5.LeftJacobian.Regroup

/-! Algebraic assembly of the material and diffusion expansions into the named Section 5.1
residual (corrected form).

`LeftJacobian.variantA_residual_identity_sel_of_expansions` assembles the literal-name split
the corrected formulation (36); `LeftJacobian.residualIdentityPlus_of_sel` regroups it into (38), and
`LeftJacobian.residualIdentity_iff_plus` identifies (38) with the named-slot `residualIdentity` (ten slot
names; `twistie3 = twistie3⁺ + 𝓜`). The earlier assembly (with `𝒥 : ∇Ḡ` and the old `normie3`)
was removed. -/

@[expose] public section

