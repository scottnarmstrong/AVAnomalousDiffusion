-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.Contracts.TermCenteredTwistie4
public import AVenhance.Infra.Section5.Contracts.TermCenteredTwistie5
public import AVenhance.Infra.Section5.Contracts.TermCenteredNormie3

/-! # Centered negative-norm source contracts of `twistie4`, `twistie5`, `normie3`

Facade of the producers

* `twistie4CenteredSource_contract` (`TermCenteredTwistie4.lean`),
* `twistie5CenteredSource_contract` (`TermCenteredTwistie5.lean`),
* `normie3CenteredSource_contract` (`TermCenteredNormie3.lean`),

in the abstract-amplitude producer form of `Contracts/TermFluxes.lean`.  Inputs at the same
amplitude `B`: `TPositiveJetsContract`, `TGradientContract`, and (the ergodic main term multiplies
`ε_m` by space-time `L²` norms of `∇(∇(T∘X)∘X⁻¹)`, which slice-only jets cannot supply)
`FirstOrderGradJetContract`.

In the corrected form, `normie3 = Σ_k ξ_k F_kᵀ (𝒥 - C⁰_k) : ∇G_k` has a fast factor of exact
zero cell mean, and `normie3CenteredSource_contract` (`TermCenteredNormie3.lean`) produces
`Normie3CenteredSourceContract` with the same three inputs. (Pre-, the fast factor `𝒥 - C_k∘X⁻¹`
had slow mean `-σ(∇X⁻¹ - I)⟨ψ ∇Χ⟩ ≈ κ_{m-1}` and the contract was not producible.) -/

@[expose] public section

