-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.Contracts.TermSourcesFlux
public import AVenhance.Infra.Section5.Contracts.TermSourcesCutoff
public import AVenhance.Infra.Section5.Contracts.TermSourcesTiny
public import AVenhance.Infra.Section5.Contracts.TermSourcesTwistie1

/-! # Big-bound/step-down part (ii) term source contracts (facade `TermSourcesAll`)

Producers, abstract amplitude `B` (big-bound estimate: `B = ‖θ₀‖`; Step-down part (ii): `B = S`), each conditional on input
contracts at the same amplitude:
* `cutoff1Source_contract` (`TermSourcesCutoff`), `twistie3Source_contract`,
  `normie1Source_contract`, `normie2Source_contract` (`TermSourcesFlux`) — `L²` source bounds;
* `twistie1HMinusSource_contract` (`TermSourcesTwistie1`) and `tinyHMinusSource_contract`
  (`TermSourcesTiny`) — negative-norm source bounds.
The centered slots are in `Contracts/TermCentered.lean`. -/

@[expose] public section

