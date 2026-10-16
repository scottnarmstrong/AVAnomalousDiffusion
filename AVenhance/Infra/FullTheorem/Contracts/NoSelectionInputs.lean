-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

import AVenhance.Infra.FullTheorem.NoSelectionInputs.TwoDiffusivity
import AVenhance.Infra.FullTheorem.NoSelectionInputs.Cosine
import AVenhance.Infra.FullTheorem.NoSelectionInputs.VelGrad
import AVenhance.Infra.FullTheorem.NoSelectionInputs.A0Core
public import AVenhance.Infra.FullTheorem.Integration.NoSelectionInputs

/-! # Small inputs of the no-selection argument, proved

* `twoDiffusivity_contract`: comparison of two diffusivities with the same drift;
* `cosineDatum_contract`: facts about the cosine data;
* `velGrad_contract`: gradient bound on the drift of the stream sequence;
* `a0Core_contract`: the main theorem at ingredient level (for the given limit field). -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem

theorem twoDiffusivity_contract : TwoDiffusivityContract :=
  NoSelectionInputs.twoDiffusivity

theorem cosineDatum_contract : CosineDatumContract :=
  NoSelectionInputs.cosineDatum

theorem velGrad_contract (β C₀ : ℝ) : VelGradContract β C₀ :=
  NoSelectionInputs.velGrad β C₀

theorem a0Core_contract (β C₀ : ℝ) (hβ : 6 / 5 ≤ β) : A0CoreContract β C₀ :=
  NoSelectionInputs.a0Core β C₀ hβ

end AVenhance.Infra.FullTheorem.Contracts
