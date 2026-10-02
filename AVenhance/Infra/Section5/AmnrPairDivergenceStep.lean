-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.AmnrMaterialStep

/-! The divergence form of the per-index `A`/`q` transport step. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance
open Homogenization
open Filter
open scoped Topology

variable {β : ℝ} (I : Ingredients β)
variable {Φ : ℕ → ℝ → Vec 2 → ℝ}

def AmnrPairDivergenceStep.amnrPairFlux (A : ST → Fin 2 → Fin 2 → Fin 2 → ℝ)
    (q : ℝ → Fin 2 → Fin 2 → ℝ) (j k : Fin 2) : ST → Vec 2 :=
  fun z i => A z i j k * q z.1 j k

end AVenhance.Infra.Section5

end
