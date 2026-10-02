-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Ingredients.HatZetaML

/-! Statement file: `hatXiML` (Ingredients).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

noncomputable section

namespace AVenhance

open Homogenization
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `ξ̂_{m,l} = ξ̂_{m,0}(· - l τ''_m)` (1321). -/
def hatXiML (m : ℕ) (l : ℤ) : ℝ → ℝ := shiftCutoff (I.hatXi m) (l * tauPP β I.Λ m)

end Ingredients
end AVenhance
