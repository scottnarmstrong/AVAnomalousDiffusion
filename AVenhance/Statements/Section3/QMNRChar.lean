-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

import AVenhance.Proofs.Section3.QMNRChar
public import AVenhance.Statements.Section3.QMNR

/-! Public statement. -/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β)

/-- `qMNR` is the family characterized in `e.q.mnr.def` (existence and uniqueness), with the
period corrected to `4τ_m`.  Required before FILE 19 lands (source-characterized rule). -/
theorem qMNR_char (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) (n : ℕ) :
    (∀ t, I.qMNR κ m n 0 t = I.jMN κ m n t - timeAvgMat (I.jMN κ m n)) ∧
    (∀ r, Function.Periodic (I.qMNR κ m n r) (4 * tau β I.Λ m)) ∧
    (∀ r, 1 ≤ r → timeAvgMat (I.qMNR κ m n r) = 0) ∧
    (∀ (r : ℕ) (t : ℝ) (i j : Fin 2),
      HasDerivAt (fun s => I.qMNR κ m n (r + 1) s i j) (-(I.qMNR κ m n r t i j)) t) ∧
    ∀ q' : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ,
      (∀ t, q' 0 t = I.jMN κ m n t - timeAvgMat (I.jMN κ m n)) →
      (∀ r, Function.Periodic (q' r) (4 * tau β I.Λ m)) →
      (∀ r, 1 ≤ r → timeAvgMat (q' r) = 0) →
      (∀ (r : ℕ) (t : ℝ) (i j : Fin 2), HasDerivAt (fun s => q' (r + 1) s i j) (-(q' r t i j)) t) →
      ∀ r, q' r = I.qMNR κ m n r := by
  exact AVenhance.Proofs.Ingredients.qMNR_char I κ hκ m hm n

end Ingredients
end AVenhance
