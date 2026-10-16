-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Statements.Section4.Amnr
public import AVenhance.Statements.Section3.QMNR
public import AVenhance.Statements.Section4.VecDiv

/-! Public statement. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

noncomputable section

namespace AVenhance

namespace Ingredients
variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- `H̃_{m,r} := ∇ · ∑_{n=0}^{N_*-1} 𝐀_{m,n,r} 𝐪_{m,n,r+1}`, `e.H.mr.def` (4178), with
`∇·(𝐀𝐪) = ∂_i(𝐀^{ijk} 𝐪^{jk})`. -/
def Hmr (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ) (Tm1 : ℝ → Vec 2 → ℝ) (r : ℕ) (t : ℝ)
    (x : Vec 2) : ℝ :=
  vecDiv (fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
    I.Amnr hΦ m κm n Tm1 r t y i j k * I.qMNR κm m n (r + 1) t j k) x

end Ingredients
end AVenhance
