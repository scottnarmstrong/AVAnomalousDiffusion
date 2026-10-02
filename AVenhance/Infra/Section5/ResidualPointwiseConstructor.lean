-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import AVenhance.Infra.Section5.ResidualFluxRegularity
public import AVenhance.Infra.Section5.HmBaseFluxIdentity
public import AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import AVenhance.Infra.Section5.ClassicalRegularity
public import AVenhance.Infra.Section5.SMatRegularity
public import AVenhance.Infra.Section5.SourceErrors
public import AVenhance.Infra.Section5.LeftJacobian.PulledFluxSmooth
public import AVenhance.Infra.Section5.Terms.R46IteratesRegularity
public import AVenhance.Infra.Section4.TIterateSmooth

/-! Construct the residual calculus data from the classical iterates,
their actual AMNR regularity, and the smooth flow. -/

@[expose] public section

noncomputable section

open Filter Homogenization
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace AVenhance.Infra.Section5

open AVenhance AVenhance.Infra.Section4

abbrev ResidualPointwiseConstructor.residualPositiveDomain : Set (ℝ × Vec 2) :=
  Set.Ioi (0 : ℝ) ×ˢ Set.univ

theorem ResidualPointwiseConstructor.residual_Gslice_smooth {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (l : ℤ) :
    ContDiff ℝ ∞ (G I hΦ m T l t) := by
  have hcoord (i : Fin 2) : ContDiffOn ℝ ∞
      (fun p : ℝ × Vec 2 => G I hΦ m T l p.1 p.2 i)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    Integration.transportedGrad_contDiffOn I hΦ m l hT i
  have hembed : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
  apply contDiff_pi.mpr
  intro i
  have hmaps : Set.MapsTo (fun x : Vec 2 => (t, x)) Set.univ
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro y _
    exact ⟨ht, Set.mem_univ _⟩
  have hcomp := (hcoord i).comp hembed.contDiffOn hmaps
  exact contDiffOn_univ.mp (by simpa [Function.comp_def] using hcomp)

theorem ResidualPointwiseConstructor.residual_Gbar_slice_smooth {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (Gbar I hΦ m T t) := by
  let S := (I.hatXiML_support_finite hm t).toFinset
  have hrep : Gbar I hΦ m T t = fun x =>
      ∑ l ∈ S, I.hatXiML m l t • G I hΦ m T l t x := by
    funext x
    exact Gbar_eq_finite_support I hΦ m hm T t x
  rw [hrep]
  apply ContDiff.sum
  intro l hl
  have hc : ContDiff ℝ ∞ (fun _ : Vec 2 => I.hatXiML m l t) := contDiff_const
  exact hc.smul (ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m T hT ht l)

theorem ResidualPointwiseConstructor.residual_Gbar_eq_source_flowAverage {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) (hT : ContDiff ℝ 1 (T t)) :
    Gbar I hΦ m T t x = ∑' l : ℤ,
      I.hatXiML m l t •
        ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)) := by
  apply tsum_congr
  intro l
  have hG := G_eq_flowGrad_mulVec I hΦ m T l t x
    (hT.differentiable (by norm_num) x).hasFDerivAt
    ((xFlow_spatial_contDiff_two I hΦ m l t).differentiable
      (by norm_num) (I.xFlowInv hΦ m l t x)).hasFDerivAt
    (by
      let b := streamVel (Φ (m - 1))
      let F := flow b (hΦ.adm_pred m).vel_continuous
        (hΦ.adm_pred m).vel_lipschitz
      have hF : IsFlow b F := flow_isFlow b
        (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
      let s := (l : ℝ) * tauPP β I.Λ m
      change F t (F s x t) s = x
      calc
        F t (F s x t) s = F t x t :=
          Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t
        _ = x := hF.1 x t)
  simpa [Gbar, smul_eq_mul] using congrArg
    (fun z : Vec 2 => I.hatXiML m l t • z) hG

theorem ResidualPointwiseConstructor.residual_time_hasDerivAt {F : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) ResidualPointwiseConstructor.residualPositiveDomain)
    (ht : 0 < t) :
    HasDerivAt (fun s => F s x)
      (fderiv ℝ (Function.uncurry F) (t, x) (1, 0)) t := by
  have hp : (t, x) ∈ ResidualPointwiseConstructor.residualPositiveDomain := by simp [ResidualPointwiseConstructor.residualPositiveDomain, ht]
  have hAt := hF.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have hfun : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (t, x)) (t, x) :=
    (hAt.differentiableAt (by simp)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => (s, x)) (1, (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  simpa [Function.uncurry, Function.comp_def] using
    hfun.comp_hasDerivAt t hpath

theorem ResidualPointwiseConstructor.residual_slice_hasFDerivAt {F : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2} {L : Vec 2 →L[ℝ] ℝ}
    (hF : ContDiffAt ℝ 1 (Function.uncurry F) (t, x))
    (hL : L = (fderiv ℝ (Function.uncurry F) (t, x)).comp
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2)))) :
    HasFDerivAt (F t) L x := by
  have hfun : HasFDerivAt (Function.uncurry F)
      (fderiv ℝ (Function.uncurry F) (t, x)) (t, x) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hpath : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hcomp := hfun.comp x hpath
  simpa [Function.uncurry, Function.comp_def, hL] using hcomp

theorem ResidualPointwiseConstructor.residual_slice_hasFDerivAt_canonical {F : ℝ → Vec 2 → ℝ}
    {t : ℝ} {x : Vec 2}
    (hF : ContDiffAt ℝ 1 (Function.uncurry F) (t, x)) :
    HasFDerivAt (F t) (fderiv ℝ (F t) x) x := by
  have huncurry := (hF.differentiableAt (by simp)).hasFDerivAt
  have hpath : HasFDerivAt (fun y : Vec 2 => (t, y))
      ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))) x := by
    exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hslice := huncurry.comp x hpath
  exact hslice.differentiableAt.hasFDerivAt

theorem ResidualPointwiseConstructor.residual_matrixMulVec_contDiff {n : ℕ}
    {M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : Vec 2 → Vec 2}
    (hM : ContDiff ℝ n M) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun x => (M x).mulVec (v x)) := by
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ n (fun x => ∑ j : Fin 2, M x i j * v x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.mp ((contDiff_pi.mp hM) i)) j).mul
    (contDiff_pi.mp hv j)

theorem ResidualPointwiseConstructor.residual_vecDiv_contDiff {n : ℕ}
    {V : Vec 2 → Vec 2} (hV : ContDiff ℝ (n + 1) V) :
    ContDiff ℝ n (fun x => vecDiv V x) := by
  have hD : ContDiff ℝ n (fderiv ℝ V) := hV.fderiv_right (by simp)
  have hterm (i : Fin 2) : ContDiff ℝ n
      (fun x => (fderiv ℝ V x (basisVec i)) i) := by
    have hEval : ContDiff ℝ n (fun x => fderiv ℝ V x (basisVec i)) :=
      hD.clm_apply contDiff_const
    exact (contDiff_pi.mp hEval) i
  have hsum : ContDiff ℝ n
      (fun x => ∑ i : Fin 2, (fderiv ℝ V x (basisVec i)) i) := by
    apply ContDiff.sum
    intro i hi
    exact hterm i
  have heq : (fun x => vecDiv V x) =
      fun x => ∑ i : Fin 2, (fderiv ℝ V x (basisVec i)) i := by
    funext x
    unfold vecDiv
    apply Finset.sum_congr rfl
    intro i hi
    change fderiv ℝ (fun y => V y i) x (basisVec i) = _
    rw [fderiv_apply (hV.differentiable (by simp) x) i]
    rfl
  rw [heq]
  exact hsum

theorem ResidualPointwiseConstructor.residual_Gspatial_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    {t : ℝ} (ht : 0 ≤ t) (l : ℤ) :
    ContDiff ℝ ∞ (fun x => G I hΦ m T l t x) :=
  ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m T hT ht l

theorem ResidualPointwiseConstructor.residual_gradMatrix_contDiff {n : ℕ} {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (n + 1) F) :
    ContDiff ℝ n (fun x => gradMatrix F x) := by
  have hD : ContDiff ℝ n (fderiv ℝ F) := hF.fderiv_right (by simp)
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hEval : ContDiff ℝ n (fun x => fderiv ℝ F x (basisVec i)) :=
    hD.clm_apply contDiff_const
  have hEntry := contDiff_pi.mp hEval j
  have heq : (fun x => gradMatrix F x i j) =
      fun x => fderiv ℝ F x (basisVec i) j := by
    funext x
    rw [gradMatrix, Matrix.of_apply]
    change fderiv ℝ (fun y => F y j) x (basisVec i) = _
    rw [fderiv_apply (hF.differentiable (by simp) x) j]
    rfl
  rw [heq]
  exact hEntry

theorem ResidualPointwiseConstructor.residual_contDiffOn_slice {n : ℕ}
    {F : ℝ × Vec 2 → ℝ} (hF : ContDiffOn ℝ n F ResidualPointwiseConstructor.residualPositiveDomain)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ n (fun x => F (t, x)) := by
  let embed : Vec 2 → ℝ × Vec 2 := fun x => (t, x)
  have hembed : ContDiff ℝ n embed := by fun_prop
  have hmaps : Set.MapsTo embed Set.univ ResidualPointwiseConstructor.residualPositiveDomain := by
    intro x hx
    simp [embed, ResidualPointwiseConstructor.residualPositiveDomain, ht]
  have hcomp := hF.comp hembed.contDiffOn hmaps
  have heq : F ∘ embed = fun x => F (t, x) := rfl
  rw [heq] at hcomp
  exact contDiffOn_univ.mp hcomp

theorem ResidualPointwiseConstructor.residual_hmEndpoint_budget {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (Jcut β)) : 1 + (r + 1) ≤ Nstar β := by
  have hcut := Finset.mem_range.mp hr
  unfold Jcut at hcut
  omega

theorem ResidualPointwiseConstructor.residual_hmFlux_budget {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (Jcut β)) : 3 + r ≤ Nstar β := by
  have hcut := Finset.mem_range.mp hr
  unfold Jcut at hcut
  omega

theorem ResidualPointwiseConstructor.residual_amnrBudget_one {β : ℝ} {r : ℕ}
    (hr : r ∈ Finset.range (Jcut β)) : 1 + r ≤ Nstar β := by
  have hcut := Finset.mem_range.mp hr
  unfold Jcut at hcut
  omega

theorem ResidualPointwiseConstructor.residual_terminalBudget_one {β : ℝ}
    (hN : 1 ≤ Nstar β) : 1 + Jcut β ≤ Nstar β := by
  have h := AVenhance.Infra.Section4.Jcut_budget hN
  omega

theorem ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order {n : ℕ} {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (n + 1) f) : ContDiff ℝ n (spaceGrad f) := by
  have hD : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (by simp)
  apply contDiff_pi.mpr
  intro i
  have hEval : ContDiff ℝ n
      (fun y => fderiv ℝ f y (basisVec i)) := hD.clm_apply contDiff_const
  simpa [spaceGrad, ContinuousLinearMap.comp_zero] using hEval

theorem ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev t : ℝ) (_ht : 0 ≤ t) (T : ℕ → ℝ → Vec 2 → ℝ)
    (hprev : ContDiff ℝ 3 (T (Nstar β - 1) t))
    (hlast : ContDiff ℝ 3 (T (Nstar β) t)) :
    ContDiff ℝ 2 (fun y => iterateError I hΦ m κm κprev T t y) := by
  have hsmat := sMat_spatial_contDiff_two I hΦ m hm κm t
  have hM : ContDiff ℝ 2 (fun y =>
      I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        I.sMat hΦ m κm t y) := by
    exact (contDiff_const.sub contDiff_const).add hsmat
  have hgradPrev := ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order hprev
  have hgradLast := ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order hlast
  have hV : ContDiff ℝ 2 (fun y =>
      spaceGrad (T (Nstar β - 1) t) y - spaceGrad (T (Nstar β) t) y) := by
    exact (hgradPrev.of_le (by norm_num)).sub (hgradLast.of_le (by norm_num))
  have hmul := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hM hV
  simpa [iterateError] using hmul

theorem ResidualPointwiseConstructor.residual_sourceTail_spatial_contDiff {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (hκm : 0 < κm) (T : ℕ → ℝ → Vec 2 → ℝ)
    {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ 1 (fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) t y i j k *
        I.qMNR κm m n (Jcut β) t j k) := by
  classical
  have hN : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hbudget := ResidualPointwiseConstructor.residual_terminalBudget_one hN
  have hA (n : ℕ) (hn : n ∈ Finset.range (Nstar β))
      (i j k : Fin 2) : ContDiff ℝ 1
        (fun y => I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) t y i j k) := by
    have hreg := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT
      n (Jcut β) 1 hbudget i j k
    have hslice := ResidualPointwiseConstructor.residual_contDiffOn_slice hreg ht
    simpa using hslice
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun y => ∑ n ∈ Finset.range (Nstar β),
    ∑ j : Fin 2, ∑ k : Fin 2,
      I.Amnr hΦ m κm n (T (Nstar β)) (Jcut β) t y i j k *
        I.qMNR κm m n (Jcut β) t j k)
  apply ContDiff.sum
  intro n hn
  apply ContDiff.sum
  intro j hj
  apply ContDiff.sum
  intro k hk
  exact (hA n hn i j k).mul contDiff_const

theorem ResidualPointwiseConstructor.residual_chiSlice_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (k : ℤ) (t : ℝ) :
    ContDiff ℝ 2 (I.chiTilde hΦ m κ k t) := by
  apply contDiff_pi.mpr
  intro i
  let embed : Vec 2 → ℝ × Vec 2 := fun y => (t, y)
  have hembed : ContDiff ℝ 2 embed := by fun_prop
  have hi := (Integration.chiTilde_component_contDiff_two I hΦ m κ k i).comp hembed
  simpa [embed, Function.comp_def] using hi

theorem ResidualPointwiseConstructor.residual_Gjoint_contDiffOn {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (l : ℤ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec 2 => G I hΦ m T l z.1 z.2)
      ResidualPointwiseConstructor.residualPositiveDomain := by
  apply contDiffOn_pi.mpr
  intro i
  exact (Integration.transportedGrad_contDiffOn I hΦ m l hT i).mono (by
    intro z hz
    exact ⟨Set.mem_Ici.mpr (le_of_lt hz.1), Set.mem_univ _⟩)

theorem ResidualPointwiseConstructor.residual_matrixMul_contDiff {n : ℕ}
    {A B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) :
    ContDiff ℝ n (fun y => A y * B y) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ n (fun y => ∑ p : Fin 2, A y i p * B y p j)
  apply ContDiff.sum
  intro p hp
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) p).mul
    (contDiff_pi.mp (contDiff_pi.mp hB p) j)

theorem ResidualPointwiseConstructor.residual_psi_contDiff_two {β : ℝ} (I : Ingredients β)
    (m : ℕ) (k : ℤ) : ContDiff ℝ 2 (psi β I.Λ m k) := by
  unfold psi
  have hprofile : ContDiff ℝ 2
      (fun y : Vec 2 => psi0 k ((epsilon β I.Λ m)⁻¹ • y)) := by
    unfold psi0
    split_ifs <;> fun_prop
  exact contDiff_const.mul hprofile

theorem ResidualPointwiseConstructor.residual_psiTilde_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (_hm : 1 ≤ m) (t : ℝ) :
    ContDiff ℝ 1 (psiTilde I hΦ m t) := by
  classical
  let S : Finset {k : ℤ // Odd k} :=
    ((I.zetaMK_support_finite m t).preimage
      (fun _ _ _ _ h => Subtype.ext h)).toFinset
  have hsum : psiTilde I hΦ m t = fun y =>
      ∑ k ∈ S, I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t *
        psi β I.Λ m k.1 (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t y) := by
    funext y
    unfold psiTilde
    apply tsum_eq_sum
    intro k hk
    have hz : I.zetaMK m k.1 t = 0 := by
      by_contra hne
      have hS : k ∈ S := by
        simp only [S, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact hne
      apply hk
      exact hS
    simp [hz]
  rw [hsum]
  apply ContDiff.sum
  intro k hk
  have hInv : ContDiff ℝ 2
      (I.xFlowInv hΦ m (lIdx β I.Λ m k.1) t) :=
    xFlowInv_spatial_contDiff_two I hΦ m (lIdx β I.Λ m k.1) t
  have hpsi := (ResidualPointwiseConstructor.residual_psi_contDiff_two I m k.1).comp hInv
  have hc : ContDiff ℝ 1 (fun _ : Vec 2 =>
      I.hatZetaML m (lIdx β I.Λ m k.1) t * I.zetaMK m k.1 t) := contDiff_const
  exact ((hc.mul (hpsi.of_le (by norm_num))).of_le (by norm_num))

theorem ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κ : ℝ) (t : ℝ) :
    ContDiff ℝ 1 (fun y => diffusionMatrix I hΦ m κ t y) := by
  have hpsi := ResidualPointwiseConstructor.residual_psiTilde_contDiff I hΦ m hm t
  have hscaled : ContDiff ℝ 1 (fun y => psiTilde I hΦ m t y • sigmaMat) :=
    hpsi.smul contDiff_const
  exact contDiff_const.add hscaled

theorem ResidualPointwiseConstructor.residual_chiGradG_contDiff {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ)
    (T : ℝ → Vec 2 → ℝ) (k : ℤ) (t : ℝ)
    (hT : ContDiffOn ℝ ∞ (Function.uncurry T)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)) (ht : 0 ≤ t) :
    ContDiff ℝ 1 (chiGradG I hΦ m κ T k t) := by
  have hchi : ContDiff ℝ 2 (I.chiTilde hΦ m κ k t) :=
    ResidualPointwiseConstructor.residual_chiSlice_contDiff I hΦ m κ k t
  have hG : ContDiff ℝ ∞ (G I hΦ m T (lIdx β I.Λ m k) t) :=
    ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m T hT ht (lIdx β I.Λ m k)
  have hgrad : ContDiff ℝ 1 (fun y =>
      gradG I hΦ m T (lIdx β I.Λ m k) t y) := by
    have hGM := ResidualPointwiseConstructor.residual_gradMatrix_contDiff (n := 1) (hG.of_le (by norm_num))
    have heq : (fun y => gradG I hΦ m T (lIdx β I.Λ m k) t y) =
        fun y => gradMatrix (G I hΦ m T (lIdx β I.Λ m k) t) y := by
      funext y
      ext i j
      simp [gradG, gradMatrix, Matrix.of_apply]
    rw [heq]
    exact hGM
  apply contDiff_pi.mpr
  intro i
  change ContDiff ℝ 1 (fun y => ∑ j : Fin 2,
    I.chiTilde hΦ m κ k t y j *
      gradG I hΦ m T (lIdx β I.Λ m k) t y i j)
  apply ContDiff.sum
  intro j hj
  exact (contDiff_pi.mp hchi j).of_le (by norm_num) |>.mul
    ((contDiff_pi.mp (contDiff_pi.mp hgrad i)) j)

/-- Every component of the source's pointwise residual-calculus record is
obtained from the classical iterate and the declared smooth flow. -/
def frozenResidualPointwiseData_of_iterates {β : ℝ}
    (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm κprev : ℝ) (hκm : 0 < κm)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (hθprev : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (t : ℝ) (ht : 0 < t) (x : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) :
    FrozenResidualPointwiseData I hΦ m hm κm κprev θ₀ θprev T hT
      t ht x ρ hρ := by
  classical
  let Tlast : ℝ → Vec 2 → ℝ := T (Nstar β)
  have hTjoint : ContDiffOn ℝ ∞ (Function.uncurry Tlast)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    exact tIterate_contDiffOn_nonneg I hΦ hT hθprev le_rfl
  have hU : IsOpen ResidualPointwiseConstructor.residualPositiveDomain := isOpen_Ioi.prod isOpen_univ
  have hUp (z : ℝ × Vec 2) (hz : z ∈ ResidualPointwiseConstructor.residualPositiveDomain) :
      ResidualPointwiseConstructor.residualPositiveDomain ∈ 𝓝 z := hU.mem_nhds hz
  have hHmOn := residual_Hm_contDiffOn_two I hΦ hm hκm hθprev hT
  have hTlastSlice : ContDiff ℝ ∞ (Tlast t) :=
    tIterate_space_contDiff I hΦ hT hθprev le_rfl (le_of_lt ht)
  have hTprevSlice : ContDiff ℝ ∞ (T (Nstar β - 1) t) :=
    tIterate_space_contDiff I hΦ hT hθprev (by omega) (le_of_lt ht)
  have hTlastC3 : ContDiff ℝ 3 (Tlast t) := hTlastSlice.of_le (by norm_num)
  have hTprevC3 : ContDiff ℝ 3 (T (Nstar β - 1) t) :=
    hTprevSlice.of_le (by norm_num)
  have hTlastGrad : ContDiff ℝ 2 (spaceGrad (Tlast t)) :=
    ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order hTlastC3
  have hHmSlice : ContDiff ℝ 2 (I.Hm hΦ m κm Tlast t) := by
    exact ResidualPointwiseConstructor.residual_contDiffOn_slice hHmOn ht
  have hTjointU : ContDiffOn ℝ ∞ (Function.uncurry Tlast)
      ResidualPointwiseConstructor.residualPositiveDomain := hTjoint.mono (by
        intro z hz
        exact ⟨Set.mem_Ici.mpr (le_of_lt hz.1), Set.mem_univ _⟩)
  have hTjointPos : ContDiffOn ℝ 1 (Function.uncurry Tlast)
      ResidualPointwiseConstructor.residualPositiveDomain := hTjointU.of_le (by norm_num)
  have hTpoint : ContDiffAt ℝ 1 (Function.uncurry Tlast) (t, x) :=
    (hTjointPos.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩))
  have hHmPoint : ContDiffAt ℝ 2
      (Function.uncurry fun s y => I.Hm hΦ m κm Tlast s y) (t, x) :=
    hHmOn.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
  refine {
    Dt := fun r => deriv (fun s => I.Hmr hΦ m κm Tlast r s x) t
    LHm := fun r => fderiv ℝ (I.Hmr hΦ m κm Tlast r t) x
    hDt := by
      intro r hr
      have hHmr := residual_Hmr_contDiffOn_two I hΦ hm hκm hθprev hT r hr
      have hHmr1 : ContDiffOn ℝ 1
          (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm Tlast r z.1 z.2)
          ResidualPointwiseConstructor.residualPositiveDomain := hHmr.of_le (by norm_num)
      have hHmrU : ContDiffOn ℝ 1
          (Function.uncurry fun s y => I.Hmr hΦ m κm Tlast r s y)
          ResidualPointwiseConstructor.residualPositiveDomain := by
        change ContDiffOn ℝ 1
          (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm Tlast r z.1 z.2)
          ResidualPointwiseConstructor.residualPositiveDomain
        exact hHmr1
      have hder := ResidualPointwiseConstructor.residual_time_hasDerivAt (F := fun s y =>
        I.Hmr hΦ m κm Tlast r s y) (x := x) hHmrU ht
      rw [hder.deriv]
      exact hder
    hDx := by
      intro r hr
      have hHmr := residual_Hmr_contDiffOn_two I hΦ hm hκm hθprev hT r hr
      have hp := hHmOn
      have hAt := hHmr.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
      have hAt1 : ContDiffAt ℝ 1
          (Function.uncurry fun s y => I.Hmr hΦ m κm Tlast r s y) (t, x) :=
        hAt.of_le (by norm_num)
      have hAtU : ContDiffAt ℝ 1
          (Function.uncurry fun s y => I.Hmr hΦ m κm Tlast r s y) (t, x) := by
        change ContDiffAt ℝ 1
          (fun z : ℝ × Vec 2 => I.Hmr hΦ m κm Tlast r z.1 z.2) (t, x)
        exact hAt1
      exact ResidualPointwiseConstructor.residual_slice_hasFDerivAt_canonical hAtU
    hA := by
      intro r hr n i j k z hz
      have hreg := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT n r 1
        (ResidualPointwiseConstructor.residual_amnrBudget_one hr) i j k
      exact (hreg.contDiffAt (hUp z ⟨hz, Set.mem_univ _⟩)).differentiableAt
        (by norm_num)
    hPair := by
      intro r hr a z hz
      have hAtA (i : Fin 2) : ContDiffAt ℝ 1
          (fun p : ℝ × Vec 2 =>
            I.Amnr hΦ m κm a.1.1 Tlast r p.1 p.2 i a.1.2 a.2) z := by
        have hreg := amnr_actual_contDiffOn I hΦ hm hκm hθprev hT
          a.1.1 r 1 (ResidualPointwiseConstructor.residual_amnrBudget_one hr) i a.1.2 a.2
        exact hreg.contDiffAt (hUp z ⟨hz, Set.mem_univ _⟩)
      have hq := residual_qMNR_contDiff I κm m a.1.1 (r + 1)
      have hqEntry : ContDiff ℝ ∞ (fun s =>
          (I.qMNR κm m a.1.1 (r + 1) s) a.1.2 a.2) :=
        (contDiff_pi.mp ((contDiff_pi.mp hq) a.1.2)) a.2
      have hqJoint : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
          (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) := by
        exact hqEntry.comp contDiff_fst
      have hPairAt : ContDiffAt ℝ 1
          (amnrPairFlux I hΦ m κm Tlast r a) z := by
        apply contDiffAt_pi.mpr
        intro i
        have hqJoint1 : ContDiff ℝ 1 (fun p : ℝ × Vec 2 =>
            (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) :=
          hqJoint.of_le (by simp)
        have hqAt : ContDiffAt ℝ 1 (fun p : ℝ × Vec 2 =>
            (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) z := hqJoint1.contDiffAt
        change ContDiffAt ℝ 1 (fun p : ℝ × Vec 2 =>
          I.Amnr hΦ m κm a.1.1 Tlast r p.1 p.2 i a.1.2 a.2 *
            (I.qMNR κm m a.1.1 (r + 1) p.1) a.1.2 a.2) z
        exact (hAtA i).mul hqAt
      exact hPairAt.differentiableAt (by norm_num)
    hFlux := by
      intro r hr
      have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
          2 + r ≤ Nstar β := by
        have hcut := Finset.mem_range.mp hr
        unfold Jcut at hcut
        omega
      have hflux := residual_pairFluxSum_contDiffOn I hΦ hm hκm hθprev hT
        (Nstar β) r 2 hbudget
      exact hflux.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
    hEndNext := by
      intro r hr
      have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
          1 + (r + 1) ≤ Nstar β := ResidualPointwiseConstructor.residual_hmEndpoint_budget hr
      have hend := residual_pairEndpointFluxSum_contDiffOn I hΦ hm hκm
        hθprev hT (Nstar β) (r + 1) 1 hbudget
      exact hend.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩) |>.differentiableAt
        (by norm_num)
    hEnd := by
      intro r hr
      have hbudget (n : ℕ) (_hn : n ∈ Finset.range (Nstar β)) :
          1 + r ≤ Nstar β := by
        have h := ResidualPointwiseConstructor.residual_hmEndpoint_budget hr
        omega
      have hend := residual_pairEndpointFluxSum_contDiffOn I hΦ hm hκm
        hθprev hT (Nstar β) r 1 hbudget
      exact hend.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩) |>.differentiableAt
        (by norm_num)
    hTail := by
      let Tail : Vec 2 → Vec 2 := fun y i =>
        ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n Tlast (Jcut β) t y i j k *
            I.qMNR κm m n (Jcut β) t j k
      have hTail : ContDiff ℝ 1 Tail := by
        simpa [Tail, Tlast] using
          ResidualPointwiseConstructor.residual_sourceTail_spatial_contDiff I hΦ m hm κm κprev hκm T
            hθprev hT ht
      exact (hTail.differentiable (by norm_num) x)
    hBase := (LeftJacobian.contDiff_pulledGapFlux I hΦ m hm (I.Jhat κm m t - I.Kmat κm m t) Tlast t
      hTlastSlice).differentiable (by simp) x
    hTtime := by
      have hder := ResidualPointwiseConstructor.residual_time_hasDerivAt (F := Tlast) (x := x)
        hTjointPos ht
      rw [hder.deriv]
      exact hder
    hHtime := by
      have hHmOn1 : ContDiffOn ℝ 1
          (Function.uncurry fun s y => I.Hm hΦ m κm Tlast s y)
          ResidualPointwiseConstructor.residualPositiveDomain := by
        change ContDiffOn ℝ 1
          (fun z : ℝ × Vec 2 => I.Hm hΦ m κm Tlast z.1 z.2)
          ResidualPointwiseConstructor.residualPositiveDomain
        exact hHmOn.of_le (by norm_num)
      have hder := ResidualPointwiseConstructor.residual_time_hasDerivAt
        (F := fun s y => I.Hm hΦ m κm Tlast s y) (x := x) hHmOn1 ht
      rw [hder.deriv]
      exact hder
    hXi := by
      intro k hk
      exact (Integration.contDiff_xiMK I m k).differentiable
        (by norm_num) t |>.hasDerivAt
    Lχ := fun k => fderiv ℝ
      (Function.uncurry fun s y => I.chiTilde hΦ m κm k s y) (t, x)
    LG := fun k => fderiv ℝ
      (Function.uncurry fun s y => G I hΦ m Tlast (lIdx β I.Λ m k) s y) (t, x)
    hChiJoint := by
      intro k hk
      have hchi : ContDiff ℝ 2
          (Function.uncurry fun s y => I.chiTilde hΦ m κm k s y) := by
        apply contDiff_pi.mpr
        intro i
        exact Integration.chiTilde_component_contDiff_two I hΦ m κm k i
      exact (hchi.differentiable (by norm_num) (t, x)).hasFDerivAt
    hGJoint := by
      intro k hk
      have hGOn := ResidualPointwiseConstructor.residual_Gjoint_contDiffOn I hΦ m Tlast hTjoint
        (lIdx β I.Λ m k)
      have hGAt := hGOn.contDiffAt (hUp (t, x) ⟨ht, Set.mem_univ _⟩)
      exact (hGAt.differentiableAt (by simp)).hasFDerivAt
    hr46 := (tIterate_r46Flux_regular I hΦ hm κm hT hθprev le_rfl ht).1.differentiable
      (by simp) x
    hDE := by
      let Tail : Vec 2 → Vec 2 := fun y i =>
        ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
          I.Amnr hΦ m κm n Tlast (Jcut β) t y i j k *
            I.qMNR κm m n (Jcut β) t j k
      have hTail : ContDiff ℝ 1 Tail := by
        simpa [Tail, Tlast] using
          ResidualPointwiseConstructor.residual_sourceTail_spatial_contDiff I hΦ m hm κm κprev hκm T
            hθprev hT ht
      have hgap := LeftJacobian.contDiff_pulledGapFlux I hΦ m hm (I.Jhat κm m t - I.flux κm m t)
        Tlast t hTlastSlice
      have hiterate := ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff I hΦ m hm
        κm κprev t (le_of_lt ht) T hTprevC3 hTlastC3
      have hsum : ContDiff ℝ 1 (fun y =>
          (∑' l : ℤ, I.hatXiML m l t •
            ((I.flowGrad hΦ m l t y).transpose.mulVec
              ((I.Jhat κm m t - I.flux κm m t).mulVec
                ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (Tlast t) y))))) + Tail y +
            iterateError I hΦ m κm κprev T t y) :=
        ((hgap.of_le (by simp)).add hTail).add (hiterate.of_le (by norm_num))
      exact hsum.differentiable (by norm_num) x
    hSmooth := hTlastSlice
    hHGlobal := by
      intro y
      exact ((hHmSlice.differentiable (by norm_num) y).hasFDerivAt)
    hChiGlobal := by
      intro k hk y
      have hchi := ResidualPointwiseConstructor.residual_chiSlice_contDiff I hΦ m κm k t
      exact (hchi.differentiable (by norm_num) y).hasFDerivAt
    hGGlobal := by
      intro k hk y
      have hG := ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m Tlast hTjoint
        (le_of_lt ht) (lIdx β I.Λ m k)
      exact (hG.differentiable (by norm_num) y).hasFDerivAt
    hCorrectorFlux := by
      intro q hq i j
      let l := lIdx β I.Λ m q.1
      have hInv : ContDiff ℝ 2 (I.xFlowInv hΦ m l t) :=
        xFlowInv_spatial_contDiff_two I hΦ m l t
      have hpsi : ContDiff ℝ 2 (fun y =>
          psi β I.Λ m q.1 (I.xFlowInv hΦ m l t y)) :=
        (ResidualPointwiseConstructor.residual_psi_contDiff_two I m q.1).comp hInv
      have hchi : ContDiff ℝ 2 (I.chiTilde hΦ m κm q.1 t) :=
        ResidualPointwiseConstructor.residual_chiSlice_contDiff I hΦ m κm q.1 t
      have hgradChi : ContDiff ℝ 1
          (fun y => gradMatrix (I.chiTilde hΦ m κm q.1 t) y) :=
        ResidualPointwiseConstructor.residual_gradMatrix_contDiff (n := 1) hchi
      have hcoef : ContDiff ℝ 1 (fun y =>
          I.hatZetaML m l t * I.zetaMK m q.1 t *
            psi β I.Λ m q.1 (I.xFlowInv hΦ m l t y)) :=
        (contDiff_const.mul (hpsi.of_le (by norm_num)))
      have hbase : ContDiff ℝ 1 (fun y =>
          κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            (I.hatZetaML m l t * I.zetaMK m q.1 t *
              psi β I.Λ m q.1 (I.xFlowInv hΦ m l t y)) • sigmaMat) := by
        exact contDiff_const.add (hcoef.smul contDiff_const)
      have hright : ContDiff ℝ 1 (fun y =>
          (1 : Matrix (Fin 2) (Fin 2) ℝ) +
            gradMatrix (I.chiTilde hΦ m κm q.1 t) y) :=
        contDiff_const.add hgradChi
      have hflux := ResidualPointwiseConstructor.residual_matrixMul_contDiff hbase hright
      have hentry : ContDiff ℝ 1
          (fun y => correctorFlux I hΦ m κm q.1 t y i j) := by
        simpa [correctorFlux, gradChiTilde, l] using
          (contDiff_pi.mp ((contDiff_pi.mp hflux) i) j)
      exact (hentry.differentiable (by norm_num) x).hasFDerivAt
    hGodd := by
      intro q
      have hG := ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m Tlast hTjoint
        (le_of_lt ht) (lIdx β I.Λ m q.1)
      exact (hG.differentiable (by norm_num) x).hasFDerivAt
    LM := fderiv ℝ (fun y =>
      (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (Tlast t) y -
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t • G I hΦ m Tlast
              (lIdx β I.Λ m q.1) t y)) x
    LC := fderiv ℝ (fun y =>
      ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • (diffusionMatrix I hΦ m κm t y).mulVec
          (chiGradG I hΦ m κm Tlast q.1 t y)) x
    LHflux := fderiv ℝ (fun y =>
      (diffusionMatrix I hΦ m κm t y).mulVec
        (spaceGrad (I.Hm hΦ m κm Tlast t) y)) x
    hMismatch := by
      have hD := ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one I hΦ m hm κm t
      have hGmode (q : {k : ℤ // Odd k}) : ContDiff ℝ ∞
          (fun y => G I hΦ m Tlast (lIdx β I.Λ m q.1) t y) :=
        ResidualPointwiseConstructor.residual_Gslice_smooth I hΦ m Tlast hTjoint (le_of_lt ht)
          (lIdx β I.Λ m q.1)
      have hGsum : ContDiff ℝ 2 (fun y =>
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t • G I hΦ m Tlast
              (lIdx β I.Λ m q.1) t y) := by
        apply ContDiff.sum
        intro q hq
        have hG2 : ContDiff ℝ 2
            (fun y => G I hΦ m Tlast (lIdx β I.Λ m q.1) t y) :=
          (hGmode q).of_le (by norm_num)
        have hξ : ContDiff ℝ 2
            (fun _ : Vec 2 => I.xiMK m q.1 t) := contDiff_const
        exact hξ.smul hG2
      have hV : ContDiff ℝ 1 (fun y =>
          spaceGrad (Tlast t) y -
            ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
              I.xiMK m q.1 t • G I hΦ m Tlast
                (lIdx β I.Λ m q.1) t y) := by
        exact (hTlastGrad.of_le (by norm_num)).sub (hGsum.of_le (by norm_num))
      have hflux := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hD hV
      exact (hflux.differentiable (by norm_num) x).hasFDerivAt
    hChiFlux := by
      have hD := ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one I hΦ m hm κm t
      have hterm (q : {k : ℤ // Odd k}) : ContDiff ℝ 1
          (fun y => (diffusionMatrix I hΦ m κm t y).mulVec
            (chiGradG I hΦ m κm Tlast q.1 t y)) := by
        have hχG := ResidualPointwiseConstructor.residual_chiGradG_contDiff I hΦ m κm Tlast q.1 t
          hTjoint (le_of_lt ht)
        exact ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hD hχG
      have hsum : ContDiff ℝ 1 (fun y =>
          ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
            I.xiMK m q.1 t •
              (diffusionMatrix I hΦ m κm t y).mulVec
                (chiGradG I hΦ m κm Tlast q.1 t y)) := by
        apply ContDiff.sum
        intro q hqmem
        have hξ : ContDiff ℝ 1
            (fun _ : Vec 2 => I.xiMK m q.1 t) := contDiff_const
        exact hξ.smul (hterm q)
      exact (hsum.differentiable (by norm_num) x).hasFDerivAt
    hHmFlux := by
      have hD := ResidualPointwiseConstructor.residual_diffusionMatrix_contDiff_one I hΦ m hm κm t
      have hgrad := ResidualPointwiseConstructor.residual_spaceGrad_contDiff_order (n := 1) hHmSlice
      have hflux := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hD hgrad
      exact (hflux.differentiable (by norm_num) x).hasFDerivAt
    hVecGlobal := by
      intro y
      have hM : ContDiff ℝ 2 (fun z => I.Kmat κm m t + I.sMat hΦ m κm t z) :=
        contDiff_const.add (sMat_spatial_contDiff_two I hΦ m hm κm t)
      have hV := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hM
        (hTlastGrad.of_le (by norm_num))
      exact (hV.differentiable (by norm_num) y)
    hIterateGlobal := by
      intro y
      exact (ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff I hΦ m hm
        κm κprev t (le_of_lt ht) T hTprevC3 hTlastC3).differentiable
          (by norm_num) y
    hVecDiv := by
      have hM : ContDiff ℝ 2 (fun z => I.Kmat κm m t + I.sMat hΦ m κm t z) :=
        contDiff_const.add (sMat_spatial_contDiff_two I hΦ m hm κm t)
      have hV := ResidualPointwiseConstructor.residual_matrixMulVec_contDiff hM
        (hTlastGrad.of_le (by norm_num))
      have hdiv := ResidualPointwiseConstructor.residual_vecDiv_contDiff hV
      exact hdiv.differentiable (by norm_num) x
    hIterateDiv := by
      have hiter := ResidualPointwiseConstructor.residual_iterateError_spatial_contDiff I hΦ m hm
        κm κprev t (le_of_lt ht) T hTprevC3 hTlastC3
      exact (ResidualPointwiseConstructor.residual_vecDiv_contDiff hiter).differentiable (by norm_num) x
    hAnsatz := by
      classical
      let S := (I.xiMK_support_finite m t).toFinset
      have hzero (k : ℤ) (hk : k ∉ S) : I.xiMK m k t = 0 := by
        by_contra hne
        exact hk ((I.xiMK_support_finite m t).mem_toFinset.mpr hne)
      have hfun : I.ansatz hΦ m κm Tlast t = fun y =>
          Tlast t y +
            (∑ k ∈ S, Integration.ansatzSummand I hΦ m κm Tlast k t y) +
              I.Hm hΦ m κm Tlast t y := by
        funext y
        rw [Integration.ansatz_eq_summand]
        congr 2
        exact tsum_eq_sum fun k hk =>
          Integration.ansatzSummand_eq_zero I hΦ m κm Tlast (hzero k hk) y
      rw [hfun]
      have hSeries : ContDiff ℝ 2 (fun y =>
          Tlast t y +
            (∑ k ∈ S, Integration.ansatzSummand I hΦ m κm Tlast k t y)) := by
        apply (hTlastSlice.of_le (by norm_num)).add
        apply ContDiff.sum
        intro k hk
        exact Integration.ansatzSummand_slice_contDiff I hΦ m κm k hTlastSlice
          |>.of_le (by norm_num)
      exact (hSeries.add hHmSlice).contDiffAt
  }

end AVenhance.Infra.Section5

end
