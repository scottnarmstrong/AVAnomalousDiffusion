-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Anomalous diffusion by fractal homogenization: the main theorem

A standalone, Mathlib-only statement of the main theorem of S. Armstrong and V. Vicol,
*Anomalous diffusion by fractal homogenization*, arXiv:2305.05048,
together with two further results of the paper, combined into one statement about a
single drift.

We work on the two-dimensional torus `𝕋² = ℝ²/ℤ²`, realized by `ℤ²`-periodic functions on
`ℝ² = Fin 2 → ℝ`; integrals over `𝕋²` are integrals over the open unit square `(0,1)²`.
For a drift `b(t,x)` and diffusivity `κ > 0`, a solution of the advection–diffusion equation

  `∂ₜθ + b·∇θ = κΔθ`  on `(0,1) × 𝕋²`,  `θ(0,·) = θ₀`,

is understood in the weak sense of `IsWeakSolution` below. For `0 < α < 1/3` the theorem
produces one divergence-free drift `b ∈ C⁰_t C^{0,α}_x ∩ C^{0,α}_t C⁰_x([0,1] × 𝕋²)`,
`ℤ²`-periodic in space, such that:

* **(i) Anomalous dissipation** (Theorem 1.1 of the paper). For every mean-zero datum
  `θ₀ ∈ H¹(𝕋²)`, `limsup_{κ→0} κ‖∇θ^κ‖²_{L²((0,1)×𝕋²)} ≥ ϱ(‖θ₀‖_{L²}/‖∇θ₀‖_{L²})² ‖θ₀‖²_{L²}`,
  with `ϱ` positive and independent of `θ₀`.
* **(ii) Uniform Hölder regularity in time.** Along the set of diffusivities
  `𝒦 = ⋃ⱼ [κⱼ/2, 2κⱼ]`, where `κⱼ ↓ 0` with `4κⱼ₊₁ < κⱼ`, every solution satisfies
  `‖θ^κ‖_{C^{0,μ}([0,1]; L²(𝕋²))} ≤ C‖θ₀‖_{H¹}` with `μ, C` independent of `κ` and `θ₀`.
* **(iii) Non-uniqueness of vanishing-diffusivity limits.** There is a class `𝒟` of smooth,
  mean-zero, nonzero data (closed under nonzero scalings and containing `cos(2πn x₁)` for
  infinitely many `n`) such that, for every `θ₀ ∈ 𝒟`, the solutions along the two sequences
  `κ_{2j}/2` and `2κ_{2j}` converge in `C^{0,ν}([0,1]; L²(𝕋²))` to two weak solutions of the
  transport equation `∂ₜθ + b·∇θ = 0` whose `L²` norms differ at some time.

Item (iii) is a corrected form of the paper's no-selection statement; see the repository's
README and errata.
-/

@[expose] public section

open Filter MeasureTheory Topology

noncomputable section

namespace AVChallenge

/-! ## Euclidean plane, torus and Sobolev notions -/

/-- The Euclidean dot product on `ℝ² = Fin 2 → ℝ`. -/
def dot (x y : Fin 2 → ℝ) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean length on `ℝ²`. -/
def normSq (x : Fin 2 → ℝ) : ℝ := dot x x

/-- The open unit square `(0,1)²`, a full-measure fundamental cell of `𝕋²`. -/
def unitCube : Set (Fin 2 → ℝ) := Set.pi Set.univ fun _ => Set.Ioo (0 : ℝ) 1

/-- The space-time cell `(0,1) × (0,1)²`. -/
def timeCube : Set (ℝ × (Fin 2 → ℝ)) := Set.Ioo (0 : ℝ) 1 ×ˢ unitCube

/-- `ℤ²`-periodicity: `f (x + n) = f x` for all `n ∈ ℤ²` and `x ∈ ℝ²`. -/
def IsZ2Periodic {β : Type*} (f : (Fin 2 → ℝ) → β) : Prop :=
  ∀ (n : Fin 2 → ℤ) (x : Fin 2 → ℝ), f (x + fun i => (n i : ℝ)) = f x

/-- `‖f‖²_{L²(𝕋²)} = ∫_{(0,1)²} f²`. -/
def l2NormSq (f : (Fin 2 → ℝ) → ℝ) : ℝ := ∫ x in unitCube, f x ^ 2

/-- `‖Du‖²_{L²(𝕋²)} = ∫_{(0,1)²} |Du|²`. -/
def gradNormSq (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : ℝ := ∫ x in unitCube, normSq (Du x)

/-- `‖Dθ‖²_{L²((0,1)×𝕋²)}` for a time-dependent vector field `Dθ`. -/
def spaceTimeGradNormSq (Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : ℝ :=
  ∫ p in timeCube, normSq (Dθ p.1 p.2)

/-- The classical gradient of `f : ℝ² → ℝ`, coordinatewise. -/
def spaceGrad (f : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun x i => fderiv ℝ f x (Pi.single i (1 : ℝ))

/-- `u ∈ L²(U)`. -/
abbrev MemL2On (U : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ) : Prop :=
  MemLp u 2 (volume.restrict U)

/-- Each component of `Du` lies in `L²(U)`. -/
def GradMemL2On (U : Set (Fin 2 → ℝ)) (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2, MemL2On U (fun x => Du x i)

/-- `gi` is the weak `i`-th partial derivative of `u` on `U`. -/
def HasWeakPartialDerivOn (U : Set (Fin 2 → ℝ)) (i : Fin 2)
    (u gi : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x in U, u x * (fderiv ℝ φ x) (Pi.single i (1 : ℝ)) = -∫ x in U, gi x * φ x

/-- `Du` is the weak gradient of `u` on `U`. -/
def HasWeakGradientOn (U : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ)
    (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ i : Fin 2, HasWeakPartialDerivOn U i u (fun x => Du x i)

/-- `u ∈ H¹(𝕋²)` with weak gradient `Du`: both periodic, square integrable on the cell, and
`Du` is the weak gradient of `u` on all of `ℝ²`. -/
def IsPeriodicH1With (u : (Fin 2 → ℝ) → ℝ) (Du : (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  IsZ2Periodic u ∧ IsZ2Periodic Du ∧ MemL2On unitCube u ∧ GradMemL2On unitCube Du ∧
    HasWeakGradientOn Set.univ u Du

/-- `∫_U u = 0`. -/
def MeanZeroOn (U : Set (Fin 2 → ℝ)) (u : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∫ x in U, u x = 0

/-! ## Drifts -/

/-- The drift class: on `[0,1] × ℝ²`, `b` is `ℤ²`-periodic in space, continuous, bounded,
and `α`-Hölder in space and in time. -/
def IsHolderClass (α : ℝ) (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (b t)) ∧
  ContinuousOn (fun p : ℝ × (Fin 2 → ℝ) => b p.1 p.2) (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x y, ‖b t x - b t y‖ ≤ C * ‖x - y‖ ^ α) ∧
  (∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x,
    ‖b s x - b t x‖ ≤ C * |s - t| ^ α)

/-- `t ↦ b(t,·)` is continuous on `[0,1]` for the spatial `α`-Hölder seminorm. Together with
`IsHolderClass α b` this is the class `C⁰_t C^{0,α}_x ∩ C^{0,α}_t C⁰_x` on `[0,1] × 𝕋²`. -/
def IsContinuousIntoHolder (α : ℝ) (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |t - s| < δ → ∀ x y : Fin 2 → ℝ,
      ‖(b t x - b s x) - (b t y - b s y)‖ ≤ ε * ‖x - y‖ ^ α

/-- `b(t,·)` is distributionally divergence-free for every `t ∈ [0,1]`. -/
def IsDivFree (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ → ∫ x, dot (b t x) (spaceGrad φ x) = 0

/-! ## Weak solutions -/

/-- Test functions: smooth on `ℝ × ℝ²`, `ℤ²`-periodic in space, vanishing for `t ≥ 1`. -/
def IsTestFunction (φ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin 2 → ℝ) => φ p.1 p.2) ∧
  (∀ t, IsZ2Periodic (φ t)) ∧ ∀ t, 1 ≤ t → ∀ x, φ t x = 0

/-- `θ` is a weak solution on `[0,1] × 𝕋²` of `∂ₜθ + b·∇θ − κΔθ = 0`, `θ(0) = θ₀`, with spatial
weak gradient `Dθ`: `θ ∈ L^∞_t L²_x ∩ L²_t H¹_x`, weakly continuous in time, the drift term
`b·Dθ` is integrable, and the weak formulation holds against every test function. -/
def IsWeakSolutionGrad (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (κ : ℝ) (θ₀ : (Fin 2 → ℝ) → ℝ)
    (θ : ℝ → (Fin 2 → ℝ) → ℝ) (Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ t) ≤ C) ∧
  MemLp (fun p : ℝ × (Fin 2 → ℝ) => θ p.1 p.2) 2 (volume.restrict timeCube) ∧
  (∀ i : Fin 2, MemLp (fun p : ℝ × (Fin 2 → ℝ) => Dθ p.1 p.2 i) 2 (volume.restrict timeCube)) ∧
  (∀ᵐ t ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), IsPeriodicH1With (θ t) (Dθ t)) ∧
  Integrable (fun p : ℝ × (Fin 2 → ℝ) => dot (b p.1 p.2) (Dθ p.1 p.2))
    (volume.restrict timeCube) ∧
  (∀ ψ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ φ : ℝ → (Fin 2 → ℝ) → ℝ, IsTestFunction φ →
    ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + dot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
        + κ * dot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
      = ∫ x in unitCube, θ₀ x * φ 0 x)

/-- `θ` is a weak solution of the advection–diffusion equation for some spatial gradient. -/
def IsWeakSolution (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (κ : ℝ) (θ₀ : (Fin 2 → ℝ) → ℝ)
    (θ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∃ Dθ : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ, IsWeakSolutionGrad b κ θ₀ θ Dθ

/-- `θ` is a weak solution on `[0,1] × 𝕋²` of the transport equation `∂ₜθ + ∇·(bθ) = 0`,
`θ(0) = θ₀` (equivalently `∂ₜθ + b·∇θ = 0` for divergence-free `b`). -/
def IsTransportWeakSolution (b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ) (θ₀ : (Fin 2 → ℝ) → ℝ)
    (θ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ t) ≤ C) ∧
  MemLp (fun p : ℝ × (Fin 2 → ℝ) => θ p.1 p.2) 2 (volume.restrict timeCube) ∧
  (∀ ψ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
    ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc (0 : ℝ) 1)) ∧
  (∀ φ : ℝ → (Fin 2 → ℝ) → ℝ, IsTestFunction φ →
    Integrable (fun p : ℝ × (Fin 2 → ℝ) => θ p.1 p.2 * dot (b p.1 p.2) (spaceGrad (φ p.1) p.2))
      (volume.restrict timeCube) ∧
    ∫ p in timeCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        - θ p.1 p.2 * dot (b p.1 p.2) (spaceGrad (φ p.1) p.2))
      = ∫ x in unitCube, θ₀ x * φ 0 x)

/-! ## Hölder continuity in time with values in `L²(𝕋²)` -/

/-- `‖θ(t) − θ(s)‖_{L²(𝕋²)} ≤ H |t − s|^μ` for all `s, t ∈ [0,1]`. -/
def IsHolderTimeL2 (μ H : ℝ) (θ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Real.sqrt (l2NormSq (fun x => θ t x - θ s x)) ≤ H * |t - s| ^ μ

/-- `‖θ‖_{C^{0,μ}([0,1]; L²(𝕋²))} ≤ H`, the norm being `sup_{t∈[0,1]} ‖θ(t)‖_{L²}` plus the
`μ`-Hölder seminorm (each slice `θ(t)` is required to lie in `L²`). -/
def HolderTimeL2Le (μ H : ℝ) (θ : ℝ → (Fin 2 → ℝ) → ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ t)) ∧
  ∃ A B : ℝ, A + B ≤ H ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, Real.sqrt (l2NormSq (θ t)) ≤ A) ∧
    IsHolderTimeL2 μ B θ

/-! ## The main theorem -/

/-- **Anomalous diffusion by fractal homogenization** (Armstrong–Vicol), combined form.
For `0 < α < 1/3` there is one divergence-free, `ℤ²`-periodic drift
`b ∈ C⁰_t C^{0,α}_x ∩ C^{0,α}_t C⁰_x([0,1] × 𝕋²)`
such that (i) anomalous dissipation holds for every mean-zero `H¹` datum, with a rate `ϱ`
depending only on the ratio `‖θ₀‖_{L²}/‖∇θ₀‖_{L²}`; (ii) along the diffusivities
`𝒦 = ⋃ⱼ [κⱼ/2, 2κⱼ]` all solutions are bounded in `C^{0,μ}([0,1]; L²)` by `C‖θ₀‖_{H¹}`; and
(iii) for every datum in a class `𝒟` containing `cos(2πn x₁)` for infinitely many `n`, the
solutions along `κ_{2j}/2` and along `2κ_{2j}` converge in `C^{0,ν}([0,1]; L²)` to two
transport solutions with different `L²` norms at some time. -/
theorem anomalous_dissipation_full (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ, IsHolderClass α b ∧ IsContinuousIntoHolder α b ∧ IsDivFree b ∧
    ∃ ϱ : ℝ → ℝ, (∀ r, 0 < ϱ r ∧ ϱ r ≤ 1) ∧
    ∃ κseq : ℕ → ℝ, (∀ j, 0 < κseq j) ∧ (∀ j, 4 * κseq (j + 1) < κseq j) ∧
      Tendsto κseq atTop (𝓝 0) ∧
    ∃ μ ν C : ℝ, 0 < μ ∧ 0 < ν ∧
    ∃ 𝒟 : Set ((Fin 2 → ℝ) → ℝ),
      -- (i) anomalous dissipation
      (∀ (θ₀ : (Fin 2 → ℝ) → ℝ) (Dθ₀ : (Fin 2 → ℝ) → Fin 2 → ℝ),
        IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
        ∀ (θ : ℝ → ℝ → (Fin 2 → ℝ) → ℝ) (Dθ : ℝ → ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ),
          (∀ κ : ℝ, 0 < κ → IsWeakSolutionGrad b κ θ₀ (θ κ) (Dθ κ)) →
          Filter.limsup (fun κ : ℝ => κ * spaceTimeGradNormSq (Dθ κ)) (𝓝[>] 0) ≥
            ϱ (Real.sqrt (l2NormSq θ₀) / Real.sqrt (gradNormSq Dθ₀)) ^ 2 * l2NormSq θ₀) ∧
      -- (ii) uniform Hölder regularity in time along 𝒦
      (∀ (θ₀ : (Fin 2 → ℝ) → ℝ) (Dθ₀ : (Fin 2 → ℝ) → Fin 2 → ℝ),
        IsPeriodicH1With θ₀ Dθ₀ → MeanZeroOn unitCube θ₀ →
        ∀ κ ∈ ⋃ j : ℕ, Set.Icc (κseq j / 2) (2 * κseq j),
        ∀ θ : ℝ → (Fin 2 → ℝ) → ℝ, IsWeakSolution b κ θ₀ θ →
          HolderTimeL2Le μ (C * Real.sqrt (l2NormSq θ₀ + gradNormSq Dθ₀)) θ) ∧
      -- (iii) the data class
      (∀ θ₀ ∈ 𝒟, ContDiff ℝ (⊤ : ℕ∞) θ₀ ∧ IsZ2Periodic θ₀ ∧ MeanZeroOn unitCube θ₀ ∧
        0 < l2NormSq θ₀) ∧
      (∀ θ₀ ∈ 𝒟, ∀ c : ℝ, c ≠ 0 → (fun x => c * θ₀ x) ∈ 𝒟) ∧
      (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        (fun x : Fin 2 → ℝ => Real.cos (2 * Real.pi * (n : ℝ) * x 0)) ∈ 𝒟) ∧
      -- (iii) two distinct vanishing-diffusivity limits
      (∀ θ₀ ∈ 𝒟, ∀ θ : ℝ → ℝ → (Fin 2 → ℝ) → ℝ,
        (∀ κ : ℝ, 0 < κ → IsWeakSolution b κ θ₀ (θ κ)) →
        ∃ θ₁ θ₂ : ℝ → (Fin 2 → ℝ) → ℝ,
          IsTransportWeakSolution b θ₀ θ₁ ∧ IsTransportWeakSolution b θ₀ θ₂ ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
            HolderTimeL2Le ν η (fun t x => θ (κseq (2 * j) / 2) t x - θ₁ t x)) ∧
          (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
            HolderTimeL2Le ν η (fun t x => θ (2 * κseq (2 * j)) t x - θ₂ t x)) ∧
          ∃ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ₁ t) ≠ l2NormSq (θ₂ t)) := by
  sorry

end AVChallenge
