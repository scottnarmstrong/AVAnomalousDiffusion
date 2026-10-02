# Anomalous diffusion by fractal homogenization, formalized in Lean 4

[![Build](https://github.com/scottnarmstrong/AVAnomalousDiffusion/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/AVAnomalousDiffusion/actions/workflows/build.yml)
[![Comparator](https://github.com/scottnarmstrong/AVAnomalousDiffusion/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/AVAnomalousDiffusion/actions/workflows/comparator.yml)

A complete, machine-checked proof of the main theorem of

> S. Armstrong and V. Vicol, *Anomalous diffusion by fractal homogenization*,
> [arXiv:2305.05048](https://arxiv.org/abs/2305.05048),

together with two further results of the paper, all for one and the same drift.
The paper constructs, for every $\alpha \in (0, 1/3)$, a divergence-free vector
field $\mathbf b \in C^{\alpha}$ on $[0,1] \times \mathbb T^2$ for which the
advection–diffusion equation

$$\partial_t \theta + \mathbf b \cdot \nabla \theta = \kappa \Delta \theta
\text{ in } (0,1) \times \mathbb T^2, \text{ with } \theta(0,\cdot) = \theta_0,$$

exhibits *anomalous dissipation*: as $\kappa \to 0$ the energy dissipated by
diffusion does not vanish, for every mean-zero, nonconstant initial datum in $H^1$.
The field is built by an infinite sequence of shear flows at rapidly
decreasing length scales, and the dissipation is obtained from a quantitative
homogenization argument run iteratively across all of these scales.

The formalization is written in Lean 4 on top of Mathlib. It contains no
`sorry` and uses no axioms beyond Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`).

## The main theorem

The headline declaration is `AVenhance.anomalous_dissipation_full` in
[AVenhance/Statements/FullTheorem/AnomalousDissipationFull.lean](AVenhance/Statements/FullTheorem/AnomalousDissipationFull.lean).
A standalone, Mathlib-only restatement is in [Challenge.lean](Challenge.lean)
(see [Independent statement check](#independent-statement-check)). For every
$\alpha \in (0, 1/3)$ it provides one drift
$\mathbf b \in C^0_t C^{0,\alpha}_x \cap C^{0,\alpha}_t C^0_x([0,1] \times \mathbb T^2)$,
the class of Theorem 1.1, which is $\mathbb Z^2$-periodic in space and
divergence-free in the sense of distributions on each time slice, and which
satisfies the following three properties.

**(i) Anomalous dissipation** (Theorem 1.1 of the paper). There is a function
$\varrho$ with values in $(0, 1]$ such that every mean-zero
$\theta_0 \in H^1(\mathbb T^2)$ satisfies

$$\limsup_{\kappa \to 0^+} \kappa \|\nabla \theta^\kappa\|_{L^2((0,1) \times \mathbb T^2)}^2
\ge \varrho\left(\frac{\|\theta_0\|_{L^2}}{\|\nabla\theta_0\|_{L^2}}\right)^{2} \|\theta_0\|_{L^2}^2 ,$$

where $\theta^\kappa$ is the weak solution with diffusivity $\kappa$ and datum
$\theta_0$. The rate $\varrho$ does not depend on $\theta_0$ beyond the
displayed ratio.

**(ii) Uniform Hölder regularity in time** (a remark in Section 5.4 of the paper).
There are diffusivities $\kappa_j \to 0$ with $4\kappa_{j+1} < \kappa_j$ and
constants $\mu > 0$, $C$ such that, for every $\kappa$ in
$\mathcal K = \bigcup_j [\kappa_j/2, 2\kappa_j]$ and every mean-zero datum
$\theta_0 \in H^1$,

$$\|\theta^\kappa\|_{C^{0,\mu}([0,1]; L^2(\mathbb T^2))} \le C \|\theta_0\|_{H^1}.$$

**(iii) Non-uniqueness of vanishing-diffusivity limits** (a corrected form of
no-selection principle in Section 5.5 of the paper). There is a class
$\mathcal D$ of smooth, mean-zero, nonzero data, closed under multiplication by
nonzero constants and containing $\cos(2\pi n x_1)$ for infinitely many $n$,
and an exponent $\nu > 0$, such that for every $\theta_0 \in \mathcal D$ the
solutions along $\kappa_{2j}/2$ and along $2\kappa_{2j}$ converge in
$C^{0,\nu}([0,1]; L^2(\mathbb T^2))$ to two weak solutions of the transport
equation $\partial_t \theta + \mathbf b \cdot \nabla \theta = 0$ with datum
$\theta_0$, and these two solutions have different $L^2$ norms at some time.
In particular the vanishing-diffusivity limit is not unique.

Part (i) alone is also stated and proved as `AVenhance.anomalous_dissipation`
in [AVenhance/Statements/Roots/AnomalousDissipation.lean](AVenhance/Statements/Roots/AnomalousDissipation.lean).

### Definitions

The statement uses the following definitions, all in
[AVenhance/Statements](AVenhance/Statements). Space is
`Vec 2 = Fin 2 → ℝ`, functions on $\mathbb T^2$ are $\mathbb Z^2$-periodic
functions on $\mathbb R^2$, and integrals over $\mathbb T^2$ are integrals over
the open unit square.

| Lean | Meaning |
|---|---|
| `IsHolderClass α b` | $\mathbf b$ is periodic in space, continuous, bounded, and $\alpha$-Hölder in $x$ (uniformly in $t$) and in $t$ (uniformly in $x$) on $[0,1] \times \mathbb R^2$ |
| `IsContinuousIntoHolder α b` | $t \mapsto \mathbf b(t,\cdot)$ is continuous on $[0,1]$ for the spatial $C^{0,\alpha}$ seminorm; with `IsHolderClass` this is $C^0_t C^{0,\alpha}_x \cap C^{0,\alpha}_t C^0_x$ |
| `IsDivFree b` | $\int \mathbf b(t,\cdot) \cdot \nabla\varphi = 0$ for all $t \in [0,1]$ and all smooth compactly supported $\varphi$ |
| `IsPeriodicH1With θ₀ Dθ₀` | $\theta_0 \in H^1(\mathbb T^2)$ with weak gradient $D\theta_0$ |
| `IsWeakSolutionGrad b κ θ₀ θ Dθ` | $\theta \in L^\infty_t L^2_x \cap L^2_t H^1_x$ with spatial weak gradient $D\theta$, weakly continuous in time, $\mathbf b \cdot D\theta$ integrable, and the weak form of the equation holds against all smooth periodic test functions vanishing at $t = 1$ |
| `IsWeakSolution b κ θ₀ θ` | `IsWeakSolutionGrad` for some $D\theta$ |
| `HolderTimeL2Le μ H θ` | $\sup_{t \in [0,1]} \|\theta(t)\|_{L^2} + [\theta]_{C^{0,\mu}([0,1]; L^2)} \le H$ |
| `IsTransportWeakSolution b θ₀ θ` | weak solution of $\partial_t\theta + \nabla\cdot(\mathbf b\theta) = 0$ in the same class, without the gradient |

Weak solutions of the advection–diffusion equation exist and are unique for
every $\kappa > 0$ and every $H^1$ datum (`AVenhance.weak_wellposed`), so
the hypotheses of (i) and (ii) can be met. The `limsup` in (i) is taken in
$\mathbb R$. The energy identity bounds
$\kappa \|\nabla\theta^\kappa\|^2$ by $\frac12 \|\theta_0\|_{L^2}^2$, so the
`limsup` is a genuine limit superior and not a default value.

## Scope and differences from the paper

- **Dimension.** The paper states Theorem 1.1 in every dimension $d \ge 2$ but
  writes out the proof only for $d = 2$. The formalization is in $d = 2$.
- **Details of the proof.** In a few places the formal proof differs from the
  printed one: the induction step controls errors relative to the dissipation
  rather than additively, and the coarse coefficient of the multiscale ansatz
  includes a left Jacobian factor. As a result the construction uses
  $\beta \in (\max\{6/5, 1+\alpha\}, 4/3)$ rather than $\beta = 1 + \alpha$,
  and the power of the ratio in $\varrho$ differs slightly; the statement of
  Theorem 1.1 is unchanged. These points and some minor corrections (signs,
  ranges, exponents) are listed in [doc/errata.pdf](doc/errata.pdf).
- **No-selection principle.** The proof of the no-selection
  principle in Section 5.5 of the paper contains a scaling error, and its
  restriction $\beta \ge 68/67$ is an artifact of that error. Part (iii) is a
  corrected version for the class $\mathcal D$ above, valid for the same drift as
  Theorem 1.1, hence for every $\alpha \in (0, 1/3)$ (the construction uses
  $\beta \in [6/5, 4/3)$ with $\beta > 1 + \alpha$).
  The printed statement for the class $\dot H^2(A,B)$ is not formalized; we
  do not know whether it holds.
- **Not formalized.** Appendix A of the paper, the explicit formula for
  $\varrho$, and the parts of Section 5.5 beyond (iii).
- **Classical inputs.** The paper uses several classical facts without proof:
  well-posedness, smoothness of solutions for smooth drifts, smooth dependence of flows on
  parameters, Liouville's theorem, and the energy identity for forced
  equations. These are all proved here.

## Repository layout

| Path | Contents |
|---|---|
| [AVenhance/Statements](AVenhance/Statements) | The public statements: the main theorems, the definitions they use, and the principal intermediate results of the paper (one declaration per file) |
| [AVenhance/Proofs](AVenhance/Proofs) | One short file per public theorem, closing it from the supporting library |
| [AVenhance/Infra](AVenhance/Infra) | The supporting library, organized by the sections of the paper (`Section3`, `Section4`, `Section5`), by topic (`Parabolic`, `Flow`, `FaaDiBruno`, `Heat`, `Ergodic`, …), and `FullTheorem` for parts (ii) and (iii) |
| [Homogenization](Homogenization) | Ambient-space and Sobolev definitions vendored from [CoarseGraining](https://github.com/scottnarmstrong/CoarseGraining) (Armstrong–Kuusi) |
| [Challenge.lean](Challenge.lean), [Solution.lean](Solution.lean), [comparator.json](comparator.json) | Independent statement check (below) |
| [doc](doc) | Errata to the paper |

The library has about 1,700 Lean files and 270,000 lines, all in Lean's
module system and none longer than 1,500 lines.

Principal intermediate results, stated in
[AVenhance/Statements](AVenhance/Statements) and proved in full:

| Paper | Lean |
|---|---|
| Well-posedness of weak solutions | `AVenhance.weak_wellposed` |
| Well-posedness of classical solutions for smooth drifts | `AVenhance.classical_wellposed` |
| Construction of the stream functions, §2 | `AVenhance.exists_isStreamSeq`, `AVenhance.stream_regularity`, `AVenhance.limit_field_regular` |
| Flows of the stream functions, §2.2 | `AVenhance.existsUnique_flow` |
| Recurrence for the renormalized diffusivities, §3.3 | `AVenhance.l_recurse` |
| Estimate of the nine error terms, §5.2 | `AVenhance.bigbound` |
| Step-down estimate of the energy cascade, §5.3 (corrected form) | `AVenhance.indystepdown` |
| Uniform time-regularity step, §5.3 | `AVenhance.lebron_step` |
| Theorem 1.1 | `AVenhance.anomalous_dissipation` |
| Theorem 1.1, uniform time regularity (§5.4), corrected no-selection principle (§5.5) | `AVenhance.anomalous_dissipation_full` |

## Independent statement check

[Challenge.lean](Challenge.lean) restates the main theorem using only Mathlib,
with every definition written out, and leaves its proof as the single
intentional `sorry` in the repository. [Solution.lean](Solution.lean) contains
the same text and proves the theorem from `AVenhance.anomalous_dissipation_full`;
the Challenge definitions agree with the library definitions by unfolding.
Lean's [comparator](https://github.com/leanprover/comparator), configured by
[comparator.json](comparator.json), checks that the two files state the same
theorem, that the Solution uses only the standard axioms, and replays the
Solution through Lean's kernel and the independent kernel checkers bundled
with the toolchain.

## Building and checking

Install [elan](https://github.com/leanprover/elan), then from the repository
root:

```sh
lake exe cache get   # download the Mathlib build cache
lake build           # build the library, Challenge and Solution
```

The toolchain is `leanprover/lean4:v4.35.0-rc2` with Mathlib `v4.35.0-rc2`.
A clean build of the library takes about an hour on an 8-core machine. To
print the axioms of the main theorem:

```sh
echo 'import AVenhance.Statements.FullTheorem.AnomalousDissipationFull
#print axioms AVenhance.anomalous_dissipation_full' > /tmp/Axioms.lean
lake env lean /tmp/Axioms.lean
```

To run the comparator as Palomar does (requires `bubblewrap`):

```sh
scripts/verify-comparator.sh
```

## How this formalization was made

The Lean code was written by AI models under the supervision of the authors,
who decided the mathematical statements, approved every public definition and
theorem statement before its proof was developed, and decided the corrections
to the paper. GPT-6 (luna and astra) and GPT-6.1 (sol) wrote most of the code
through Codex; Claude Opus 5.5 coordinated the work and wrote the later parts
with Claude Sonnet 5.5. Each public statement was compared against the paper
by an independent model review before its proof was accepted. The project took about
two and a half days.

## Authors and citation

Scott Armstrong and Vlad Vicol. If you use this formalization, please cite it
using [CITATION.cff](CITATION.cff), together with the paper.

## Acknowledgements

Scott Armstrong was supported by the European Research Council (ERC) under the
European Union's Horizon Europe research and innovation programme (grant
agreement No. 101200828). Vlad Vicol was partially supported by the
Collaborative NSF grant DMS-2307681 and by a Simons Investigator Award. Built
on Lean 4, Mathlib and Lake. The Sobolev carriers are taken from the
CoarseGraining formalization of Scott Armstrong and Tuomo Kuusi.

## License

Apache 2.0; see [LICENSE](LICENSE).
