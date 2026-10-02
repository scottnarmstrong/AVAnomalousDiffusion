# Contributing

This repository formalizes S. Armstrong and V. Vicol, *Anomalous diffusion by
fractal homogenization* (arXiv:2305.05048), in Lean 4 and Mathlib. The public
statements are in [AVenhance/Statements](AVenhance/Statements), one declaration
per file; their proofs are in [AVenhance/Proofs](AVenhance/Proofs) and the
supporting library in [AVenhance/Infra](AVenhance/Infra).

## Development environment

Install the pinned toolchain and obtain the Mathlib cache:

```sh
elan toolchain install leanprover/lean4:v4.35.0-rc2
lake exe cache get
lake build
```

Keep the committed `lake-manifest.json`. Avoid `lake update` and `lake clean`
when verifying this version: they can change dependencies or remove the cache.

## Lean source conventions

Lean files begin with the notice

```lean
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
```

followed by the `module` header; the vendored files in
[Homogenization](Homogenization) keep their own notice. All Lean files use
Lean's module system.

Library code contains no `sorry`, `admit` or custom axiom; the only
intentional `sorry` is the theorem body in [Challenge.lean](Challenge.lean),
proved in [Solution.lean](Solution.lean). Do not add heartbeat overrides.
Library files stay below 1,500 lines; split a file into focused modules when it
grows. The Challenge must stay below 1,000 lines and 100 KiB.

Changes to a statement in `AVenhance/Statements`, or to a definition it uses,
need mathematical review against the paper and a matching change to
`Challenge.lean` and `Solution.lean`.

## Checking a change

From the repository root:

```sh
lake build
python3 scripts/check-lean-sources.py
scripts/verify-comparator.sh
```

For a new public theorem, include its `#print axioms` output with the change.
