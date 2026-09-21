# Density of forces producing Navier–Stokes blowup

This project accompanies the paper *Density of Forces Producing Navier–Stokes
Blowup*. Its formalization focuses on the paper's two main density theorems
and the mathematical results needed to prove them:

- **Theorem 3.1:** subcritical force density for each fixed admissible initial
  velocity on the torus, and the sharp zero-initial-velocity threshold
  `s = 1/2` in `L¹_t Hˢ_x`.
- **Theorem 4.1:** the corresponding whole-space classifications, with
  thresholds `s = 1/2` in `L¹_t Hˢ_x` and `s = -1/2` in `L²_t Hˢ_x`.

Both main theorems and all 25 other mapped article entries are **Closed** in
Lean. Claims outside the mapped article scope are not part of this inventory.

## Read the project

- [Article](paper/blowup_density_revised.pdf) and [TeX source](paper/revised/blowup_density_revised.tex)
- [Guide to this Project](paper/formalization_guide.pdf) and [TeX source](paper/formalization_guide.tex)
- [Proof dependencies and coverage](formalization/blueprint/DEPENDENCY_GRAPH.md)
- [Article-to-code correspondence](formalization/blueprint/RESULT_MAP.md)
- Original PDFs: [Paper 1](paper/originals/local/paper_1_theory.pdf), [Paper 3](paper/originals/local/paper_3_whole_space.pdf)
- [Reference corpus](reference/README.md)

## Repository layout

- [.github/](.github/): GitHub Actions workflows for source checks and Lean builds.
- [experiments/](experiments/): Python scripts for source, interface, axiom and document checks.
- [formalization/](formalization/): Lean proofs, the main Lake package and article-to-code proof maps.
- [paper/](paper/): Article and guide sources, their PDFs and the original manuscripts.
- [reference/](reference/): Cited literature, archived software sources and provenance records.
- [vendor/](vendor/): Upstream Lean modules used in the build, with their licenses and package configuration.
- [verification/](verification/): Independent theorem specifications, implementation bindings and Lean acceptance checks.

## Formalization scope

**Closed** means that the complete stated result has a Lean kernel-checked
proof, including all auxiliary results and their instantiations. No unproved
theorem input, admission or extra axiom is allowed. The result's stated
mathematical hypotheses and the standard logical axioms `propext`,
`Classical.choice` and `Quot.sound` remain.

The article-level inventory contains **27 Closed entries**. The
[proof graph](formalization/blueprint/DEPENDENCY_GRAPH.md) records their exact
scope and dependencies.

## Check the Lean project

Use Lean **4.34.0-rc2** and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, as fixed by the checked-in manifests.
Run in Linux with elan and Python 3:

```sh
lake -d verification exe cache get
lake -d verification build
```

On macOS 27, use a Linux VM: the pinned Lean 4.34.0-rc2 toolchain has a
[Lake memory-allocation crash (leanprover/lean4#15087)](https://github.com/leanprover/lean4/issues/15087).

To reproduce the source and article-declaration audits:

```sh
python3 experiments/check_formalization_plan.py --check
python3 experiments/check_contracts.py --summary
python3 experiments/audit_article_axioms.py --build --output-dir /tmp/article-audit
```

This checks actual declaration dependencies with `Lean.collectAxioms`.
Statement scope and auxiliary-input closure are reviewed separately; an
axiom check alone is not a completeness test. See
[verification/README.md](verification/README.md).

## Upstream sources

`vendor/` retains the upstream Lean modules used by the project, their licenses
and required package configuration. HeliCorgi is an in-place source library
under the main pin. The full downloaded OpenAI archive and the literature
corpus remain in `reference/`. See
[source provenance](formalization/blueprint/EXTERNAL_REUSE.md).
