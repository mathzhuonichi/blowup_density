# Density of forces producing Navier–Stokes blowup

This project accompanies the paper *Density of Forces Producing Navier–Stokes
Blowup*. Its formalization focuses on the paper's two main density theorems
and the mathematical results needed to prove them:

- **Theorem 3.1:** subcritical force density for each fixed admissible initial
  velocity on the torus, and the sharp zero-initial-velocity threshold
  `s = 1/2` in `L¹_t Hˢ_x`.
- **Theorem 4.1:** the corresponding whole-space classifications, with
  thresholds `s = 1/2` in `L¹_t Hˢ_x` and `s = -1/2` in `L²_t Hˢ_x`.

Both main theorems are **Closed** in Lean. Some auxiliary statements and
broader variants are only partially formalized; the project does not claim
that every statement in the paper has been fully formalized.

## Read the project

- [Article](output/pdf/blowup_density_revised.pdf) and [TeX source](paper/revised/blowup_density_revised.tex)
- [Guide to this Project](output/pdf/formalization_guide.pdf) and [TeX source](paper/formalization_guide.tex)
- [Proof dependencies and coverage](formalization/blueprint/DEPENDENCY_GRAPH.md)
- [Article-to-code correspondence](formalization/blueprint/RESULT_MAP.md)
- Original PDFs: [Paper 1](paper/originals/local/paper_1_theory.pdf), [Paper 3](paper/originals/local/paper_3_whole_space.pdf)
- [Reference corpus](reference/README.md)

## Formalization scope

**Closed** means that the complete stated result has a Lean kernel-checked
proof, including all auxiliary results and their instantiations. No unproved
theorem input, admission or extra axiom is allowed. The result's stated
mathematical hypotheses and the standard logical axioms `propext`,
`Classical.choice` and `Quot.sound` remain. **Partial** means that some of the
article statement is not yet covered by such a proof.

The article-level inventory contains **22 Closed and 5 Partial entries**.
A single proposition may contain both Closed and Partial parts. The
[proof graph](formalization/blueprint/DEPENDENCY_GRAPH.md) separates these parts:
green nodes are Closed, and orange nodes are Partial. Solid arrows show proof
dependencies; dashed arrows identify unfinished extensions of proved cases.

The remaining Partial article entries are Proposition 2.1,
Lemma 3.5, Theorem 3.6, and Propositions 3.16 and 3.17.

## Check the Lean project

Use Lean **4.34.0-rc2** and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`, as fixed by the checked-in manifests.
Run in Linux with elan and Python 3:

```sh
lake -d verification exe cache get
make check
make test
make test-mutations
```

For macOS 27, use a Linux VM with the pinned toolchain; see the
[saved software sources](reference/web/README.md).

To reproduce the article-declaration axiom audit:

```sh
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
