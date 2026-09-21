# Reference corpus and source provenance

This directory contains the literature and software sources for the
[article](../paper/blowup_density_revised.pdf) and
[formalization guide](../paper/formalization_guide.pdf). The current project
formalizes both main density theorems and all 27 mapped article results.
The [result map](../formalization/blueprint/RESULT_MAP.md) records their proof
locations; the [closure review](../formalization/blueprint/CLOSURE_AUDIT.md)
and [kernel audit](../formalization/blueprint/AXIOM_AUDIT.json) record the
statement scope and transitive-axiom checks.

## Corpus inventory

[SOURCES.md](SOURCES.md) lists the 18 distinct works cited by the article and
guide. [sources.json](sources.json) records their bibliography text, citation
keys, local files, SHA-256 hashes, source URLs and version notes. Coverage is:

- 15 works with full text, including the Berselli–Spirito article and Hunter's full PDE notes.
- One complete OpenAI source archive at the recorded revision.
- Two works with the complete cited chapters: Taylor's PDE I and PDE III, rather than the complete books.

The [article bibliography](../paper/revised/references.tex) and the guide use
these records. The source index distinguishes author drafts, published PDFs,
arXiv versions and HTML snapshots; page locators below refer to the saved
version. Availability and file hashes establish the source inventory, while
mathematical scope and formal proof closure are recorded separately.

## Software sources and formalization

The OpenAI archive
[OpenAI_NavierStokesAndEuler_8937a8f.tar.gz](OpenAI_NavierStokesAndEuler_8937a8f.tar.gz)
preserves revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`.
[R3ActualCandidate.lean](R3ActualCandidate.lean) and
[R3CompactCandidate.lean](R3CompactCandidate.lean) are retained source copies.
The selected modules used by the build live in
[vendor/NavierStokesAndEuler](../vendor/NavierStokesAndEuler/); that tree is
a maintained dependency subset, not an untouched copy of the full archive.
The local `Source.source_breakdown` proves the complete article Theorem 1.1
for the selected force, including the global nonexistence conclusion.

The retained [HeliCorgi modules](../vendor/HeliCorgi/) come from revision
`de518485776d1d8de60f0c51151121df71e3ab6d` of
[ns-mns2-flowmap-bridge](https://github.com/HeliCorgi/ns-mns2-flowmap-bridge).
They compile in place as dependencies of the current proofs. The local
formalization supplies the forced classical-solution statements and their
adapters; the upstream unforced distributional theorem is not identified
with those statements. Both upstream licenses are retained. See the
[reuse record](../formalization/blueprint/EXTERNAL_REUSE.md) for package scope.

The project pins Lean 4.34.0-rc2 and Mathlib
`85e3a25e006c35636f0e53b0e9296caca2685bc0`.
[web/](web/README.md) contains saved software issue reports and Mathlib
definition snapshots. The pinned Lake version's macOS 27 crash is documented
in [Lean issue #15087](https://github.com/leanprover/lean4/issues/15087);
the supported build instructions use Linux.

## Article citations and formal proof routes

The current article has four sections. The analytic material from earlier
appendices is incorporated into Section 2 and the relevant proofs. The guide
maps the statements to Lean and explains the proof-method comparisons:

- Proposition 2.1 is formalized for locally smooth forcing on both domains,
  without global time-integrability or compact temporal support assumptions.
  The density proofs retain the original whole-space H7 and periodic H3
  construction and continuation routes. Fixed-force H1-uniform restart and
  endpoint continuation are also proved for the density force classes.
- Propositions 3.16 and 3.17 include every nonempty bounded open domain.
  Their formal proofs retain the finite-superposition and energy/IBP arguments;
  the required integration identity is proved without a boundary-shape premise.
- For fractional localization, the article cites coordinate localization and
  interpolation, while Lean proves the torus estimate by fractional-energy
  identities and a direct kernel comparison.
- For critical regularity, the article cites forced critical fixed-point
  theory; the Lean density proofs retain their critical energy estimates,
  smallness bootstrap and high-order continuation argument.

Literature citations provide the mathematical references and comparisons.
They are not unproved Lean axioms. The exact statement hypotheses, proved
adaptations and implementation locations are given in guide Sections 2–4.

## Classical source locators

These locators refer to the saved primary texts. Specializations and changes
of convention are stated explicitly in the article or guide. Author-draft
pagination is not attributed to a published edition.

| Topic | Primary source and exact locator | Use and adaptation |
|---|---|---|
| H2 boundedness | Tao, *Nonlinear Dispersive Equations*, author draft, Appendix A, (A.13), printed p. 336 | Set dimension 3 and order 2; apply componentwise and convert to derivative norms by Plancherel. No claim of identical numerical constants. |
| Sobolev algebra and tame products | Same draft, Lemma A.8, (A.17)-(A.18), printed p. 338 | Combine (A.17) with (A.13) for the H2 low norm; take components for scalar-vector products. |
| Euclidean fractional energy | Di Nezza, Palatucci, Valdinoci, arXiv:1104.4345v3, Proposition 3.4, pp. 16-17 | Specialize to dimension 3 and real vector components, adjusting Fourier normalization. |
| Periodic fractional energy | Roncal and Stinga, arXiv:1209.6104v3, Theorem 1.5, (1.6)-(1.8), p. 3, and (1.1), p. 1 | Pair the operator with the function and symmetrize, then use Parseval with sigma=2s. Rescale the 2pi-periodic torus to period one. This is a derived energy identity, not their literal theorem statement. |
| Spatial approximation | Taylor, PDE I, author Chapter 4, Section 1, Exercise 1, p. 5 | The exercise states Schwartz density at every real order. A large spatial cutoff converges in the Schwartz topology, giving compactly supported smooth approximants. |
| Bochner approximation | Hunter, Appendix 6.A, Proposition 6.29, p. 200 | The source treats a finite interval. Truncate the integrable q-th power tail before applying it on the positive half-line, q finite. |
| Ball vector potential | Petersen, saved author notes, Section 7.1, Lemma 7.1.2, pp. 127-128; Lemma 7.1.5, p. 129 | Apply the homotopy formula to the closed 2-form associated to the divergence-free field and radial contraction. Differentiate under the compact parameter integral for smooth time dependence. |
| NS local theory, uniqueness and continuation | Tao (2013), Theorems 5.1(ii)-(iv), p. 48, and 5.4(ii)-(iv), pp. 52-53; Lemma 4.1(i), (40), pp. 44-45; Corollary 5.2, p. 50 | These give local theory, pressure normalization and periodic maximal development. The exact squared-H2 criterion and H7/H3 fixed-force restart remain derived arguments, as explained in guide Section 3. |
| Smooth cutoffs | Petersen, saved author notes, Section 1.3.1, Corollary 1.3.4 | Nested relatively compact neighborhoods supply a compactly supported cutoff with a plateau. |
| Fourier and Bochner conventions | Taylor, saved PDE I Chapter 3, Sections 3–4, and Chapter 4, Sections 1 and 3; Hunter, Appendix 6.A, Definitions 6.14 and 6.27 | The manuscript records its Fourier normalization, multiplier notation and time-norm conventions. |
| Smooth multiplication and coordinate localization | Taylor, saved PDE I Chapter 4, Section 2, (2.19), and Sections 2–3 | The article uses these for multiplication at real Sobolev orders and coordinate localization on compact manifolds. |
| Torus Sobolev embedding | Taylor, saved PDE III Chapter 13, Section 6, Proposition 6.4, (6.13), and preceding compact-manifold discussion | The inhomogeneous embedding is combined with the explicit mean-zero spectral-gap conversion. |
| Forced critical theory | Danchin, Theorem 2.3.1 and Lemma 2.3.2, pp. 47–49; Theorem 2.2.5 and the periodic discussion, p. 44 | The article uses critical fixed-point theory and finite-time heat estimates. Mean removal and the inhomogeneous finite-horizon adjustment are deductions; the Lean proof route is described above. |
| Critical stability precedent | Marin-Rubio, Robinson and Sadowski, accepted manuscript, Theorem 3, pp. 6–7 | The result concerns H1/2 initial perturbations and L2 H-1/2 forcing on a mean-zero periodic domain; it is not a whole-space or L1-forcing theorem. |

For the whole-space inhomogeneous L2 endpoint, the article uses the space
C H1/2 intersect L2 H3/2 after viscosity rescaling. Its heat estimate and
bilinear contraction give a radius of the form c nu^(3/2) exp(-C nu S).
A homogeneous negative-order small-data theorem alone does not supply this
step. The non-density argument uses stability of the zero solution.

## Construction and contextual sources

| Source | Locator | Role |
|---|---|---|
| OpenAI, *Finite Time Blowup for Navier–Stokes* | Theorem 1.1, p. 1; pinned source archive above | Compact forced blowup construction and the corresponding upstream Lean proof, connected to article Theorem 1.1. |
| Enciso, Peñafiel-Tomás and Peralta-Salas, published article (2025) | Theorem 1.5, p. 5; Lemma 2.11, p. 17; Lemmas 11.1–11.2, pp. 70–71; Section 11.3, pp. 75–77 | A gluing precedent for weak unforced Euler solutions. The article distinguishes that setting from classical forced Navier–Stokes solutions. |
| Hofmanová, Zhu and Zhu, arXiv v2 | Theorem 1.4, pp. 4–5; Corollary 4.6 and Theorem 5.1, p. 24 | Force-density and general-initial-data context for weak nonuniqueness, rather than the source of the classical blowup construction. |
| Fefferman, Clay problem statement | Equations (4)–(5), p. 1 | Initial Schwartz regularity and force-derivative decay conventions for the rapid-decay class. |
| Tao, 254A Notes 1 (2018) | Theorem 45 | Unforced mean-zero periodic small-data precedent; the forced estimates and mean treatment are proved separately. |
| Berselli and Spirito (2021) | Definition 1 and Remark 4 | Energy-class solutions and forcing conventions. The complete article is saved as [Berselli_Spirito_2021_Leray_Hopf.pdf](Berselli_Spirito_2021_Leray_Hopf.pdf). |
| Guermond, Minev and Shen (2006) | Section 2, (2.2)–(2.3), and Theorem 3.2, p. 6014 | The distinction between energy spaces and stronger numerical-error hypotheses; no numerical convergence result is claimed for the constructed flow. |

Canonical URLs and bibliographic metadata for these works are in
[sources.json](sources.json). The guide uses the recorded source versions and
identifies consequences or specializations rather than claiming verbatim
agreement between every literature statement and its formal counterpart.

## Earlier manuscripts and background notes

- The original Paper 1 and Paper 3 PDFs are in [paper/originals/local](../paper/originals/local/). The saved [torus preprint](Cao_Chi_2026_arXiv_2609.10262v1_Torus_Paper1.pdf) precedes the current combined article.
- [Sobolev notation sources](SOBOLEV_NOTATION_SOURCES_20260912.md) and the [PDE gluing survey](URYSOHN_GLUING_LITERATURE_20260912.md) retain the dated source-reading records. Their old appendix references and acquisition updates describe those earlier stages.
- [TERMINOLOGY.md](TERMINOLOGY.md) records the current prose conventions; the related background PDFs remain available for comparison.
- The [Fujita–Kato publisher record](Fujita_Kato_1964.html) is archived background only. Its full text was not obtained, and it is not part of the active bibliography; `sources.json` records it under `archived_sources`.

## Checking the corpus

From the repository root, run:

```sh
python3 experiments/check_reader_documents.py
```

This checks bibliography agreement, source hashes, document references and
article-to-code mappings. Lean build and kernel-audit commands are documented
in the [project README](../README.md#check-the-lean-project).
