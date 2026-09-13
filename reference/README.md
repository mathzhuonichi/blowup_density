# Citation sources and scope

## Formalization source packages

The Section 4 proof plan now compares both
[OpenAI's source package](../vendor/NavierStokesAndEuler/) and
[HeliCorgi's concrete R3 package](../vendor/HeliCorgi/), with pinned metadata
and exact applicability limits in the
[external reuse audit](../formalization/blueprint/EXTERNAL_REUSE.md).
HeliCorgi's snapshot is revision
`de518485776d1d8de60f0c51151121df71e3ab6d` of
[ns-mns2-flowmap-bridge](https://github.com/HeliCorgi/ns-mns2-flowmap-bridge).
Its generic pressure, operator, mild existence and restart results are
reusable; its top-level PDE theorem is unforced and spatially distributional.
The package is not a replacement for the manuscript's forced classical
local-theory statement without the adapters identified in that audit.

The original local Paper 1 and Paper 3 PDF/TeX pairs are preserved in
[paper/originals/local](../paper/originals/local/). The OpenAI reference PDF
already stored here was compared with the previous local source copy. No
separate HeliCorgi paper PDF has been identified; the source repository itself
is the formalization reference.

## Manuscript citation audit

For the source and convention audit of the introductory notation, see
[Sources for the introductory notation](SOBOLEV_NOTATION_SOURCES_20260912.md).
It verifies Taylor's Euclidean Fourier/Sobolev convention, Hunter's Bochner
definitions, and Tao's homogeneous norm formula with its normalization
conversion. All three references are now cited as background in the
introduction, with the manuscript's own definitions retained and differences
explained in footnotes.
The same record now includes a direct-source map for Appendices A and B,
including the forced local theory in Tao's published 2013 paper and the
compact-manifold embedding in Taylor's Chapter 13. These two additional
sources have been downloaded and are now cited in the respective appendices.
The reduction was independently reviewed; see
[Appendix reduction review](../logs/APPENDIX_REDUCTION_INDEPENDENT_REVIEW_20260912.md).

For the separate survey of smooth cutoff constructions in other PDEs, see
[Smooth cutoff constructions and PDE gluing](URYSOHN_GLUING_LITERATURE_20260912.md).
It records downloaded primary texts, construction locators, and the
similarities and differences relative to Papers 1 and 3. The published Euler
article is now cited in the manuscript; the other survey sources remain
background reading.

The bibliography is maintained in `../paper/references.tex`. The following
sources were checked for this consolidation on 12 September 2026. The external
compact blowup theorem supplies the singular construction. Classical local
existence and Sobolev embeddings are cited as separate analytic inputs.
The article retains its normalization and homogeneous-realization details,
the exact continuation argument, the short multiplication proof, and the
critical force estimates.

| Reference | Locator and role | Availability and verification |
|---|---|---|
| Taylor, *Partial Differential Equations I: Basic Theory*, second edition (2011) | Chapter 3, Sections 3–4; Chapter 4, Sections 1 and 3: Fourier transforms, distributions, and Sobolev spaces | Publisher metadata checked; definitions read in the saved author chapter files `Taylor_PDE_I_Chapter3_Author.pdf` and `Taylor_PDE_I_Chapter4_Author.pdf`. The introduction cites this as background and explains the multiplier notation and periodic normalization differences. |
| Hunter, *Notes on Partial Differential Equations* | Appendix 6.A, Definitions 6.14 and 6.27: strong measurability and Bochner norms | Author's chapter saved as `Hunter_Vector_Valued_Functions.pdf`; the finite-interval, Banach-valued source setting is identified in a footnote. |
| Tao, *Nonlinear Dispersive Equations: Local and Global Analysis* (2006) | Appendix A: homogeneous norm formulas, embedding (A.11), and product estimate in Lemma A.8 | AMS metadata checked; formulas read in `Tao_Nonlinear_Dispersive_Equations_Author_Draft.pdf`, whose pagination is not attributed to the published edition. Cited in the introduction and Appendices A and B. A footnote explains the Fourier normalization conversion; the manuscript retains its own homogeneous realizations. |
| Tao, *Localisation and compactness properties of the Navier–Stokes global regularity problem* (2013) | Theorems 5.1(ii)–(iv), 5.4(ii)–(iv); Corollary 5.2; Section 3, (36)–(38) | Publisher PDF saved as `Tao_2013_Localisation_Compactness_Published.pdf`. Used for forced local theory in Appendix A, with explicit viscosity, mean, projected-force/pressure, and smoothness adaptations. The displayed continuation criterion remains proved as a consequence. |
| Taylor, *Partial Differential Equations III: Nonlinear Equations*, second edition (2011) | Chapter 13, Section 6, Proposition 6.4, (6.13), and preceding compact-manifold discussion | Publisher metadata checked; author chapter saved as `Taylor_PDE_III_Chapter13_Author.pdf`. Cited in Appendix B for the inhomogeneous torus embedding; the zero-mean spectral-gap conversion remains explicit. |
| Enciso, Peñafiel-Tomás, and Peralta-Salas | *Forum of Mathematics, Pi* 13 (2025), e21, 1–84; DOI `10.1017/fmp.2025.10012`; Theorem 1.5 (p. 5), Lemma 2.11 (p. 17), Lemmas 11.1–11.2 (pp. 70–71), Section 11.3 (pp. 75–77) | Publisher PDF downloaded as `Enciso_PenafielTomas_PeraltaSalas_2025_Published.pdf`. The stated result and construction passages were read in this published version. Cited in the introduction as a close methodological precedent for local singular insertion, with the weak unforced Euler setting distinguished from the present classical forced NS setting. |
| OpenAI, *Finite Time Blowup for Navier--Stokes* | Theorem 1.1, p. 1: compact smooth force, compact velocity and pressure, zero initial velocity, bounded energy, and unbounded speed at time one, for each positive viscosity | Official PDF opened; statement matched to merged Theorem 1.1. A previously downloaded full text is saved as `OpenAI_Finite_Time_Blowup_for_Navier_Stokes.pdf`. The external 166-page construction was not reproved in this editorial task. |
| OpenAI, *NavierStokesAndEuler* | Revision `8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538`; `R3ActualCandidate.lean`, lines 18--21; `R3CompactCandidate.lean`, lines 24--37 | Pinned repository page opened and local source declarations inspected. The two relevant source files are copied here. No Lean build or certification of the merged article is claimed. |
| Hofmanova, Zhu, and Zhu | arXiv:2309.03668v2, Theorem 1.4 (pp. 4--5), Corollary 4.6 and Theorem 5.1 (p. 24) | Full text saved as `HZZ_2024_Navier_Stokes.pdf`; the cited deterministic force-density and general-initial-data statements were read. This is context about weak nonuniqueness, not the source of the classical blowup solution. |
| Fefferman, Clay problem statement | Equations (4)--(5), p. 1 | Official PDF opened and saved copy inspected. The initial Schwartz condition and all force-derivative decay conditions match the rapid-decay class in Section 4.5. Saved as `Clay_Fefferman_Navier_Stokes.pdf`. |
| Fujita and Kato | *Archive for Rational Mechanics and Analysis* 16 (1964), 269--315; DOI `10.1007/BF00276188` | Publisher metadata checked. `Fujita_Kato_1964.html` is a publisher-page snapshot, not a full-text PDF. Cited for historical background only; no theorem is imported from this paywalled text. |
| Tao, 254A Notes 1 | Author's notes, 16 September 2018; Theorem 45 | Author's page opened; local HTML snapshot saved. Theorem 45 was checked online: it gives global existence from small critical, mean-zero periodic initial data without forcing. Cited before Proposition 3.8 as the unforced precedent for the classical small-data argument; the precise forced version and mean treatment remain proved in this manuscript. |
| Berselli and Spirito | *Fluids* 6(1) (2021), 42; Definition 1 and Remark 4 | Publisher metadata and the institutional full-text indexed passage at Remark 4 were consulted for the energy-class and forcing discussion. Direct full-text saving was blocked by HTTP 403; no local PDF is represented as available. This reference is contextual, not a proof dependency. |
| Guermond, Minev, and Shen | *Computer Methods in Applied Mechanics and Engineering* 195 (2006), 6011--6045; Section 2 and Theorem 3.2, p. 6014 | The author-hosted full text was downloaded as `Guermond_Minev_Shen_2006.pdf`. Section 2, equations (2.2)--(2.3), and Theorem 3.2 were read. The theorem assumes an initialization hypothesis and sufficient space-time smoothness. We cite only the distinction between energy spaces and stronger error hypotheses, not a numerical convergence theorem for our constructed flow. Later online requests failed, but the initial saved PDF is complete and readable. |

## Primary links

- [Enciso–Peñafiel-Tomás–Peralta-Salas, published article](https://doi.org/10.1017/fmp.2025.10012)
- [OpenAI manuscript](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf)
- [Pinned source repository](https://github.com/openai/NavierStokesAndEuler/tree/8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538)
- [Hofmanova--Zhu--Zhu, version 2](https://arxiv.org/abs/2309.03668v2)
- [Clay problem statement](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
- [Fujita--Kato publisher record](https://doi.org/10.1007/BF00276188)
- [Tao's original notes](https://terrytao.wordpress.com/2018/09/16/254a-notes-1-local-well-posedness-of-the-navier-stokes-equations/)
- [Berselli--Spirito DOI](https://doi.org/10.3390/fluids6010042) and [institutional copy](https://arpi.unipi.it/retrieve/e0d6c930-5f68-fcf8-e053-d805fe0aa794/Fluids2021.pdf)
- [Guermond--Minev--Shen DOI](https://doi.org/10.1016/j.cma.2005.10.010) and [author copy](https://people.tamu.edu/~guermond/PUBLICATIONS/guermond_minev_shen_CMAME_2006.pdf)

Tao's 2013 article is now an explicit proof dependency, with verified theorem
locators. The two identical original embedding appendices are combined into
one concise appendix. The Urysohn cutoff construction is explained directly
by mollification, so no new external theorem is needed for that step.
