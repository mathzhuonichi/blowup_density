# Citation sources and scope

## Current local corpus

[SOURCES.md](SOURCES.md) indexes all 18 active works in the revised article and guide.
[sources.json](sources.json) records their canonical bibliography text, citation
keys, local files, SHA-256 hashes, PDF page counts, source URLs and version notes.
The bibliography formatting is conventional; detailed theorem/page locators
and source adaptations remain in this audit record and in the citing text.

Coverage is explicit: 16 works have full text or the pinned software archive;
Taylor I and III have the complete cited chapters. Fujita--Kato (1964),
now removed from the active bibliography, retains only a publisher-page snapshot. Full-text requests redirected to subscription
content, the DTIC route failed, and no downloadable public copy was obtained.
Its earlier historical citation was removed at the user request; the source
record remains archived and has not been substituted for a proof reference.

Newly acquired: Berselli--Spirito's 20-page article, Hunter's 242-page full
notes, the Clay monograph PDF, and the 6 MB OpenAI source archive at commit
8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538. Existing cited originals were retained
and checked for PDF readability. [web/](web/README.md) preserves the software
issue and Mathlib definition sources used by the guide.

Earlier acquisition-status notes below describe prior audit stages; this
current corpus inventory supersedes them. Availability does not yet establish
that every mathematical citation has been verified.

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

The original local Paper 1 and Paper 3 PDFs are preserved in
[paper/originals/local](../paper/originals/local/). The OpenAI reference PDF
already stored here was compared with the previous local source copy. No
separate HeliCorgi paper PDF has been identified; the source repository itself
is the formalization reference.

The torus-only predecessor of the merged article was posted as
arXiv:2609.10262v1 [math.AP] on 9 September 2026 (Cao and Chi, 22 pages). It is
saved here as `Cao_Chi_2026_arXiv_2609.10262v1_Torus_Paper1.pdf`; its text is
identical to `paper/originals/local/paper_1_theory.pdf` apart from the arXiv
stamp, and its results are renumbered into Section 3 of the merged article
(see the [historical correspondence record](https://github.com/mathzhuonichi/blowup_density/blob/ffe8d7c201882fcaf95e0d74b4d432f906ab86b4/logs/THEOREM_CORRESPONDENCE.md)).

## Manuscript citation audit

The audit below describes the retained 12 September manuscript. In the current
reader revision, the two appendices have been absorbed into Section 2 and the
local applications. See the current revision record for the shortened proofs.


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
[Appendix reduction review](https://github.com/mathzhuonichi/blowup_density/blob/ffe8d7c201882fcaf95e0d74b4d432f906ab86b4/logs/APPENDIX_REDUCTION_INDEPENDENT_REVIEW_20260912.md).

For the separate survey of smooth cutoff constructions in other PDEs, see
[Smooth cutoff constructions and PDE gluing](URYSOHN_GLUING_LITERATURE_20260912.md).
It records downloaded primary texts, construction locators, and the
similarities and differences relative to Papers 1 and 3. The published Euler
article is now cited in the manuscript; the other survey sources remain
background reading.

The current article bibliography is maintained in `../paper/revised/references.tex`. The following
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

## Reader revision and formalization companion (20 September 2026)

The [source inventory](SOURCES.md) records the primary texts for the
[article revision](../paper/revised/) and
[formalization companion](../paper/formalization_guide.tex). The companion
explains why fixed-force H7 restart on the whole space and H3 restart on the
torus suffice after the high-order energy estimate. Tao's published local
theory supports the analytic reasoning, but does not establish a lower bound
for the particular high-order horizon selected by the Lean construction.
The named H1 restart obligations remain separate from the proved integral
continuation conclusion.


The [terminology conventions](TERMINOLOGY.md) fix the two reader documents'
vocabulary against the Euler paper (Lemma 2.11 and Sections 11.1, 11.3),
Tao's local theory, and the Clay statement. In particular, exposition uses
“gluing” and “building block”; historical Lean identifiers remain unchanged.


## Classical results used in the concise revision

- Petersen, *Manifolds, Transversality, and de Rham Cohomology*, Section 1.3.1,
  Corollary 1.3.4: smooth Urysohn lemma. The author's full text was saved as
  `Petersen_Manifolds_Author.pdf` from
  [the UCLA author page](https://www.math.ucla.edu/~petersen/manifolds.pdf),
  accessed 20 September 2026. Compact support and a plateau follow by choosing
  nested relatively compact neighborhoods before applying the lemma.
- Taylor, saved PDE I Chapter 4: Section 2, (2.19), for smooth multiplication
  on every real-order Sobolev space; Sections 2–3 for localization on compact
  manifolds; Section 1, Exercise 1, for Schwartz density in Hs.
- Hunter, saved Appendix 6.A, Proposition 6.29, p. 200: density of finite sums
  of smooth compactly supported time functions with Banach-valued coefficients.
  After spatial coefficient approximation and finite-time truncation, this
  supplies the jointly compact smooth approximation used in Section 4.

The Mathlib compatibility note is supported by
[PR 42406](https://github.com/leanprover-community/mathlib4/pull/42406) and its
[incorporated commit 8319c83](https://github.com/leanprover-community/mathlib4/commit/8319c83af32e262ad477c8a896a0859cdd061b16),
not a claim that the mathematical definition of classical Lp spaces changed.

## Guide Section 4: located classical sources

Each item now states the literature locator and whether the formal version
is a specialization or a consequence. The guide retains the implementation
declarations and their checked source line numbers.

| Guide item | Primary source and exact locator | Passage from source to formal version |
|---|---|---|
| H2 boundedness | Tao, *Nonlinear Dispersive Equations*, author draft, Appendix A, (A.13), printed p. 336 | Set dimension 3 and order 2; apply componentwise and convert to derivative norms by Plancherel. No claim of identical numerical constants. |
| Sobolev algebra and tame products | Same draft, Lemma A.8, (A.17)-(A.18), printed p. 338 | Combine (A.17) with (A.13) for the H2 low norm; take components for scalar-vector products. |
| Euclidean fractional energy | Di Nezza, Palatucci, Valdinoci, arXiv:1104.4345v3, Proposition 3.4, pp. 16-17 | Specialize to dimension 3 and real vector components, adjusting Fourier normalization. |
| Periodic fractional energy | Roncal and Stinga, arXiv:1209.6104v3, Theorem 1.5, (1.6)-(1.8), p. 3, and (1.1), p. 1 | Pair the operator with the function and symmetrize, then use Parseval with sigma=2s. Rescale the 2pi-periodic torus to period one. This is a derived energy identity, not their literal theorem statement. |
| Spatial approximation | Taylor, PDE I, author Chapter 4, Section 1, Exercise 1, p. 5 | The exercise states Schwartz density at every real order. A large spatial cutoff converges in the Schwartz topology, giving compactly supported smooth approximants. |
| Bochner approximation | Hunter, Appendix 6.A, Proposition 6.29, p. 200 | The source treats a finite interval. Truncate the integrable q-th power tail before applying it on the positive half-line, q finite. |
| Ball vector potential | Petersen, saved author notes, Section 7.1, Lemma 7.1.2, pp. 127-128; Lemma 7.1.5, p. 129 | Apply the homotopy formula to the closed 2-form associated to the divergence-free field and radial contraction. Differentiate under the compact parameter integral for smooth time dependence. |
| NS local theory, uniqueness and continuation | Tao (2013), Theorems 5.1(ii)-(iv), p. 48, and 5.4(ii)-(iv), pp. 52-53; Lemma 4.1(i), (40), pp. 44-45; Corollary 5.2, p. 50 | These give local theory, pressure normalization and periodic maximal development. The exact squared-H2 criterion and H7/H3 fixed-force restart remain derived arguments, as explained in guide Section 3. |

New saved primary texts:

- [DiNezza_Palatucci_Valdinoci_Fractional_Sobolev_v3.pdf](DiNezza_Palatucci_Valdinoci_Fractional_Sobolev_v3.pdf), downloaded from https://arxiv.org/pdf/1104.4345v3.
- [Roncal_Stinga_Fractional_Laplacian_Torus_v3.pdf](Roncal_Stinga_Fractional_Laplacian_Torus_v3.pdf), downloaded from https://arxiv.org/pdf/1209.6104v3.

All locators were checked against the saved primary text, including printed
pagination rather than assuming that PDF page indices equal printed pages.

## Critical stability and the non-density obstruction

- R. Danchin, *Fourier Analysis Methods for PDE's*, 14 November 2005; saved
  as [Danchin_Fourier_Analysis_Methods_for_PDEs.pdf](Danchin_Fourier_Analysis_Methods_for_PDEs.pdf)
  from https://perso.math.u-pem.fr/danchin.raphael/cours/courschine.pdf.
  Theorem 2.3.1, p. 47, and its proof, pp. 48-49, include an external force
  in the Chemin-Lerner L1 critical Besov space. At p=r=2, ordinary L1 in
  homogeneous H1/2 embeds into this force class by Minkowski. Theorem 2.2.5
  and the periodic discussion on p. 44 give the inhomogeneous finite-time
  heat estimate and its mean-zero periodic version. Lemma 2.3.2, p. 48, is
  the bilinear contraction lemma. These replace the long energy proofs in
  revised Propositions 3.8, 4.3 and 4.4. The mean-removing Galilean transform
  and inhomogeneous finite-time adjustment are explicit deductions, not
  quoted verbatim theorems.
- P. Marin-Rubio, J. C. Robinson and W. Sadowski, JMAA 400(1) (2013), 76-85,
  DOI 10.1016/j.jmaa.2012.10.064; saved as
  [MarinRubio_Robinson_Sadowski_2013_Robustness.pdf](MarinRubio_Robinson_Sadowski_2013_Robustness.pdf)
  from https://idus.us.es/server/api/core/bitstreams/b0e9a174-2dd3-484d-9a9d-39ec5ee1323c/content.
  Theorem 3, author-manuscript pp. 6-7, treats robustness on a finite interval
  under initial H1/2 and external L2 H-1/2 perturbations on a mean-zero
  periodic domain. It is cited as a direct stability precedent, not as a
  theorem on R3 or on L1 forcing.

For the R3 inhomogeneous L2 endpoint the manuscript uses the X_L space
C H1/2 intersect L2 H3/2 after viscosity rescaling. Heat maximal regularity
and H1 times H1 into H1/2 give a bilinear contraction with constants bounded
by C exp(CL). This yields a radius c nu^(3/2) exp(-C nu S). A homogeneous
negative-order small-data theorem alone would not justify this step.
The non-density argument needs stability of the zero solution only; no
claim about all nonzero reference solutions is inferred.
