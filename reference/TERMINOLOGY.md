# Terminology for the reader documents

These conventions apply to the reader revision in `paper/revised/` and the
formalization companion. They fix vocabulary by mathematical role; they do not
claim that every earlier alternative is nonstandard or incorrect. A new
revision should retain these choices unless an explicit mathematical distinction
requires a change. Original bibliographic titles, quotations, Lean identifiers
and historical LaTeX labels retain their original spelling.

## Primary basis

Enciso, Peñafiel-Tomás and Peralta-Salas, *An extension theorem for weak solutions
of the 3d incompressible Euler equations and applications to singular flows*,
Forum of Mathematics, Pi 13 (2025), e21, 1–84,
[DOI](https://doi.org/10.1017/fmp.2025.10012), saved as
`Enciso_PenafielTomas_PeraltaSalas_2025_Published.pdf`:

- Theorem 1.5, p. 5: a prescribed smooth solution, agreement outside a region,
  and singular behavior inside it.
- Lemma 2.11, p. 17: gluing subsolutions in space, with explicit compatibility
  conditions; it is not itself a theorem for our forced classical solutions.
- Section 11.1, p. 70: “Building blocks”; the surrounding discussion constructs
  blowup solutions and glues them together.
- Section 11.3, pp. 75–77: the given velocity is made spatially constant in a
  smaller region before the blowup construction is combined with it.

Tao's published 2013 *Localisation and compactness properties of the
Navier–Stokes global regularity problem*, Theorems 5.1 and 5.4 and Corollary 5.2,
fixes the local-theory distinctions. Fefferman's Clay problem statement,
alternatives (C) and (D), supplies the established use of “breakdown.”

## Fixed choices

| Mathematical role | Wording used | Boundary or corresponding identifier |
|---|---|---|
| Combining the given solution with the localized construction | **gluing**, **local gluing**, **glued solution** | Use instead of “insertion” in exposition. `InsertionFamilyAPI` and filenames containing `Insertion` remain unchanged. The analogy with Euler concerns the operation, not an import of the Euler theorem. |
| Chosen compact forced blowup solution `(U,P,F)` | **building block**; **rescaled building block** when rescaled | Follows Euler Section 11.1. `PacketAPI` is the historical code name. |
| The prescribed `(v,π,g)` being modified | **given smooth solution** | Follows the role of `v_0` in Euler Theorem 1.5 and Section 11.3. Avoid alternating with “background” or a bare “reference” for this object. |
| The explicit divergence-free field `w_ε` | **cutoff correction** | A descriptive name defined by this article's curl formula, not a named theorem borrowed from Euler. |
| The explicit smooth force difference `H_ε` due to that correction | **force correction** | Not a Reynolds stress. The equation is the forced Navier–Stokes equation. |
| `T_max(a,f) ≤ T` for admissible smooth data | **classical breakdown by T**, or **breakdown by T** once defined | Failure of classical continuation. This does not by itself select the particular displayed velocity norm that diverges. |
| The displayed unbounded speed of the constructed solution at its prescribed endpoint | **velocity blowup at T** or **blowup at T** with that condition explicit | Do not replace “by T” with “at T.” A force producing breakdown remains smooth; do not call it a singular force. |
| Existence on a neighborhood extending beyond T | **smooth through T** | Defined in Section 2. The code name `RegularThrough` remains unchanged. |
| Extension of an existing solution past a finite endpoint | **continuation** | “Restart at t_0” describes the intermediate initial-value problem. Fixed-force H7/H3 restart does not mean uniform H1 local existence. |
| Finite-endpoint obstruction to a smooth solution | **maximal classical lifespan** | Tao's “maximal Cauchy development” is used only for the specifically cited formulation; a chosen local horizon in code is not the maximal lifespan. |
| Regularity categories | **smooth solution**, **H1 mild solution**, **almost smooth solution**, as individually defined | Follow Tao; do not use these interchangeably. Euler's “weak solution” and “subsolution” remain confined to the Euler comparison. |
| Spatial support or fractional-norm comparison | **localization** | Distinct from gluing. The American spelling is used in prose; Tao's title retains “Localisation.” |

“Singular set” in the Euler paper is a set of spacetime points. A set of smooth
forces producing breakdown is a different object and is named accordingly.
Likewise, “admissible weak solution” has an energy meaning in Euler that is not
implied by the phrase “admissible initial data” in the present article.

## Stable implementation and checks

`paper/terminology.json` retains the reviewed prose replacement map. The reader
checker validates current terminology, references, bibliography metadata,
source locations and build logs without depending on the retired merged
manuscript. The two original article PDFs remain available for comparison;
historical TeX snapshots are outside the current publication tree.


## Zero initial velocity

“Starting from rest” has documented research usage (without “the”), for example in the
abstract of [arXiv:2306.06358](https://arxiv.org/abs/2306.06358). For explicitness and consistency this article uses
**with zero initial velocity** instead. This is only a terminology change; the
condition remains `a = 0`.
