# Lane 214-R43-parseval — the fractional Parseval pairing: `pairing_identity` of `CriticalAdvectionLpBridge`, completing the R43 bridge

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/214-R43-parseval` (git branch `erenup/214-R43-parseval`, based on `origin/erenup/integration`). Read `CLAUDE.md`, `collaboration/HANDOFF.md`
§0 and §2 P5, `Section4/R43/Trilinear.lean` (lane 182: `structure CriticalAdvectionLpBridge hcrit` with fields `shifted` and **`pairing_identity : ∀ t (ht : t ∈ Ioo 0 T),
⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ = ∫ x, ⟨advection (C01.lift (w.velocity (t,·))) 0 x, (shifted t ht).lambda x⟩`**; `criticalTrilinearEstimate_of_hcrit`, `rcritical1_of_hcrit`),
`Section4/R43/ShiftedData.lean` and `Section4/A05/RieszShift.lean` (lane 191: `criticalAdvectionLpBridge_shifted`, `rieszLambda` = the physical `Λv` with `Ḣ^{1/2}` datum = the
`Ḣ^{3/2}` datum of `v`), `Section4/R43/CriticalPairing.lean` (lane 175: `CriticalDatumPath`, the half-order data `advectionHalf`, `velocityHalf`, and the real inner product `⟪·,·⟫` on
`RealVectorSobolev (1/2)`), `Section4/D01/{HalfOrder,HomogeneousNorm,HomogeneousWitness,RealPairing}.lean`, `Source/FractionalRealization.lean`, `Source/FractionalRepresentative.lean`,
`Paper3/RealPairing*`/`AngularRealVectorBochner.lean` (real pairings via Fourier), `research/R43/REVIEW_182-R43-s1b-trilinear.md`, `research/A05/REPORT_191.md`, and the top 40 lines of
`logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on the zero solution.
- **Satisfiability rule:** if one genuinely missing fact remains, isolate it as ONE named hypothesis with the exact statement.

## Mathematics
`⟪A, B⟫` on `Ḣ^{1/2}` data is `∫ |ξ| Â·B̂ dξ` (real part); with `Â = \widehat{(u·∇)u}` and `B̂ = û`, this equals `∫ Â · \widehat{Λu}` = `∫ (u·∇)u · Λu dx` by Plancherel, where
`Λu = rieszLambda` (Fourier symbol `|ξ|`). So `pairing_identity` is: half-order datum pairing = `L²` pairing of the physical advection with the physical `Λu`. Ingredients: (i) the datum
pairing unfolded to the Fourier integral (`D01/RealPairing.lean`, `HalfOrder.lean`); (ii) `\widehat{rieszLambda u} = |ξ| û` (lane 191's realization lemma); (iii) Plancherel for the real
pairing of two `L²` fields with `L²` Fourier transforms (`Source/…`, Mathlib `MeasureTheory.Integral` + `Real.fourierIntegral` isometry on `L²`: `Mathlib/Analysis/Fourier/...`
`fourierIntegral` Plancherel — find the tree's version: `Paper3/AngularRealVectorBochner.lean`, `Source/PhysicalRemoval.lean`); (iv) the advection slice `advection (C01.lift …) 0 x` is `L²`
(A04's `NonlinearDatum`) with datum `hcrit.advectionHalf t` at order `1/2` (`hcrit.advectionHalf_isDatum` on `Ioo`).

## Goal
`theorem pairing_identity_of_hcrit (hcrit) : ∀ t (ht : t ∈ Ioo 0 T), ⟪hcrit.advectionHalf t, hcrit.velocityHalf t⟫ = ∫ x, ⟨advection … 0 x, (criticalAdvectionLpBridge_shifted hcrit t ht).lambda x⟩`
(token-for-token the field, with lane 191's `shifted`), hence `def criticalAdvectionLpBridge_of_hcrit (hcrit) : CriticalAdvectionLpBridge hcrit` and the corollaries
`criticalTrilinearEstimate_of_hcrit'`, `rcritical1_of_hcrit'` conditional on `hcrit` alone.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/Parseval.lean` (namespace `NSFormalization.Section4.R43`).
2. Records `research/R43/ATTEMPTS_PARSEVAL.md`, update `research/R43/R43_SPLIT.md` (S1b: bridge closed), conformance `research/R43/axioms_parseval.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Parseval` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_214.md`.
