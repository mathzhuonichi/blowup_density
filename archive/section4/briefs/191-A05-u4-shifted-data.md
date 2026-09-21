# Lane 191-A05-u4-shifted-data — A05 units U4/U8 for R43: the physical `Λv` realization and the half-order derivative data (`ShiftedCriticalData` for `H^∞` fields)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/191-A05-u4-shifted-data` (git branch `erenup/191-A05-u4-shifted-data`, based on
`origin/erenup/integration`, which contains lane 182's `Section4/R43/Trilinear.lean` (the consumer: `structure ShiftedCriticalData (v : SpatialField)
(Z : RealVectorSobolev (3/2))` with fields `lambda`, `lambda_memHInfty`, `lambdaHalf_isDatum : IsHomogeneousSliceDatum (1/2) lambda Z`,
`derivativeHalf j`, `derivativeHalf_isDatum`, `derivativeHalf_symbol` (Riesz coordinate symbols); `memHInfty_dirDeriv` already there),
lane 165's `Section4/A05/CriticalL3.lean` (U6/U7 closed; `dotHomogeneousENorm`, `velocityCriticalL3`), `Section4/D01/{HalfOrder,HomogeneousNorm,
HomogeneousWitness,LeraySymbol,OrderZeroSymbol}.lean`, `Source/BesselFractionalData.lean:45` (`Λ^a` on data), `Source/FractionalRealization.lean`,
`Source/FractionalRepresentative.lean`, `Paper3/SobolevDirectionalDerivative.lean:54,67,120` (U8 pieces), `Paper3/SobolevOrderLowering.lean`).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P5/P6, `research/A05/COMPARISON.md:200-235` (units U1–U9, esp. **U4** and **U8**, with their
tree pointers) and `:270-310` (`IsRieszPower` design), `research/A05/Spec.lean:160-175` (`IsRieszPower`), `research/R43/REVIEW_182-R43-s1b-trilinear.md`
(what the bridge needs), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to
  existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A05,D01,B02,R43}`, `Source/`, `Paper1/`, `Paper3/`. Before citing a
  paper line, `sed -n` it (`02-preliminaries.tex:45-60` for `Λ = (−Δ)^{1/2}`, `04-whole-space.tex:95-110`). Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example` (`v := 0`, `Z := 0`) **and** state for a nonzero Schwartz `v` why the
  hypotheses are satisfiable (satisfiability rule: named inputs must be restrictions of standard properties).

## Goal
`theorem shiftedCriticalData_of_memHInfty (v : SpatialField) (hv : MemHInfty v) (Z : RealVectorSobolev (3/2))
  (hZ : IsHomogeneousSliceDatum (3/2) v Z) : ShiftedCriticalData v Z` — i.e. for an `H^∞` field with an order-`3/2` homogeneous datum `Z`:
1. **U4 (`Λv`):** a physical field `lambda` with `MemHInfty lambda` whose order-`1/2` homogeneous datum is `Z` (Fourier: `|ξ|^{1/2}·(|ξ|^{1/2} \hat v)`
   pairing — `Λv` has `Ḣ^{1/2}` datum equal to the `Ḣ^{3/2}` datum of `v`). Realize `lambda` as the `L²` field whose Fourier transform is `|ξ| \hat v`
   (`Source/BesselFractionalData.lean` / `FractionalRealization.lean` give the realization for `0 < a < 3/2`; `H^∞` gives `|ξ|\hat v ∈ L²` at every order,
   hence `MemHInfty lambda` via the tree's datum-to-jets machinery, `D01/DatumToJets.lean`). If the `a = 3/2` endpoint of U1/U3 is needed for uniqueness
   of `Z`, use the tree's endpoint results (`COMPARISON.md` U1) and say where.
2. **U8 (`∂_j v`):** `derivativeHalf j : RealVectorSobolev (1/2)` with `IsHomogeneousSliceDatum (1/2) (dirDeriv j v) (derivativeHalf j)` and the symbol
   identity `\widehat{derivativeHalf j}_i = rieszCoordinateSymbol j ξ · (Z i) ξ` a.e. (`Paper3/SobolevDirectionalDerivative.lean` for
   `\widehat{∂_j v} = i ξ_j \hat v`, then divide by `|ξ|` against `Z`'s `|ξ|^{3/2}` weight — check the tree's exact `rieszCoordinateSymbol` definition in
   `Trilinear.lean`/`D01/LeraySymbol.lean` and match it token-for-token).
3. Package for R43: `theorem criticalAdvectionLpBridge_shifted (hcrit : CriticalDatumPath w hf) : ∀ t ∈ Ioo 0 T, ShiftedCriticalData (fun x => w.velocity (t,x)) (hcrit.velocityThreeHalf t)`
   — the velocity slices of a `ClassicalSolutionR` are `MemHInfty` (grep `A02`/`D01` for the slice `MemHInfty` lemma used by lane 165/175;
   `Section4/A01/SliceWiring.lean`, `A02/SolutionClass.lean` `sobolev` field + `D01.exists_smoothL2Field_of_memHInfty`'s converse). The remaining
   field `pairing_identity` (fractional Parseval) is **not** this lane — leave it; a `CriticalAdvectionLpBridge` is then one Parseval lemma away.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A05/RieszShift.lean` (namespace `NSFormalization.Section4.A05`): the `Λ` realization
   (`rieszLambda`, `rieszLambda_memHInfty`, `rieszLambda_halfDatum`), the derivative data (`derivativeHalfDatum`, its datum and symbol lemmas),
   `shiftedCriticalData_of_memHInfty`, and `criticalAdvectionLpBridge_shifted` (this last one may live in a small `Section4/R43/ShiftedData.lean`
   if it needs `R43` imports; say which).
2. Records `research/A05/ATTEMPTS_U4_U8.md`; update `research/A05/COMPARISON.md` U4/U8 rows and `research/R43/R43_SPLIT.md` row S1b (bridge status);
   conformance `research/A05/axioms_u4_u8.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A05.RieszShift` (and the R43 module if added; silent), `lake env lean` on
each module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands). Also write it to
`research/A05/REPORT_191.md`.
