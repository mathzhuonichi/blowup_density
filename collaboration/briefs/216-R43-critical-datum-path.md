# Lane 216-R43-critical-datum-path — construct `CriticalDatumPath` for a classical solution (R43 rows G3/G4: the half-order carrier), peeling the momentum identity if needed

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/216-R43-critical-datum-path` (git branch `erenup/216-R43-critical-datum-path`, based on `origin/erenup/integration`,
which contains lane 175's `Section4/R43/CriticalPairing.lean` (`structure CriticalDatumPath` at `:161-201` — the consumer shape; **read it field by field**), lane 214's
`Section4/R43/Parseval.lean` (`rcritical1_of_hcrit'`: eq:Rcritical1 now conditional **only** on `hcrit : CriticalDatumPath w hf`), lane 182's `R43/Trilinear.lean`, lane 191's
`R43/ShiftedData.lean`, lane 164's `Section4/D01/HomogeneousNorm.lean` (`dotHomogeneousENorm`, `IsHomogeneousSliceDatum` — `grep -rn` them), lane 165's `A05/CriticalL3.lean`,
D01's `DatumToJets.lean`/`LerayDatum.lean`/`OrderZeroCurl.lean`, and the A01 datum-path lanes that did the **inhomogeneous** analogue of this construction: 161
`A01/DatumPathContinuous.lean` (continuous datum paths at every order), 169 `A01/DatumPathDeriv.lean` (time-differentiable datum paths with the projected residual as derivative),
211 `A01/LocalTheoryBundle.lean` (`LocalCarrier`, per-slice all-order data), 180/189 (`ConstructorAssembly`, `PressureRegularity`: pressure gradient as a datum, Helmholtz).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P5, `research/R43/R43_SPLIT.md` (rows G3, G4, S6 and the table at `:225-260`), `research/R43/REPORT_214.md`,
`research/R43/REVIEW_175-R43-s1-pairing.md`, `research/A01/REPORT_169.md` (how the momentum identity was transported to datum level), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`A04.zeroSol` with `f = 0`).
- **Satisfiability rule:** any named input you leave open must be a restriction of a standard property that a nonzero classical solution satisfies, stated exactly, ONE structure
  (`CriticalDatumInputs`) bundling them; consumers copy your binder shapes. Do not invent a weaker variant of `CriticalDatumPath` — 214's `rcritical1_of_hcrit'` is the consumer.

## Goal
`theorem exists_criticalDatumPath (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) : Nonempty (CriticalDatumPath w hf)` for `0 < ν`, `0 < T`, **unconditionally if the tree
allows**, else conditional on `CriticalDatumInputs`. Mathematics (paper `04-whole-space.tex:90-110`, `appendix-a-local-theory.tex`): every slice of a classical solution is `H^∞`,
so its homogeneous order-`1/2` and `3/2` data exist (`|ξ|^{1/2} û ∈ L²` from `û ∈ L²` and `|ξ| û ∈ L²`; check `HomogeneousNorm.lean` for the comparison `dotHomogeneousENorm s ≤
sobolevENorm s` or the datum-from-inhomogeneous lemma; if absent, prove it); the Laplacian/advection/pressure-gradient/force slices are smooth `L²` fields with data likewise
(`hf : MemForceR f` gives the force's order-`6` path; for order `1/2` use `forceSobolevENormL1`'s finiteness at order `≤ 6` — row G3 asks exactly for `∀ t, IsHomogeneousSliceDatum (1/2)
(f(t,·)) (forceHalf t)` — say whether G3 needs an extra integrability input); `order_shift`/`laplacian_symbol` are the Fourier symbol identities (grep 191's `criticalAdvectionLpBridge_shifted`
and D01's symbol lemmas); `velocity_transverse` is divergence-freeness at datum level (`OrderZeroCurl`/`LerayDatum`: `lerayComplement s v = 0 ↔` solenoidal — check the order-`1/2` version
exists or transport it from order `0`); `pressure_longitudinal` is "the pressure gradient is a gradient" (`LerayDatum`/lane 189's Helmholtz converse); `velocityHalf_smooth` and
`momentum` are the time-regularity of the half-order datum path — the exact analogue of lane 169's `exists_differentiable_datumPath` at homogeneous order `1/2` (transport 169's argument
through the norm comparison, or derive from 169's inhomogeneous order-`1` path by the same `H^{1/2} ⊂ Ḣ^{1/2}`-type map, if that map is a bounded linear map on data in the tree).

Deliver in order; commit after each closes: (1) the six datum paths with all `_isDatum` fields; (2) `order_shift`, `laplacian_symbol`, `velocity_transverse`, `pressure_longitudinal`;
(3) `velocityHalf_smooth` + `momentum`; (4) the assembly `exists_criticalDatumPath` and the corollary `rcritical1_of_classical : … → (eq:Rcritical1 statement of 214)` with **no `hcrit`
binder**. If (3) does not close, ship (1)(2)(4) conditional on ONE named `CriticalDatumInputs` containing exactly the missing (3)-facts with their statements.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean` (namespace `NSFormalization.Section4.R43`).
2. Records `research/R43/ATTEMPTS_CRITICAL_DATUM.md`, update `R43_SPLIT.md` rows G3/G4 (and S6 status), conformance `research/R43/axioms_critical_datum.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.CriticalDatumPath` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_216.md`.
