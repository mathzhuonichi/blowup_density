# Lane 223-R43-endpoint — R43 rows S4/S5/S6: from the zero-datum critical bootstrap to `T_max(0, f) = ∞` (the `a = 0` clause of Proposition 4.3 that R41 consumes)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/223-R43-endpoint` (git branch `erenup/223-R43-endpoint`, based on lane 221's branch `erenup/221-R43-force-path` = `origin/erenup/integration`
+ lane 219's `Section4/R43/CriticalMomentum.lean` (merged, #223) + lane 221's `Section4/R43/ForcePath.lean` (25 declarations: `criticalForcePrimitive`, G2/G3 exact,
`critical_bootstrap_zero_datum : … 0 ≤ S < T → 0 ≤ c < 1/(2·trilinearConst) → criticalForcePrimitive f S ≤ c·ν → ∀ t ∈ Icc 0 S, criticalNormAt w.velocity t ≤ c·ν`, the two S6 zero-field
reductions)). Read those modules and `research/R43/REPORT_221.md`, `research/R43/REPORT_219.md`, then `research/R43/R43_SPLIT.md:158-246` (S3 — gate discharge `criticalL3_gate_enorm`
**closed**; S4 — `∫₀ˢ ‖u‖²_{H²} < ∞` for every finite `S`, via C01 V4 `verification/Contracts/V4/EnergyAbsorption.lean` (eq:RH1 + the Fourier inequality + zero-datum `H²` assembly; read the
registered fields and `Bindings/EnergyAbsorptionV4.lean`, `research/C01/COMPARISON.md`) with G5 (endpoint `S = T_max` gluing / monotone convergence) and G6 (closed); S5 — A04's
`lifespanInfiniteOfLocallyFinite`, now unconditional for `MemForceR` forces as `A04.lifespanInfiniteOfLocallyFinite_of_memForceR'` (`Section4/A04/ShiftedExtension.lean`, lane 217; read its
exact hypotheses — the `squaredHTwoIntegral`/`SolvesBelow` shape — and `Section4/A04/RestartFixedForce.lean` `higherOrderBound_of_gronwall`); S6 — the exact target field
`inhomogeneousAtZero` in `research/R43/Spec.lean` (grep it; copy its statement token for token)), `research/R43/Pieces.lean`'s `criticalNormBound_radius` and the `a = 0` API pieces,
`Section4/A02/SolutionClass.lean` (`maximalLifespanR`, `exists_maximal'` from lane 213 `A02/MaximalWiring.lean`: a maximal classical solution exists for every qualified datum/force),
the paper `04-whole-space.tex:86-132` (Prop. 4.3 and its proof: "with `a = 0` and `‖f‖_{L¹H^{1/2}} < cν`, the critical norm stays `≤ cν`, the `L³` gate holds, eq:RH1 gives
`∫₀ˢ ‖u‖²_{H²} < ∞` for every finite `S`, hence by the continuation criterion `T_max = ∞`"), `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P5, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`f = 0`).
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero forces; consumers copy your binders.
- **Statement fidelity:** the endpoint theorem must be `inhomogeneousAtZero`'s statement (or a strictly stronger one) — no re-cut of the smallness condition beyond replacing the paper's
  `L¹_t H^{1/2}` norm by the registered `Data` force norm the spec uses; say which norm and cite the spec line.

## Goal
`theorem inhomogeneousAtZero_of_memForceR : ∀ f, MemForceR f → forceHomogeneousENorm 1 (1/2) f < ENNReal.ofReal (c₀ · ν) → maximalLifespanR ν (fun _ => 0) f = ⊤` (with the spec's exact
binders/constant — `c₀` explicit in terms of `trilinearConst`, C01's `C₁`, and the embedding constant; positive). Route, all pieces named above:
1. Take the maximal solution `w` with `T = (maximalLifespanR ν 0 f).toReal` (or work with `SolvesBelow`/the family A04's criterion consumes — match 217's shape) — `exists_maximal'`.
2. For every `S < T`: `critical_bootstrap_zero_datum` ⇒ `y ≤ c·ν` on `[0,S]` ⇒ `criticalL3_gate_enorm` (S3) ⇒ C01 V4's absorbed eq:RH1 ⇒ `∫₀ˢ ‖u‖²_{H²} ≤ K(S)` with the zero-datum
   constant (S4, G6) — bound uniform in `S < T` if `T < ∞` (G5: monotone convergence / the bound depends on `S` only through `S ≤ T` — check the C01 V4 constant's `S`-dependence).
3. If `T < ∞`: `squaredHTwoIntegral T u < ∞` (G5 gluing) ⇒ `lifespanInfiniteOfLocallyFinite_of_memForceR'` ⇒ contradiction (or directly `T = ⊤`). Conclude `maximalLifespanR = ⊤`.
4. Also export the general-`a` form if it falls out (`sqrt_energy_le_primitive'` route) — optional, say so.
If a piece (likely G5 or the C01 V4 constant's shape) resists, ship the rest and isolate it as ONE named hypothesis with the exact statement.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/Endpoint.lean` (namespace `NSFormalization.Section4.R43`).
2. Records `research/R43/ATTEMPTS_ENDPOINT.md`, update `R43_SPLIT.md` rows S4/S5/S6/G5, `research/R43/COMPARISON.md` (what of `RCritical1API` is now proved), conformance
   `research/R43/axioms_endpoint.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Endpoint` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_223.md`.

## Clarification (statement)
The spec field is (`research/R43/Spec.lean:243-247`, token for token):
`inhomogeneousAtZero : ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f → forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (c * ν) → maximalLifespanR ν (fun _ => 0) f = ⊤`
— the smallness is in the **inhomogeneous** `forceSobolevENormL1 (1/2)`. Prove exactly this shape (with your explicit `c`); the homogeneous-smallness version is a strictly stronger
intermediate (`forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f` is lane 221's G2), so prove the homogeneous one first and derive the spec's. Name the final theorem
`inhomogeneousAtZero_of_memForceR` and state `c` (`criticalConst`) as a `def` with a positivity lemma.
