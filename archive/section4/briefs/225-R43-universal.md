# Lane 225-R43-universal — Proposition 4.3's general-datum clause (`RCritical1API.universal`): small critical data and force ⇒ the solution stays below the critical radius and `T_max ≥ S` (whatever the spec's exact conclusion is — copy it token for token)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/225-R43-universal` (git branch `erenup/225-R43-universal`, based on lane 223's branch `erenup/223-R43-endpoint` = `origin/erenup/integration`
+ `Section4/R43/Endpoint.lean` (the zero-datum endpoint: `criticalConst`, the forcing-prefix estimate, slice bootstrap, `L³` absorption, maximal-family absorption, the explicit zero-datum
`H²` budget, A04 finiteness, `inhomogeneousAtZero_of_memForceR`)). Read that module and `research/R43/REPORT_223.md`, `research/R43/REVIEW_223-R43-endpoint.md`, then the target:
`research/R43/Spec.lean` — the field `universal` of `RCritical1API` (grep `universal`; read the whole structure `:169-247` and the docstrings; **copy the field statement token for token**,
including which norms and which conclusion: the paper's Prop. 4.3 `04-whole-space.tex:86-132` says: for `a ∈ X_R` with `‖a‖_{Ḣ^{1/2}} ≤ cν`? and `‖f‖_{L¹H^{1/2}}` small, the critical norm
stays `≤ 2cν`?/the solution is regular on `[0,S]` — `sed -n 86,132p` it and match the spec), `research/R43/R43_SPLIT.md:130-157` (S2 general-`a`: `C01.sqrt_energy_le_primitive'`
(`Section4/C01/EnergyBounds.lean:179`, the `E(0)/N(0)`-arbitrary generalization) + a re-run of `Paper1.continuous_bootstrap` (`Paper1/ScalarEnergy.lean:85`) with `ρ = y(0) + ∫b` — "not yet
wrapped; R43-own, S"), lane 221's `Section4/R43/ForcePath.lean` (`critical_bootstrap_zero_datum` — the zero-datum wrapper you generalize; `criticalForcePrimitive`), lane 219's
`rcritical1_of_classical'` (eq:Rcritical1 for arbitrary classical solutions), C01 V4 `verification/Contracts/V4/EnergyAbsorption.lean` + `Bindings/EnergyAbsorptionV4.lean` (eq:RH1 with the
gate; check whether the registered `H²` budget carries the initial `‖a‖²_{H¹}` term for general data — 223 used only the zero-datum assembly; if the general budget is not registered, look for
it in `Section4/C01/` (`grep -rn "sobolevENorm 1 a\|initial" Section4/C01`) and use the local theorem), A02 `exists_maximal'` (213), A04 `lifespanInfiniteOfLocallyFinite_of_memForceR'`
(217) / `extendsBeyond_of_memForceR'`, `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P5, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`a = 0`, `f = 0`, and the zero-datum instance recovering 223's theorem).
- **Statement fidelity:** the theorem must be the spec's `universal` field verbatim (constants explicit). If the spec's field is unsatisfiable or mis-cut as written, do NOT re-cut it: prove the
  closest faithful statement, and write the discrepancy with paper/spec line numbers in `research/R43/COMPARISON_UNIVERSAL.md` for the owner.
- **Satisfiability rule:** if one fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero data/forces.

## Goal
1. `critical_bootstrap_general`: for a classical solution `w` with `y(0) = criticalNormAt w.velocity 0` and `0 ≤ S < T`: if `y(0) + criticalForcePrimitive f S ≤ c·ν` with `c < 1/(2·trilinearConst)`
   (or the spec's exact smallness), then `criticalNormAt w.velocity t ≤ c·ν` on `[0,S]` — generalize 221's zero-datum wrapper via `sqrt_energy_le_primitive'` + `continuous_bootstrap`.
2. The general-datum `H²` budget on `(0,S)` (C01 V4 / local C01 theorem with the initial term), the A04 finiteness/continuation step, and the maximal-family assembly, exactly as 223 did for `a = 0`.
3. `universal_of_memForceR : <spec's universal statement>` and, if the spec's conclusion is a lifespan bound (`ofReal S ≤ maximalLifespanR ν a f` or `= ⊤`), the explicit constants.
4. Update the API status: which of `RCritical1API`'s fields are now proved (`inhomogeneousAtZero` by 223, `universal` here); record in `research/R43/COMPARISON.md`'s companion file.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/Universal.lean` (namespace `NSFormalization.Section4.R43`).
2. Records `research/R43/ATTEMPTS_UNIVERSAL.md`, `research/R43/COMPARISON_UNIVERSAL.md`, conformance `research/R43/axioms_universal.lean` (audit in `Contracts.V1.Data` vocabulary too, as 223 did).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Universal` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_225.md`.
