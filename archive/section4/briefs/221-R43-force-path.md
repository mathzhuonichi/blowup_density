# Lane 221-R43-force-path — R43 rows G2/G3/G4 (time-path level): the homogeneous half-order force path `b(t) = ‖f(t,·)‖_{Ḣ^{1/2}}` is continuous, integrable, its primitive is C¹ with FTC derivative, and the time-integrated monotonicity S6 needs

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/221-R43-force-path` (git branch `erenup/221-R43-force-path`, based on lane 219's branch `erenup/219-R43-critical-momentum` =
`origin/erenup/integration` (which has lane 216's `Section4/R43/CriticalDatumPath.lean`: `ofSobolevVector`, `chosenHomogeneousDatum`, `criticalForceHalf`, `criticalForceHalf_isDatum`)
+ lane 219's `Section4/R43/CriticalMomentum.lean` (the Bessel-to-homogeneous map as a **continuous linear map** agreeing with 216's constructor; homogeneous datum uniqueness;
`R43.CarrierWindow`; `rcritical1_of_classical'`)). Read those two modules and `research/R43/REPORT_216.md` §3, `research/R43/REPORT_219.md`, then `research/R43/R43_SPLIT.md:130-157`
(row S2: the primitive `N t = ∫₀ᵗ b` must be continuous with FTC derivative `b(t) = ‖f(t)‖_{Ḣ^{1/2}}`, the exact shape `Paper1.critical_norm_bound`/`C01.sqrt_energy_le_primitive'`
consume — `sed -n` those suppliers: `Paper1/ScalarEnergy.lean:22,85,123`, `Section4/C01/EnergyBounds.lean:179`; and `R43.criticalNormBound_radius` in `Section4/R43/Pieces.lean`),
`R43_SPLIT.md:207-246` (S6, **G2** time-integrated monotonicity — copy its exact statement; **G3** the measurable `L¹_t Ḣ^{1/2}` datum path; **G4** time-path measurability/FTC),
C01's force regularity (`Section4/C01/` `forcePath`, `forcePath_jetLp_continuous`, `forceTimeRegularity` in `research/C01/Spec.lean:326` — continuity of the force jets in `L²` in time;
lane 215's `referenceForce_timeShift_norm_le` (`Section4/A04/RestartFixedForce.lean:21-40`) shows how the `H⁶` force path norm on `[0,S]` is handled), D01's `lowerVectorL`
(`Section4/D01/HalfOrder.lean:79-110`), lane 164's `D01/HomogeneousNorm.lean` (`dotHomogeneousENorm`, `dotHomogeneousENorm_le_of_isHomogeneousSlice`), lane 214's `criticalForceAt`
(`Section4/R43/Parseval.lean` / `CriticalPairing.lean` — the exact spelling of `b(t)` that `rcritical1_of_classical'` outputs: `criticalForceAt f t`), `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 and §2 P5, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` (`f = 0`, and a nonzero `MemForceR` force if one exists in the tree — grep
  `research/`/`Section4` for a nonzero `MemForceR` witness).
- **Satisfiability rule:** if a fact remains open, isolate it as ONE named hypothesis with the exact statement, satisfiable by nonzero forces.

## Goal
For `hf : MemForceR f` and the path `b t := criticalForceAt f t` (214's spelling; identify it with `‖criticalForceHalf f t‖` or `(dotHomogeneousENorm (1/2) (f(t,·))).toReal` — prove the
identification lemma, do not introduce a third spelling):
1. `criticalForceAt_continuousOn : ContinuousOn b (Icc 0 S)` for every `S ≥ 0` (route: the `H¹` (or `H⁶`) force datum path is continuous in time from C01's jet continuity — grep how
   215/211 get `sobolevPath (C01.forcePath …)` continuity — lower with `lowerVectorL 1 (1/2)`, push through 219's CLM, use homogeneous datum uniqueness to identify with 216's chosen
   `criticalForceHalf`, then `‖·‖` is continuous). If continuity on `[0,S]` for every `S` is what the tree gives, also state the version on `Ico 0 T`.
2. `criticalForceAt_intervalIntegrable : IntervalIntegrable b volume 0 S` and `criticalForceAt_nonneg`.
3. The primitive `N t := ∫ s in (0)..t, b s`: `continuousOn N (Icc 0 S)`, `HasDerivAt N (b t) t` on `Ioo 0 S` (FTC, `intervalIntegral.integral_hasDerivAt_right`), `N 0 = 0`, monotone —
   in exactly the shape `Paper1.critical_norm_bound`/`sqrt_energy_le_primitive'` and `R43.criticalNormBound_radius` consume (read their hypotheses and match them token for token).
4. **G2** (the split's exact statement at `R43_SPLIT.md:214-219`): time-integrated monotonicity of the force norm — prove it from 1–3 and `dotHomogeneousENorm ≤ sobolevENorm`
   (164) or whatever comparison the statement needs; if G2's statement is about the `L¹_t Ḣ^{1/2}` norm on prefixes, prove the prefix integral is monotone in the endpoint and bounded
   by the `L¹_t H^{1/2}` (inhomogeneous, `forceSobolevENormL1 (1/2) f`, finite by lane 165) norm.
5. Wiring probe: `research/R43/probes/lane221_s2_wiring.lean` showing `R43.criticalNormBound_radius` (S2) now applies to a classical solution with `a = 0` using `rcritical1_of_classical'`
   (219) and items 1–4 — i.e. the `a = 0` bootstrap `y(t) ≤ c·ν` on `[0,T]` conditional on nothing but `0 < ν`, `MemForceR f`, the smallness `∫₀ᵀ b ≤ ρ`, and `y(0) = 0`. If the probe
   closes, promote it to a theorem `critical_bootstrap_zero_datum` in the module.

## Deliverables
1. New module `formalization/NSFormalization/Section4/R43/ForcePath.lean` (namespace `NSFormalization.Section4.R43`).
2. Records `research/R43/ATTEMPTS_FORCE_PATH.md`, update `R43_SPLIT.md` rows G2/G3/G4/S2/S6, conformance `research/R43/axioms_force_path.lean`, the probe.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.ForcePath` (silent), `lake env lean` on the module (0 output), the axioms file, the probe, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/R43/REPORT_221.md`.

## Addendum — the exact G2/G3 targets (from `R43_SPLIT.md:214-232`; these are the two theorems S6 needs, state them token for token)
- **G3 (content):** `forceHomogeneousENorm 1 (1/2) f ≠ ⊤` for `MemForceR f`. The definition is an infimum over **measurable `L¹` homogeneous datum paths** (`IsHomogeneousPath` —
  grep its definition in `Contracts`/`Section4/D01`), so construct the path `t ↦ criticalForceHalf f t` (or the canonical CLM image of the lowered `H¹` path — the same element by
  uniqueness) and prove its measurability (continuity suffices), `L¹` membership on the time domain the definition uses, and the `IsHomogeneousPath` clauses.
- **G2 (monotonicity):** `∀ f, MemForceR f → forceHomogeneousENorm 1 (1/2) f ≤ forceSobolevENormL1 (1/2) f`: from any `IsSobolevPath` `G` at order `1/2` build the `IsHomogeneousPath`
  `G' := ofSobolevVector ∘ G` with `‖G' t‖ ≤ ‖G t‖` pointwise (the multiplier is bounded by `1`), then compare the infima.
- Then the S6 reduction pieces the split lists as R43-own S: `dotHomogeneousENorm (1/2) (fun _ => 0) = 0`, `(fun _ => 0) ∈ initialClassR` (grep — probably already in the tree).
