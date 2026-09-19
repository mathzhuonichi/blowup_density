# REPORT 456 — T15 U12/U13 force Sobolev bound

## 1. Theorems, exact statements, and constant

Both units are complete on the entire interval `0 ≤ s ≤ 1`, including both endpoints. Namespace: `NSFormalization.Section3.T15`.

The explicit family is independent of placement and scale:

```lean
def packetEndpoint (f : VelocityField) (s : ℝ) (i : Fin 3) : ℝ≥0∞ :=
  eLpNorm (fun t => fourierSobolevNorm s
    (fun x => coordinateForce f i (t, x))) 1 volume

def packetComponentConst (f : VelocityField) (s : ℝ) (i : Fin 3) : ℝ :=
  (packetEndpoint f 0 i).toReal ^ (1 - s) *
    (2 * Real.pi * (packetEndpoint f 1 i).toReal) ^ s

def sobolevConst (f : VelocityField) (s : ℝ) : ℝ :=
  1 + ∑ i : Fin 3, packetComponentConst f s i

theorem sobolevConst_pos (f : VelocityField) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst f s
```

`packetEndpoint_lt_top` proves the endpoint norms finite from the raw force smoothness and compact support. Their `toReal` values therefore represent actual finite endpoint norms.

```lean
theorem forceSobolev_memLp
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      MemForceSobolevT 1 s (periodizedScaledForce f place.x₀ place.T ε)

theorem packetSobolevBound
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      forceSobolevENormT 1 s (periodizedScaledForce f place.x₀ place.T ε) ≤
        ENNReal.ofReal (sobolevConst f s *
          (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)))
```

These are the canonical `ScalingAPI` field types with the displayed constant substituted. The probe closes them by `exact` and checks reverse conformance by `exact A.forceSobolev_memLp`, `exact A.packetSobolevBound`, and `exact A.sobolevConst_pos`.

The proof uses route B. `T15.force_mem` and `T17.force_coefficient_path_real` give a continuous, compactly supported, strongly measurable real-order datum path and its honest time `MemLp`. For the estimate, `chartForce` recenters the single Euclidean copy at the chart center. This works even when `place.x₀ ≠ place.chartCenter`. T13's `ball_coord_bounds` gives `chartRadius < 1/2`; support transport gives Paper1's `SupportedInCube`. The existing packet component endpoint rates interpolate to `ε^(1/2-s)` through `periodized_scalar_L1Hs_le_endpoint_product`. The T17 translation/datum-norm bridge and finite component assembly yield the manuscript's two-term bound. No additional geometric, analytic, or packet premises are introduced.

## 2. Files

- `formalization/NSFormalization/Section3/T15/SobolevBound.lean`: 16 declarations (4 definitions, 12 theorems).
- `research/T15/probes/sobolev_bound_closes.lean`: exact field conformance and the existing explicit nonzero time/space bump packet with concrete placement, scale `ε = 1/2`, and every order in `[0,1]`.
- `research/T15/axioms_u12_u13.lean`: all 16 module declarations audited.
- `research/T15/ATTEMPTS_U12_U13.md`: both development failures with their complete exact Lean diagnostics, route comparison, and the search-only glob diagnostic.
- `research/T15/T15_SPLIT.md`: U12/U13 completion statuses.
- `logs/LESSONS.md`: one pin-specific endpoint-integrand/rewrite lesson.
- `research/T15/REPORT_456.md`: this report.

All Lean files are new; no existing module was edited. Work stayed in this worktree. No push, merge, or rebase.

## 3. Gaps and error text

No mathematical residual and no gate gap. Both endpoint cases and every fractional `s ∈ (0,1)` are proved.

Route A was not needed. The exact sufficient `ENNReal` adapter from `dotHomogeneousENorm` to the cycles-frequency vector norm is recorded in ATTEMPTS; the existing angular/cycles convention bridge is acknowledged. No claim is made that Fourier convention conversion itself is absent. No unfinished adapter, named input, or placeholder is added to Lean.

The two resolved development failures were:

- `Application type mismatch: The argument hrate1 ...` after the endpoint theorem unfolded `coordinateForce`; fixed by `change` on both endpoint integrands before rewriting.
- `error: unsolved goals` after endpoint `ofReal_toReal` rewrites also changed occurrences inside the constant; fixed by simplifying `ENNReal.toReal_ofReal` with explicit nonnegativity before real-power algebra.

Complete diagnostic text is preserved in ATTEMPTS. Final module/probe checks emit no errors or warnings.

## 4. Commands and results

Every shell sourced `. scripts/lean-env.sh`; all `lake` commands ran from `verification/` with `LEAN_NUM_THREADS=6`.

- Dependency closure: `lake build NSFormalization.Section3.T17.Sobolev NSFormalization.Section3.T15.ForceMem` — exit 0, 10017 jobs.
- Endpoint dependencies: `lake build NSFormalization.Paper1.PeriodicPacketEndpointRates NSFormalization.Paper3.PositiveFourierTime` — exit 0.
- `lake build NSFormalization.Section3.T15.SobolevBound` — exit 0, 10018 jobs; existing upstream warnings replayed, no module warnings/errors.
- `lake env lean ../formalization/NSFormalization/Section3/T15/SobolevBound.lean` — exit 0, zero output.
- `lake env lean ../research/T15/probes/sobolev_bound_closes.lean` — exit 0, zero output.
- `lake env lean ../research/T15/axioms_u12_u13.lean` — exit 0; all 16 print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — exit 0, 13 policy tests pass, 45 work items consistent; repeated after documentation edits.
- `make test` — exit 0, through job 10911/10911.
- `make test-mutations` — exit 0; infrastructure mutation suite passed. This is not a mathematical mutation test of the new inequality.
- `git diff --check` — exit 0.
- Forbidden-token/heartbeat scan of the new module and probe — no matches.

Committed on branch `erenup/456-T15-U12-U13-force-sobolev` with message `Prove T15 force Sobolev paths and packet bound on [0,1]`.
