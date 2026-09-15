# D01 draft A — review (lane 002)

**VERDICT: REJECT** — one blocker (issue 1). The Lean is clean and the
transcription is unusually careful: every paper citation and every
`COMPARISON_A.md` `file:line` I opened matched. But `MemForceR` omits the
manuscript's `C^∞` clause, and that one omission makes `thm:Rmain` (ii) **false**
as formalized and (i) trivially true. One-field fix; re-review should be fast.

## Ranked issues
### 1. BLOCKER — `MemForceR` (`DraftA.lean:157`) drops `f ∈ C^∞`, so `B^R` leaks
Paper `02-preliminaries.tex:18` (`eq:Rclasses`): `F_R = {f ∈ C^∞([0,∞);H^∞) : …}`.
`MemDatumR` correctly carries `smooth : ContDiff ℝ ∞ a` (`:125`); `MemForceR` has
no analogue. Every clause of `MemForceR` reaches `f` only through the Lebesgue
integral inside `IsAngularDatum`, so it cannot see a null-set change of the
physical field. Machine-checked (`/tmp/d01rev/Probe.lean`, exit 0):
* `memForceR_congr` : `(∀ t, f(t,·) =ᵐ[volume] g(t,·)) → MemForceR f → MemForceR g`
* `diff_isAngularPath_zero` : same hypothesis gives `IsAngularPath s (f-g) 0`,
  hence `forceBochnerNorm q s 0 = 0 < r` for every `q, s, r > 0`.

Consequence. Take any globally regular `g ∈ F_R` and let `f = g` except
`f(t,x₀) = g(t,x₀) + e₁` at one point `x₀`, every `t`. Then `MemForceR f`, and
`f` sits at distance `0` from `g` in every `L^q_tH^s_x`. But
`ClassicalSolutionR.equation` (`:359`) is pointwise `∀ x`, while the residual of a
velocity that is `ContDiffOn ℝ ∞ · (Ico 0 T ×ˢ univ)` is continuous in `x` at
interior times, and cannot equal an `f(t,·)` discontinuous at `x₀`. So no
`ClassicalSolutionR ν T a f` exists at any horizon,
`maximalLifespanR ν a f = 0 ≤ ENNReal.ofReal T`, and `f ∈ breakdownSetR ν a T`.
Hence `RelativelyDenseInForceR q s (breakdownSetR ν a T)` is provable for **every**
real `s` and every `q`: 4.1(i) is vacuous and the "only if" of 4.1(ii) is false.
(First two steps mechanized; the residual-continuity step is standard, not.)
*Fix*: add `smooth : ContDiff ℝ ∞ f` (or `ContDiffOn ℝ ∞ f (Ici 0 ×ˢ univ)`) to
`MemForceR`, mirroring `MemDatumR.smooth`.

### 2. MAJOR — implementation unit L4 (`COMPARISON_A.md:100`) is false as stated
L4 claims `IsAngularPath s f G → forceBochnerNorm (ofReal q) s G =
forcePhysicalTimeNorm q s f` for `1 ≤ q < ∞`. `angularFourier`
(`Source/FourierConvention.lean:23`) is `frequencyUnit^(-3/2) • 𝓕 f (…)`, and
Mathlib's `𝓕` is the literal Bochner integral, totalizing to `0` off `L¹`.
`H^∞ ⊄ L¹` on `R³` (e.g. smooth `~(1+|x|)^{-2}`), so for `f(t,·) = φ(t)·z` with
`z ∈ H^∞ \ L¹`, `φ ∈ C_c^∞((0,∞))`, the Bochner side is `‖φ‖_q‖z‖_{H^s} > 0` while
`forcePhysicalTimeNorm q s f = 0`. The junk-value caveats at `COMPARISON_A.md:31`
and `:32` therefore mis-scope the risk: the failure condition is `z ∉ L¹`, not
`z ∉ H^s`, and it *does* bite inside `F_R`. (Risk note 6, `:77-82`, is separately
correct — it concerns `∫ ψ·z`, where Schwartz × `L²` really is `L¹`.)
Not a blocker: `RelativelyDenseInForceR` measures with `forceBochnerNorm` (junk-
free), and `eq:RpositiveScale`/`eq:RnegativeScale` are applied only to compactly
supported, hence `L¹`, profiles. *Fix*: add an `L¹`-slice hypothesis to L4 and
soften the `forcePhysicalTimeNorm` docstring (`DraftA.lean:192-198`).

### 3-8. MINOR

* **`\dot H^{-1}` scalar-only** (`:255`). The transcription of
  `02-preliminaries.tex:58-69` is faithful, temperedness estimate included, and
  the pairing direction (`Û = |ξ|G`, i.e. `G = |ξ|^{-1}Û`) is right. But
  `prop:Renergy` (`04-whole-space.tex:43-54`) needs the *vector*,
  *time-integrated* `‖g_ε−g‖_{L^2_t\dot H^{-1}_x}`, unwritable with what is here.
  Arguably outside D01's goal (`collaboration/tasks/D01.md:7`).
* **Exponent type mismatch.** `criticalOrder : ℝ → ℝ` (`:228`) vs
  `forceBochnerNorm (q : ℝ≥0∞)` (`:212`) vs `forcePhysicalTimeNorm (q : ℝ)`
  (`:199`); `BreakdownDenseR` takes `ℝ≥0∞`, so `s < s_q` needs an
  `ENNReal.ofReal` round-trip at every use site.
* **`equation` on `Ioo 0 T`, not `Ico 0 T`** (`:359`). `eq:NS` holds on `[0,T)`,
  but interior times are the *safe* choice: `navierStokesResidual`
  (`R3/ProblemStatement.lean:57`) takes `temporalDerivative` as an unrestricted
  two-sided `fderiv`, which need not exist at `t=0` for a field smooth only on
  `Ico 0 T ×ˢ univ`. Matches `SmoothLifespan.Flow.equation:31`; faithful up to
  continuity. A decision to ratify, not a defect.
* **Dead declaration** `forceTimeDomain` (`:72`); `Ici 0` is inlined at `:160`.
* **Three `COMPARISON_A.md` labels overstate reuse.** Rows `:24`, `:29`, `:33`
  (`IsRealFrequencyDatum`, `MemForceCompactR`, `forceBochnerNorm`) say
  `reused-exact`, but each names a *new* definition wrapping a reused
  predicate/norm. No line number was wrong in any row I opened.
* **D01 acceptance not fully met.** `collaboration/tasks/D01.md:27` asks for "a
  concrete versioned Lean contract"; draft A sketches one at
  `COMPARISON_A.md:108-115` but adds no `verification/Contracts/V1/*`.

## Verified as faithful (no action)

`X_R` vs `eq:Rinitial`: `H^∞` as an order-`m` datum for every `m`, `L²` as `m=0`,
divergence identical to `Paper1/PeriodicInitialData.lean:24`; `ContDiff` is a
redundancy that usefully pins the representative. `s_q = 2/q − 3/2` matches
`thm:Rmain` (`1 ↦ 1/2`, `2 ↦ −1/2`, per the intro table). `E_T` matches
`eq:Enorm`: `essSup` over `Ioo 0 T` (no endpoint at `T`), and `spatialGradient`
in `WithLp 2` is the Frobenius `(∑_{i,j}|∂_i z_j|²)^{1/2}` demanded by "sum the
squared component norms", not an operator norm. `ClassicalSolutionR`: one-sided
`[0,T)` smoothness; `C([0,S];H^m)` as `ContinuousOn G (Ico 0 T)`, equivalent to
the paper's compact-interval form; `MemLp 2` on `pressureGradient` with **no**
scalar `p ∈ L²` — exactly `02-preliminaries.tex:101-102`. Omitting `eq:Rpressure`
is correct: for a smooth solenoidal solution, `∇p ∈ L²` plus the momentum
equation determines `∇p` (a harmonic `L²` gradient vanishes), so `(I−P)` is
derivable, not definitional. `PressureGaugeEquiv` and `radialPressurePotential`
transcribe `02-preliminaries.tex:97` verbatim. `maximalLifespanR` reproduces
`SmoothLifespan.lifespan:41` (`ℝ≥0∞`, empty sup `0`, `horizon_pos` excluding
`T ≤ 0`); `breakdownSetR` is literally `eq:Rsingularforces`.
`RelativelyDenseInForceR` is the ε-form the paper's proof opens with
(`04-whole-space.tex:177`), and its `∃ D` is faithful because
`angularRealization_injective` (`AngularFourierDilation.lean:203`) makes `D`
unique. The normalization is the manuscript's `(2π)^{-3/2}∫e^{-ix·ξ}`, discharged
by `angularFourier_eq_integral` rather than assumed; vector data use `PiLp 2`
(`FiniteHilbertBochner.lean:11`), correctly *not* the sup-norm `ForceDatum` of
`AdmissibleForce.lean:16`; force norms use `volume.restrict (Ioi 0)` and velocity
norms `(0,T)`.

## Draft's own open questions

1. **Sup vs Euclidean** — Euclidean is right (`01-introduction.tex:103`); cost is
   re-proving L2/L3, not a fidelity risk.
2. **`\dot H^{-1}` pairing form** — matches `eq:homogeneous-realization`; blocks
   only `prop:Renergy` — see the minor bullet on it.
3. **`Ioo` vs `Ico`** — see the minor bullet. Consistent; blocks nothing.
4. **Junk literal norms** — real, worse than documented (issue 2), but the
   theorem-facing norm is `forceBochnerNorm`, so 4.1–4.7 are unaffected.
5. **Lifespan vacuity** — correct: `maximalLifespanR = 0` without local existence,
   so 4.1(i) is provable-but-vacuous and 4.1(ii) unprovable until `prop:local`
   lands. Same symptom as issue 1, different cause; fixing issue 1 does not
   remove it, and it is A01's job, not D01's.
6. **`F_rd` / `S_σ` / Leray** — the first two block `cor:Rclasses` only and are
   outside D01's goal; omitting Leray is right (see above).
7. **ε-form vs closure-form** — ε-form is correct for `thm:Rmain`, which
   topologizes `F_R` by a *relative norm*. Closure-form is `prop:Renergy`, a
   different statement, correctly excluded.

## Check log
```
$ cd WT/verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 \
    lake env lean ../research/D01/DraftA.lean
(no output)                                                        EXIT = 0
$ grep -nE "sorry|axiom|admit|native_decide|unsafe" research/D01/DraftA.lean
7:content, no `sorry`, no `axiom`, and no placeholder `Prop` fields.
403:positive radius admit a member `f` of `B` whose difference from `g` has
   -> both inside doc comments ("admit" matches the English word). Clean.
$ grep -nE "^\s*(theorem|lemma|example|instance)\b" research/D01/DraftA.lean
(no matches)   -> 5 abbrev, 2 structure, 31 def; no proof obligations.
$ lake env lean /tmp/d01rev/Probe.lean                             EXIT = 0
   isAngularDatum_congr, memForceR_congr, diff_isAngularPath_zero (issue 1).
```

`COMPARISON_A.md` spot-checks — 22 declarations opened, all correct, none wrong:
`ProblemStatement.lean` 30/35/36/39/59, `R3/ProblemStatement.lean` 57/66,
`PositiveTemporalDensity.lean` 11, `FourierConvention.lean` 23/27/44/47,
`AngularFourierDilation.lean` 172/176, `SobolevHilbertModel.lean` 21,
`AngularSobolevClass.lean` 22/91, `RealSobolev.lean` 118/121,
`RealVectorPositiveDensity.lean` 15, `AdmissibleForce.lean` 16,
`AngularRealVectorBochner.lean` 54/64/120, `PeriodicInitialData.lean` 21,
`RealAdmissibleForce.lean` 15, `SmoothLifespan.lean` 23/41,
`TimeNormScaling.lean` 68, `HomogeneousRealization.lean` 17, `Thresholds.lean` 12.

Not verified: that `angularRealization` realizes the manuscript weights (taken on
`weightedAngularFourier_realization`); that `ContDiffOn ℝ ∞ G (Ici 0)` is the right
one-sided notion into `RealVectorSobolev` (Mathlib convention, accepted).
