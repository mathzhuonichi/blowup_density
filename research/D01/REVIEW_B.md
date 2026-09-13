# REVIEW_B — lane 003, task D01 draft B

**VERDICT: ACCEPT-WITH-NOTES**

`research/D01/DraftB.lean` typechecks clean (exit 0, no diagnostics), is genuinely
definitions-only, and is faithful to the manuscript on every point I checked,
including the two conventions that are easiest to get wrong (angular Fourier
normalization and the gradient-only pressure gauge). Every one of the 30+
`file:line` reuse citations in `COMPARISON_B.md` that I opened resolved to the
named declaration — zero wrong lines, zero overclaims. One theorem-facing
definition (`CompletedDense`) is over-quantified and unusable as written; the
rest are notes.

**Specifically cleared (the two flagged risks are not present):**

* `ForceR` (`:215`) carries `smooth : ContDiffOn ℝ ∞ field futureDomain`, so
  smoothness of `f` *itself* — not merely of its Sobolev data — is a hypothesis
  of membership. Consequently `ForceR` membership is **not** stable under
  modification of `f` on a null set: a null-set edit destroys `ContDiffOn`.
  `MemForceR` (`:236`) is likewise not null-set stable: `datum`/`G` is
  `ContDiffOn ℝ ∞ _ (Ici 0)` and the realization equality is pointwise for
  every `t ≥ 0`, and since `angularRealization` is injective
  (`AngularFourierDilation.lean:203`) a one-point edit of `g` would need a
  discontinuous `G`. **No blocker for Theorem 4.1(ii).**
* Negative-time freedom in `ForceR` is harmless for `thm:Rmain`: both
  `forceRelativeDistance` (integrates over `positiveTimeMeasure`) and
  `maximalLifespanR` (via `ClassicalSolutionR`, which constrains only
  `Ico 0 T` / `Ioo 0 T`) ignore `t < 0`.

## Ranked issues

| # | Sev | Declaration | Paper loc | What differs | One-line fix |
|---|---|---|---|---|---|
| 1 | **major** | `CompletedDense` (`:386`) | `04-whole-space.tex` prop:Renergy | `b` ranges over **all** `ℝ → ForceDistribution`, not over the completion `L^q(0,∞;H^s)`. Taking `b t = δ₀` (triple) at `s = 0` gives `sobolevENorm 0 (f.toDist t − b t) = ⊤` for a.e. `t`, so the distance is `⊤` for every `f`: the predicate is **false for every `S`**, and prop:Renergy stated with it is unprovable. Fail-safe (over-strong, not unsound), but it blocks prop:Renergy as formalized. | Add `bochnerSobolevENorm q s b ≠ ⊤` (plus measurability) as a hypothesis on `b`, or quantify `b` over an `Lp` completion type. |
| 2 | minor | `energyNormET` (`:270`) | `01-introduction.tex` eq:Enorm | `.toReal` sends `⊤ ↦ 0` and the totalized `∫` sends non-integrable `↦ 0`, so eq:REclose `‖u_ε−v‖_{E_T} ≤ …` can be satisfied vacuously by a field of infinite energy. Shape, interval `Ioo 0 T`, and the Frobenius gradient (`dissipation = Σᵢ ∫‖∂ᵢu‖²`) are exact. | Carry a finite-energy side hypothesis in every `E_T` estimate, or return `ℝ≥0∞`. |
| 3 | minor | `bochnerSobolevENorm` (`:113`), `bochnerHomogeneousENorm` (`:168`) | eq:time-norms | `∫⁻` with no measurability of `t ↦ vectorSobolevENorm s (g t)`: off the measurable class this is the *lower* integral, so it can under-report the `L^q` norm. Already scoped as **U5**. | Discharge U5 (measurability) before any density theorem is stated. |
| 4 | minor | `MemHomogeneous` (`:145`), `homogeneousENorm` (`:152`) | eq:homogeneous-realization; App. B | Non-integrable integrand silently returns `0` in Mathlib. Benign: it then forces `u = 0`, which `G = 0` already realizes correctly, and the used range (`s = −1`, and `a ∈ (0,3/2)` for App. B) is integrable by Cauchy–Schwarz. `‖ξ‖^(−s)` is `Real.rpow`, junk `0` at `ξ = 0` (null set). Sign convention verified: `s = −1` gives `û = |ξ|G`, i.e. `|ξ|^{-1}û = G ∈ L²` — literally the displayed set, and `‖·‖ = ‖G‖₂` matches the stated isometry. | Add an integrability hypothesis, or state the definition through a pairing bound. |
| 5 | minor | `ForceR.field` (`:216`) | eq:Rclasses | Docstring says "(zero-extended in `t`)" but nothing enforces `field (t,·) = 0` for `t < 0`; `ForceR` is not extensional below zero. Harmless for Thm 4.1 (see above), but blocks a *separated* `MetricSpace ForceR` without quotienting by nonnegative-time equality (**U10**). | Fix the docstring, or add `∀ t < 0, field (t, ·) = 0`. |
| 6 | minor | `physicalSobolevNorm` (`:130`), `physicalBochnerENorm` (`:134`) | eq:time-norms | Built on `Source.vectorAngularSobolevNorm`, whose `angularSobolevSq` uses the pointwise Bochner `𝓕`; faithful only for slices in `L¹ ∩ L²`. The draft confines them to the insertion estimates (correct), but they are theorem-facing. | Keep a `ContDiff ∧ HasCompactSupport` hypothesis on every use. |
| 7 | minor | `bochnerSobolevENorm` (`:113`) | eq:time-norms | `q : ℝ`, literal for any `q ≠ 0`; no `q = ∞` case. Paper's force norms only use `q ∈ {1,2}`, so this is cosmetic. | None needed; note the intended range. |
| 8 | minor | `sobolevENorm` docstring (`:101`) | — | Cites `MemAngularSobolev.exists_unique_datum` for uniqueness of `{l // angularRealization s l = u}`; the lemma that actually gives it is `angularRealization_injective` (`AngularFourierDilation.lean:203`). Both exist. | Swap the citation. |

## Check log

**1. Typecheck.** `. scripts/lean-env.sh; cd verification; LEAN_NUM_THREADS=6 lake env lean ../research/D01/DraftB.lean` → **exit 0, empty output** (no errors, no warnings, no `sorry` diagnostics).

**2. Hygiene.** `grep -nE "sorry|axiom|admit|native_decide|unsafe"` → one hit, `:13`, inside the module docstring ("no `sorry`, no `axiom`"). `grep -c "^\s*(theorem|lemma)"` → **0**. Two `example`s (`:397`, `:400`), both `norm_num [criticalOrder]` arithmetic (`criticalOrder 1 = 1/2`, `criticalOrder 2 = −(1/2)`), matching the thm:Rmain thresholds. No `instance`, no attribute, no `Prop` placeholder field. 46 declarations, all `def`/`abbrev`/`structure`.

**3. Fidelity.** Verified against the cited paper locations:

* **Fourier/norms.** `angularSobolevSq s f = ∫ (1+‖ξ‖²)^s ‖angularFourier f ξ‖²` and `angularFourier f ξ = (2π)^{−3/2}·𝓕f(ξ/2π)` (`FourierConvention.lean:23,44`) — literally `01-introduction.tex`'s display. Every Sobolev quantity in the draft goes through `angularRealization`, never Mathlib's cycles `sobolevRealization`. Vector norms are `PiLp 2` (`Product ι H := PiLp 2 …`, `FiniteHilbertBochner.lean:11`), i.e. the paper's "sum the squared component norms". Time domain `positiveTimeMeasure = volume.restrict (Ioi 0)` = the paper's `(0,∞)` default for forces; velocity norms on `Ioo 0 T`.
* **`sobolevENorm` totalization.** `⨅` over `{l // angularRealization s l = u}`; empty subtype ⇒ `⊤` (correct: off `H^s`), and injectivity makes the value unique otherwise. `vectorSobolevENorm` propagates `⊤` correctly through `^2 / Σ / ^(1/2)` in `ℝ≥0∞`. Theorem-facing dependence: `forceRelativeDistance` and `RelativelyDense` do depend on it, and `⊤` is the right off-space value.
* **`ForceR`/`MemForceR` vs eq:Rclasses.** `ContDiffOn ℝ ∞ (datum m) (Ici 0)` = "smoothness into each `H^m`, with one-sided time derivatives at zero" (`Ici 0` is `UniqueDiffOn`). `MemLp _ 1` + `MemLp _ 2` over `positiveTimeMeasure` = `‖f‖_{L¹_tH^m} + ‖f‖_{L²_tH^m} < ∞` for every integer `m ≥ 0`. No compact support, no vanishing near `t = 0` — as `02-preliminaries.tex` lines 22–26 require for the whole-space class. Per-order data are automatically compatible (realization is injective).
* **`X_R`, `S_σ`, `F_c`, `F_rd`.** `MemHInfty` = `ContDiff ∞ ∧ ∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume`, field-for-field `SmoothL2Field Space` (`LpSmoothField.lean:31`); the smooth representative is the right choice for a classical solution class. `IsSolenoidal` uses `spatialDivergence` (`ProblemStatement.lean:67`, `Σᵢ ∂ᵢuᵢ`) on the time-independent lift. `MemFc` = `ContDiff ∞ ∧ CompactPositiveTimeSupport`, and `positiveTimeDomain = Ioi 0 ×ˢ univ` (`R3/ProblemStatement.lean:53`) = `R³ × (0,∞)`. `MemFrd`: `futureDomain = Ici 0 ×ˢ univ` (`ProblemStatement.lean:45`) = `R³ × [0,∞)` in the time-first convention; the joint order-`k` `iteratedFDerivWithin` norm is equivalent to `max_{|α|+j=k} |∂_x^α ∂_t^j f|` up to dimensional constants, which the per-`(N,k)` existential `C` absorbs, so `∀ N k, ∃ C` matches the paper's `∀ N, α, j` seminorm family exactly; no common numerical bound is imposed, as §4.6 requires.
* **`ClassicalSolutionR` + pressure.** `navierStokesResidual ν u p = ∂ₜu + (u·∇)u − νΔu + ∇p` (`R3/ProblemStatement.lean:57`) = eq:NS. Momentum on `Ioo 0 T` only (correct: a two-sided `∂ₜ` at `t = 0` is not determined by one-sided data); divergence and Sobolev regularity on `Ico 0 T` (one-sided at 0). `sobolev_path` + `_ae` + `_continuous` encode `u ∈ C([0,S];H^m)` for every integer `m` on each compact subinterval. Pressure enters **only** through `momentum` (its gradient); no scalar `L²` field anywhere, matching "There is no requirement that `p ∈ L²(R³)`"; `pressure_gradient_memLp` is the paper's `∇p ∈ L²` and is `PressureGaugeEquiv`-invariant. `PressureGaugeEquiv` = "determined up to a function of time". `pressurePotential z = ∫₀¹ ⟪G(t, r·x), x⟫ dr` = the paper's `p(x,t) = ∫₀¹G(rx,t)·x dr`. eq:Rpressure in `(I−P)` form is not defined; it is equivalent to `momentum` given `divergence` (apply `I−P`: `(I−P)∂ₜu = (I−P)Δu = 0` for divergence-free `u`, `(I−P)∇p = ∇p`), an unformalized obligation (U8c).
* **Lifespan / breakdown / density.** `maximalLifespanR` is the same `⨆ S, ⨆ (_ : Nonempty …), ENNReal.ofReal S` shape as `SmoothLifespan.lifespan` (`:41`), only the solution class changing. `RegularThrough` = `∃ δ>0` with a solution on `[0,T+δ)` ⊇ the paper's smooth extension to `[0,T+δ]`. `breakdownSetR : Set ForceR` = `{f ∈ F_R : T^ν_{max,R}(a,f) ≤ T}` (eq:Rsingularforces), `breakdownSetRZero` = `B^R_{ν,0,T}`. `RelativelyDense` is the ε-form, which for a pseudometric-induced topology is density (periodic analogue proved: `ManuscriptTopology.denseAt_iff_approximation:176`). `criticalOrder q = 2/q − 3/2` = `s_q`; `scalingExponent q s = 2/q − 3/2 − s` = `β(q,s)` (and matches `Contracts/V1/Thresholds.lean` `formula`).
* **Grid.** `cellAverage C z = |C|⁻¹ • ∫_C z` and `gridObservation grid z k = cellAverage (grid.cell k) z` over `k : Fin 3 → ℤ` = §4.8's `(A_hz)_C = |C|⁻¹∫_C z` with codomain `(R³)^{T_h}` and coordinatewise equality. `CartesianGrid` (`GridGeometry.lean:15`) has per-axis positive widths; `cell` (`:81`) is the half-open box, so `volume C ∈ (0,∞)`. The volume-weighted sequence norm of §4.8 is not defined (not needed by thm:Rgrid).

**4. Reuse spot-check.** Opened 36 cited `file:line` references: `FourierConvention.lean:15,23,50`; `AngularFourierDilation.lean:172,176,203,228`; `AngularSobolevClass.lean:54,68,91`; `RealSobolev.lean:118`; `RealVectorPositiveDensity.lean:15`; `PositiveTemporalDensity.lean:11`; `AdmissibleForce.lean:16`; `RealAdmissibleForce.lean:15,99`; `AngularRealVectorBochner.lean:15,47,54,64`; `AngularForceNorms.lean:16,19,88,98`; `InsertionEnergy.lean:30`; `CompactEnergy.lean:190,195`; `SmoothLifespan.lean:23,41,48,58,70,83,124`; `ManuscriptTopology.lean:44,139,150,156,161,176`; `GridGeometry.lean:15,81`; `HomogeneousRealization.lean:17`; `FractionalRealization.lean:78,96`; `TimeNormScaling.lean:68`; `ActualGridObservations.lean:22`; `RealPositiveDensity.lean:54`; `FourierPhysicalJets.lean:159,169`; `OrdinaryForcedLocal.lean:18`; `ProblemStatement.lean:30,35,36,67`; `R3/ProblemStatement.lean:57,66`; `LpSmoothField.lean:31`; `EulerProof.lean:1340,5216`; HeliCorgi `R3HelmholtzPressure.lean:228,259`, `R3SchwartzInitialData.lean:77`. **All correct** — name, kind and (where checked) type/normalization. Notably confirmed: `energyNormET` is expression-for-expression `InsertionEnergy.energyNorm`; `maximalLifespanR` is expression-for-expression `SmoothLifespan.lifespan`; `angularRealVectorSlice_pairing:54` has exactly `RepresentsSlice`'s shape; `ForceDatum` really is sup-normed `Fin 3 → SobolevHilbert` (so the switch to `PiLp 2` is a genuine fidelity fix); `HomogeneousRealization.lean` really does state "A full `L² → 𝓢'` homogeneous multiplier is intentionally not introduced here".

**5. The draft's own open questions.**

1. *sup-norm `ForceDatum` vs `PiLp 2`.* Consistent — `PiLp 2` is the paper's "sum the squared component norms"; `ForceDatum`'s `Pi` sup norm is not. Non-blocking; reusing the `RealAdmissibleForce` algebra (U4) needs a norm transport with constants `≤ √3`.
2. *`sobolevRealization` vs `angularRealization`, the `(2π)^{|s|}` factor.* Consistent — the paper *defines* `H^s(R³)` by the angular transform and the weight `(1+|ξ|²)^s`, which is what the draft uses; the cycles convention is only equivalent (`angularSobolevSq_equivalence`). Non-blocking for Thms 4.1–4.7, since the thresholds are convergence-to-zero statements; the exact `(2π)^s` homogeneous factor (U7) must be carried in prop:Renergy's `Ḣ^{-1}` estimates.
3. *No completed homogeneous multiplier.* Consistent — `MemHomogeneous`/`homogeneousENorm` are stated as a pairing predicate on `𝓢'`, exactly like eq:homogeneous-realization, so the multiplier is not needed to *state* them. It blocks the constructive half of prop:Renergy (producing elements of `Ḣ^{-1}`), not thm:Rmain.
4. *`(I−P)` form of eq:Rpressure not defined.* Consistent — the paper's own `∇p ∈ L²` is imposed instead, and the two are equivalent given `momentum` + `divergence`. Non-blocking for the definitions; needed for thm:Rinsert's "applying `I−P` recovers eq:Rpressure" (U8c).
5. *`ForceR` not extensional in negative time.* Consistent with the paper (which only defines `f` on `[0,∞)`). Non-blocking for Thms 4.1–4.7; blocks a separated metric on `ForceR` (U10). See issue 5.
6. *ε-form density vs `Dense`.* Consistent; equivalent for any pseudometric-induced topology, with the periodic equivalence already proved. Non-blocking.
7. *No Fréchet topology on `X_R`.* Consistent — thm:Rmain fixes `a ∈ X_R` and never topologizes it. Non-blocking.
8. *`F_rd` translation.* Consistent; the joint order-`k` derivative bound is equivalent to the mixed `∂_x^α∂_t^j` family with the same quantifier structure. Non-blocking.
9. *Totalized integrals.* Consistent in intent but they hide obligations rather than errors — see issues 2, 3, 4. The sharpest is `energyNormET`'s `.toReal`, because eq:REclose is a *bound*.
