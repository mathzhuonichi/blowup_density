# C01 specification review (lane 031)

Reviewed: `research/C01/Spec.lean` (540 lines, `BlowupDensity.C01.Draft.EnergyAbsorptionAPI`,
22 fields) and `research/C01/COMPARISON.md` (224 lines), at commit `0e16ace`.
Read-only review; nothing in the lane was changed except this file.

## Verdict: **ACCEPT-WITH-NOTES**

The contract compiles, contains no `sorry`, no `axiom` and no placeholder `Prop`
field, and `make check` passes. Every sign, factor and threshold I re-derived
matches the manuscript: the energy identity, the enstrophy identity, the `ν/4`
absorption threshold with its Young half, eq:RH1's `Cν^{-1}‖f‖₂²`, eq:RL2 and
the three-term assembly. All four constants are structure fields, so they are
quantified outside `ν`, the datum and the solution, as
`STATEMENTS.md:483-484` requires; I found no field whose quantifier order lets a
constant be chosen after the solution. Citations spot-checked against the paper,
`Data.lean`, `GradientL6.lean`, `ScalarEnergy.lean`, `LpSmoothField.lean`,
`OrdinaryViscousStability.lean`, `CompactEnergy.lean` and `PacketEnergy.lean`
all resolve, and the three `rfl` bridges the file claims are genuinely `rfl`
(reproduced independently, below).

Two findings (1 and 2) are substantive: two of the 22 fields —
`trilinearHolder` and `trilinearAbsorbed` — are as stated neither derivable from
the registered clause the docstring names, nor combinable with the rest of the
contract. They are currently documentary. The remaining findings are cosmetic.
None of this makes any field false or vacuously satisfiable, which is why this
is not a REJECT.

---

## Findings

### 1. MEDIUM — `trilinearHolder`, `trilinearAbsorbed`: hypothesis class does not match the registered clause they are claimed to follow from

`trilinearAbsorbed`'s docstring says it is "obtained from the first by the
registered `gradientL6.gradientLSix` ... and not an independent assumption".
But both trilinear fields are stated as

```lean
∀ z : SpatialField, MemHInfty z → …
```

while the registered clause carried in the `gradientL6` field is

```lean
gradientLSix : ∀ v : SpatialField, SmoothSquareIntegrableJets v → …
```

(`verification/Contracts/V1/GradientL6.lean:138-141`). `MemHInfty` is the
*datum* form; `SmoothSquareIntegrableJets` is the *jet* form. The registered
contract's own module docstring warns about exactly this:
"A consumer that holds `MemHInfty v` therefore still needs unit L2 to reach
`gradientLSix`" (`GradientL6.lean:41-42`), and the datum ⟹ jet direction is
recorded **open** at `BoundedRepresentative.lean:71-74`.

The spec does take that obligation on — but only for velocity slices, in
`velocityJets` (`∀ ν a f T w t ∈ Ico 0 T, MemHInfty (slice w.velocity t) ∧
SmoothSquareIntegrableJets (slice w.velocity t)`). The two trilinear fields are
stated over **all** `H^∞` fields, so discharging them needs D01 unit L2 at full
generality, which `velocityJets` does not give and which
`COMPARISON.md` unit U6 ("depends on U1") does not cover either — U1 is stated
as the velocity-slice instance.

Consequence: as written, `trilinearAbsorbed` silently smuggles in an
unregistered general-purpose bridge that the file's own "no independent
assumption" claim denies.

**Fix.** Change the hypothesis of `trilinearHolder` and `trilinearAbsorbed` to
`SmoothSquareIntegrableJets z` (or to `MemHInfty z ∧ SmoothSquareIntegrableJets z`
if the `H^∞` side is also wanted). This costs consumers nothing — `velocityJets`
already hands them both forms for the only fields they apply it to — and it makes
the derivation close using only the registered clause. Alternatively, add an
explicit general bridge field `∀ z, MemHInfty z → SmoothSquareIntegrableJets z`
and say in the docstring that it is D01 unit L2 at full generality.

### 2. MEDIUM — no `ℝ≥0∞ ↔ ℝ` bridge for `‖Δz‖₂²`, so the trilinear fields cannot be combined with the enstrophy fields

The contract deliberately splits its quantities: differentiated ones are real
Bochner integrals (`l2Sq`, `gradientSq`, `laplacianSq`, `pairing`,
`advectionWork`), compared-only ones stay `ℝ≥0∞` (`criticalL3`, `sobolevENorm`,
the registered `eLpNorm`s). That is the right design, and the one crossing the
file *does* bridge — `sobolevENorm 2 z ^ 2 ≤ ENNReal.ofReal (CH2 * (l2Sq z +
laplacianSq z))` in `sobolevTwoFourier` — is exactly the paper's
`04-whole-space.tex:123` inequality and is `.toReal`-free. Good.

But there is a second crossing, and it is unbridged. `trilinearHolder` and
`trilinearAbsorbed` bound

```lean
ENNReal.ofReal |advectionWork z| ≤ … * eLpNorm (laplacian z) 2 volume ^ (2 : ℝ)
```

whereas `enstrophyIdentity`, `enstrophyDifferentialBound` and
`enstrophyIntegralBound` all speak of `laplacianSq z : ℝ`. Nothing in the
structure asserts

```lean
eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z)
```

so a holder of `EnergyAbsorptionAPI` cannot feed `trilinearAbsorbed` into the
absorption step; it must reprove the conversion. Since
`enstrophyDifferentialBound` already states the absorbed conclusion outright, the
two trilinear fields are consumed by nothing — inside the contract or downstream
(`STATEMENTS.md:494-497`, `:604-606` ask C01 only for eq:RL2, eq:RH1 and the
assembly). They currently document the derivation rather than participate in it.

**Fix.** Add one bridge field, in the style of `sobolevTwoFourier`:

```lean
laplacianSqENorm : ∀ z : SpatialField, SmoothSquareIntegrableJets z →
  eLpNorm (laplacian z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z)
```

(and, if `trilinearHolder` is to stay usable, the analogue for
`eLpNorm (gradientTensor z) 6 volume`, though the `L⁶` factor is only ever an
intermediate). Do **not** fix this by moving `criticalL3` or the `L⁶` norm to
`ℝ` — the `ℝ≥0∞` hypothesis side is what makes `‖u(t)‖₃ = ⊤` fail safe, and that
is correct as it stands.

### 3. LOW — `forceTimeRegularity`: two redundant conjuncts, and a docstring that overclaims

The field concludes

```lean
(∀ t ≥ 0, MemLp (slice f t) 2 volume) ∧
  ContinuousOn (fun s => l2Norm (slice f s)) (Ici 0) ∧
  ∀ t ≥ 0, IntervalIntegrable (fun s => l2Norm (slice f s)) volume 0 t ∧
           IntervalIntegrable (fun s => l2Sq (slice f s)) volume 0 t
```

The third conjunct follows from the second: a function continuous on `Ici 0` is
continuous on each compact `[0,t]`, hence interval integrable there, and so is
its square. Harmless, but it makes the field look like it carries more than it
does.

Separately, the docstring says this is "the clause `04-whole-space.tex:171`
invokes ... its `L^1_tL^2_x` and `L^2_tL^2_x` norms are finite". The paper's
sentence is about *global* finiteness on `(0,∞)`; the field states only local
interval integrability. Local is all the assembly at a finite `S` needs, so the
statement is right and the prose is what overclaims. Either weaken the prose or
add the two `(0,∞)` finiteness conjuncts that `MemForceR` (`Data.lean:549-551`)
actually supplies.

### 4. LOW — citation slips

* Module docstring, "Bridge 1" paragraph of the header: cites
  `verification/Contracts/V1/BoundedRepresentative.lean:82-88` for the record
  that datum ⟹ jet is open. That record is at `:71-74`; `:82-88` is the
  unrelated `jetSobolevENorm` conventions bullet. The `velocityJets` field
  docstring cites `:71-74` correctly, so only the header is wrong.
  (`COMPARISON.md:26` also cites `:71-74`, correctly.)
* `enstrophyIdentity` docstring cites `04-whole-space.tex:107` for "testing
  against `−Δu`". The prose is at `:106`; `:107` is the opening of the display.
* `COMPARISON.md:69` cites `CompactEnergy.energy_hasDerivAt` at `:300`; `:300`
  is the start of its docstring, the theorem is at `:302`.
* `COMPARISON.md` §2(a) says all eight in-tree whole-space forced-energy
  theorems "carr[y] `HasCompactSupport (fun x => u (t,x))`". Four of them do
  literally (`CompactEnergy.energy_balance:206`, `energy_rate_le:257`,
  `PacketEnergy.pde_energy_inequality:39`, `energy_balance_viscosity:57`); the
  other four carry the equivalent two-hypothesis form `IsCompact K` plus
  `∀ t ∈ Icc a b, tsupport (fun x => u (t,x)) ⊆ K`
  (`CompactEnergy.energy_hasDerivAt:303-304`, `hasDerivAt_energy_balance:325-328`,
  `PacketEnergy.packet_energy:145,149`, `packet_dissipation:235,239`). The
  conclusion — none is reusable for a non-compactly-supported `H^∞` velocity —
  is unaffected and correct.

### 5. INFORMATIONAL — deliberate strengthenings and redundancies, all checked and all sound

Recording these so a later reader does not mistake them for defects:

* `enstrophyIntegralBound` demands the absorption hypothesis only on
  `Ico 0 t` but concludes at `t`. That is a *stronger* statement than the paper's
  (weaker hypothesis), and it is provable, because `gradientSq (slice u ·)` is
  continuous at `t < T` by `velocity_smooth`. Intentional and fine.
* `h2TimeIntegralZeroDatum` does not carry `(fun _ => 0) ∈ initialClassR`, so it
  is not literally an instance of `h2TimeIntegral`; supplying that membership is
  trivial and the field is otherwise exactly the `a = 0` specialization with the
  *same* `Cassembly` (`l2Norm 0 = 0`, `gradientSq (fun _ => 0) = 0`). Matches
  `STATEMENTS.md:604-605` verbatim, and `fun _ => 0` is the same spelling
  `Data.breakdownSetRZero` (`Data.lean`) uses.
* A large `C₁` weakens both `trilinearAbsorbed` (conclusion) and the four
  clauses that use `C₁‖u‖₃ ≤ ν/4` as a hypothesis, so nothing pins `C₁` from
  above. This is **not** a defect: R43/R44 pick their universal `c` *after* `C₁`
  (`04-whole-space.tex:112` "Decrease `c` so that `C₁y ≤ ν/4`"), and
  `c ≤ 1/(4 C₁ C_{A05})` stays `ν`-free. The constant chain flows in the correct
  direction.
* Taken one at a time, `energyIdentity` and `enstrophyIdentity` would be
  satisfiable on a junk path (all Bochner integrals `0` by non-integrability,
  `HasDerivAt (const 0) 0 t`). They are not, because `velocityJets` and
  `forceTimeRegularity` sit in the same structure and force integrability of
  every integrand that appears. The file says this; I confirmed there is no
  integrand left uncovered (`advectionWork` needs `(u·∇)u ∈ L²`, which follows
  from `u ∈ L^∞`, `∇u ∈ L²` on the jet class).
* `sobolevENorm` is an infimum over order-`s` data, so `sobolevTwoFourier` and
  the assembly are marginally weaker than the paper's `H²` inequality if datum
  uniqueness fails. That is a D01 design point inherited uniformly, and A04 will
  consume `eq:criterion` in the same norm, so the two sides match.
* `research/**/*.lean` is not compiled by CI: `experiments/build_changed_lean.py`
  only maps `verification/`, `formalization/` and `vendor/NavierStokesAndEuler/`
  paths to lake targets. `research/C01/Spec.lean` therefore typechecks only
  locally. Pre-existing project pattern (A02, A05 drafts are in the same
  position), not a C01 defect.

---

## Statement fidelity, field by field

Re-derived from `navierStokesResidual ν u p = ∂_t u + (u·∇)u − νΔu + ∇p = f`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:57-62`).

| field | paper | verdict |
|---|---|---|
| `gradientL6` | `appendix-b:32`, `04:110-112` | registered `GradientL6API` carried whole, not restated; inhabited by `verification/Bindings/GradientL6.lean:42`. Same device as `research/A02/Spec.lean:336` (`uniqueness : UniquenessAPI`) — citation verified. OK |
| `C₁`,`CRH1`,`CH2`,`Cassembly` + positivity | `:110`,`:115`,`:123`,`:127-130` | all structure fields ⇒ `ν`-free and datum-free. OK |
| `velocityJets` | `02-prelim:29-30` | OK; the open D01 unit L2 direction, correctly owned and flagged |
| `forceTimeRegularity` | `02-prelim:17-19`, `04:171` | OK; see finding 3 |
| `energyIdentity` | `:117` | `(‖u‖₂²)' = −2ν‖∇u‖₂² + 2⟨u,f⟩`. Testing `∂_tu+(u·∇)u = νΔu−∇p+f` against `u`: `½(‖u‖₂²)' = −ν‖∇u‖₂² + ⟨f,u⟩`. **Sign and factor correct.** `gradientSq` is the Frobenius tensor norm, which is the right pairing for `⟨Δu,u⟩ = −‖∇u‖₂²` |
| `energyDifferentialBound` | `:117-121` | `E' + 2ν‖∇u‖₂² ≤ 2‖f‖₂‖u‖₂`. Correct Cauchy–Schwarz form, and it is literally the `hineq : E' t ≤ 2*b t*Real.sqrt (E t)` shape that `ScalarEnergy.lean:30` consumes after dropping dissipation. The `∀ E', HasDerivAt … E' t →` form is equivalent to the `deriv` form by uniqueness and is non-vacuous because `energyIdentity` supplies differentiability |
| `l2Bound` (eq:RL2) | `:118-121` | `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀^t‖f‖₂`, no smallness. OK |
| `trilinearHolder` | `:107-109` | `\|⟨(u·∇)u,Δu⟩\| ≤ ‖u‖₃‖∇u‖₆‖Δu‖₂`, exponents `1/3+1/6+1/2`. Statement correct; see findings 1 and 2 |
| `trilinearAbsorbed` | `:109-112` | `≤ C₁‖u‖₃‖Δu‖₂²`. Read through `‖u‖₃` rather than the paper's `y`; that is exactly what `STATEMENTS.md:496` and `:604` book, and it is what lets one clause serve R43 (`‖u‖₃ ≤ Cy`) and R44 (`‖u‖₃ ≤ CY ≤ Cθν`). `C₁ = gradientL6.Csix` does work. See findings 1 and 2 |
| `enstrophyIdentity` | `:106-107` | `(‖∇u‖₂²)' = 2⟨(u·∇)u,Δu⟩ − 2ν‖Δu‖₂² − 2⟨f,Δu⟩`. Testing against `−Δu`: `½(‖∇u‖₂²)' = ⟨(u·∇)u,Δu⟩ − ν‖Δu‖₂² − ⟨f,Δu⟩`. **Signs and factors correct**, including `pairing (slice f t) (laplacian …)` for `⟨f,Δu⟩` |
| `enstrophyDifferentialBound` (eq:RH1) | `:113-116` | `E' + ν‖Δu‖₂² ≤ Cν^{-1}‖f‖₂²` under `C₁‖u‖₃ ≤ ν/4`. **Threshold checked arithmetically:** `(‖∇u‖₂²)' + 2ν‖Δu‖₂² = 2⟨(u·∇)u,Δu⟩ − 2⟨f,Δu⟩ ≤ 2(ν/4)‖Δu‖₂² + 2[(ν/4)‖Δu‖₂² + ν^{-1}‖f‖₂²]`, giving eq:RH1 with `CRH1 = 2`. So `ν/4` is the paper's own threshold, **neither stronger nor weaker** — it is `ν/2` split between absorption and the Young step, exactly as `:112` and the docstring say. `ENNReal` hypothesis makes `‖u(t)‖₃ = ⊤` fail safe (`ofReal C₁ * ⊤ = ⊤ > ofReal (ν/4)` since `C₁ > 0`) |
| `enstrophyIntegralBound` | `:116` | `‖∇u(t)‖₂² + ν∫₀^t‖Δu‖₂² ≤ ‖∇a‖₂² + Cν^{-1}∫₀^t‖f‖₂²`, plus the interval-integrability conjunct that keeps the left integral off Mathlib's junk `0`. `gradientSq a` is right because `w.initial` gives `slice w.velocity 0 = a` (checked). OK |
| `sobolevTwoFourier` | `:122-124` | `‖z‖²_{H²} ≤ C(‖z‖₂² + ‖Δz‖₂²)`. In D01's angular convention `‖z‖²_{H²} = ‖z‖₂² + 2‖∇z‖₂² + ‖Δz‖₂²` and `2‖∇z‖₂² ≤ ‖z‖₂² + ‖Δz‖₂²`, so `CH2 = 2`. Correct, and it is the file's single `ℝ≥0∞ ↔ ℝ` bridge, `.toReal`-free |
| `h2TimeIntegral` | `:125-131`, `STATEMENTS.md:494-497` | `∫₀^S‖u‖²_{H²} ≤ CSK(S)² + Cν^{-1}‖∇a‖₂² + Cν^{-2}∫₀^S‖f‖₂²`. Re-derived: `∫₀^S‖u‖₂² ≤ S K(S)²` (K nondecreasing) and `∫₀^S‖Δu‖₂² ≤ ν^{-1}‖∇a‖₂² + Cν^{-2}∫₀^S‖f‖₂²` from the previous field. **All three ν-powers correct.** One `Cassembly` for all three summands, as the manuscript writes one `C`. `S ≤ T` is "within or at the maximal lifespan"; `∫⁻ … Ioo 0 S` needs no integrability side condition and `≤ ENNReal.ofReal _` is the `< ∞` of `:130` |
| `h2TimeIntegralZeroDatum` | `STATEMENTS.md:604-606` | the `a = 0` shape R44 consumes, same `Cassembly`; matches "`K(S) = ∫₀^S‖f‖₂` and `‖∇a‖₂ = 0`" exactly. See finding 5 |

**Scope.** eq:Rcritical1 (`:97-99`, `½(y²)'+(ν−C₀y)z² ≤ by`, constants `c`, `C₀`)
and eq:Rcritical2 (`:161-164`, `(Y²)'+νZ² ≤ C₂νY²+C₃ν^{-1}B²`) are asserted
nowhere in the file — correct, `STATEMENTS.md:449-455` and `:576-582` book them
inside R43's and R44's own proofs. `c` and `C₀` do not appear as fields, only
`C₁` does. The unprojected-equation choice is sound: `⟨∇p,u⟩ = 0` and
`⟨∇p,Δu⟩ = 0` both follow from `ClassicalSolutionR.divergence` and
`.pressure_gradient` (`Data.lean:637-641,646-648`), so no unregistered
`⟪D01:Leray⟫` is needed.

**Coverage of the consumers.** `STATEMENTS.md:494-497` asks C01 for exactly three
things and `:604-605` for the same three with `a = 0`. All six are present. No
field is missing for R43 or R44.

## `rfl` bridges — reproduced independently

Written to `verification/C01Rfl_scratch.lean`, typechecked with
`lake env lean`, exit 0, then deleted. All of the following are `rfl`:

* `gradientTensor (slice u t) x = spatialGradient u t x`
* `laplacian (slice u t) x = spatialLaplacian u t x`
* `spatialDerivative (lift (slice u t)) 0 x = spatialDerivative u t x`
* `advection (lift (slice u t)) 0 x = advection u t x`
* `gradientTensor v x = spatialGradient (lift v) 0 x`
* `(fun x => gradientTensor (slice u t) x) = (fun x => spatialGradient u t x)`

and `slice w.velocity 0 x = a x` is `w.initial x`. So `gradientSq` really is the
integrand of `Data.energyGradient` (`Data.lean:459-461`), `advectionWork` really
is `⟨(u·∇)u(t), Δu(t)⟩` of the spacetime solution, and the registered A05 objects
apply to velocity slices with no conversion, as the file claims.

## Duplication check

No duplication of `research/A02/Spec.lean` or `research/A05/Spec.lean`.

* C01 uses the **registered** `Contracts.V1.{lift, gradientTensor, laplacian,
  SmoothSquareIntegrableJets}`, not A05's private copies of the same names
  (`research/A05/Spec.lean:90,102,109,95`). Correct choice.
* C01 restates none of `CriticalEmbeddingAPI`. Its `criticalL3 z = eLpNorm z 3
  volume` is a *name* for the left-hand side of A05's `velocityCriticalL3`
  (`A05/Spec.lean:366-368`), not a second copy of the inequality, so the two
  compose directly at the consumer.
* C01 names no A02 object (`IsMaximalSolution`, `maximalLifespanR`,
  `UniquenessAPI`, `restart`); every clause is about a fixed-horizon
  `ClassicalSolutionR`. `COMPARISON.md:193-200` records this and is right.
* `slice` is new. It is definitionally the inline `fun x => z (t, x)` that
  `Data.lean` uses throughout (`:174`, `:444`, `:645`) — confirmed by the `rfl`
  checks above. If C01 is promoted to a registered contract, `slice` is the one
  definition that should move into `Contracts/V1/Data.lean` rather than live in
  the consumer.

## COMPARISON.md spot checks — all confirmed

| claim | checked | result |
|---|---|---|
| `Paper1/ScalarEnergy.lean:22` `sqrt_energy_le_primitive`, the `(y²+ζ²)^{1/2}`/`ζ↓0` device, but assumes `E 0 = 0` and `N 0 = 0` | yes | exact: `:25` `(hE0 : E 0 = 0) (hN0 : N 0 = 0)`, `:35` `Real.sqrt (E x + δ^2)`. The stated gap for eq:RL2 (which starts at `‖a‖₂`) is real |
| `vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31` `SmoothL2Field` is field-for-field `SmoothSquareIntegrableJets` | yes | exact: `:32-34` `field`, `smooth : ContDiff ℝ ∞ field`, `integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume`, vs `GradientL6.lean:107`. Identical |
| `Source/OrdinaryViscousStability.lean:32` `laplacian_pairing`, `⟨W,ΔW⟩ = −∑ᵢ‖∂ᵢW‖₂²`, support-free | yes | exact at `:32-34` |
| all eight in-tree whole-space forced-energy theorems assume compact support | yes | `CompactEnergy.lean:202`(hyp `:206`), `:253`(`:257`), `energy_hasDerivAt` at `:302`(`:303-304`), `:323`(`:325-328`); `PacketEnergy.lean:35`(`:39`), `:53`(`:57`), `:143`(`:145,149`), `:233`(`:235,239`). Confirmed — with the form caveat in finding 4. `PacketEnergy.lean:17` `work_le` (`:18`) likewise |
| `Bindings/GradientL6.lean:42` discharges `GradientL6API` | yes | exact; so the `gradientL6` field is known inhabited |
| `SmoothSobolevL6.lean:72` support-free `H¹→L⁶`, `:133` `smooth_memLp_six` | yes | exact, both support-free |
| `AngularGradientIdentity.lean:81,92` require `HasCompactSupport` | yes | exact (`:82`, `:93`) — the U10 obstacle is real |
| `Data.lean:189,453,459,487-491,495,544,624,643` | yes | all exact |
| `ScalarEnergy.lean:68,76,156,197` | yes | all exact; `critical_energy_absorption:69` really is threshold `ν/2` for eq:Rcritical1, so the "wrong estimate and wrong threshold" note is right |

## Commands and results

```
$ cd /data_8T/ping/blowup_density/.claude/worktrees/031-C01-spec
$ LEAN_NUM_THREADS=6 bash scripts/lean-install.sh
… ℹ [9406/9406] Replayed Tests.Scaling
info: Tests/Scaling.lean:18:0: Contract BlowupDensity.Tests.checkedScaling: checked; standard logical axioms only
== OK
(all five registered contract tests report "standard logical axioms only")

$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 \
    lake env lean ../research/C01/Spec.lean
EXIT=0          (no output, no warnings; 3.0 s wall)

$ grep -nE "sorry|axiom|admit|native_decide|: Prop" research/C01/Spec.lean
13:assumes nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
(the sole hit is the module docstring)

$ cd verification && lake env lean C01Rfl_scratch.lean     # 7 `example … := rfl`
EXIT=0          (scratch file then deleted; verification/ has no stray .lean)

$ make check
python3 experiments/check_formalization_plan.py --check
python3 experiments/check_contracts.py
python3 experiments/test_contract_policy.py    → Ran 13 tests … OK
python3 experiments/check_work_queue.py        → 30 work items: ownership,
                                                 contract registration and task
                                                 cards consistent.
MAKE_EXIT=0

$ git diff --name-status <merge-base>..HEAD
M  collaboration/TASKS.md          (C01 → in-progress / erenup)
M  collaboration/tasks/C01.md      (same)
M  collaboration/work_items.json   (same)
A  research/C01/COMPARISON.md
A  research/C01/Spec.lean
```

No registered contract, binding or acceptance test was touched, so `make test`
and `make test-mutations` are unaffected by this lane; `lake test` was run anyway
as part of `lean-install.sh` and passed.
