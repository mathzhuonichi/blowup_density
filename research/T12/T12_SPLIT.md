# T12 — proof-lane split, remaining three fields of `MeanZeroSobolevCalculusAPI`

Lead-facing, 2026-09-18. Targets = the three still-open clauses of the reconciled API on
`research/T12/probes/api_on_canonical.lean`: `velocityCriticalL3` (`:148-151`),
`gradientLambdaCriticalL3` (`:170-175`), `gradientLSix` (`:184-187`). The other six clauses are
proved: `boundedRepresentative`/`hTwo_le_laplacian`/`lambda_exists` (lane 341,
`Section3/T12/FourierEmbeddings.lean`), `tameProduct` (lane 342, `TameProduct.lean`),
`spectralGap`/`homogeneous_le_sobolev` (`SpectralGap.lean`). Vocabulary =
`Section3/T12/MeanZeroCalculus.lean` (`periodicLpENorm:71`, `gradientTensor:84`, `laplacian:89`,
`IsPeriodicLambda:96`, `MemPeriodicHomogeneous:60`, `SmoothPeriodicT:66`). Design =
`research/T12/{RECONCILIATION,COMPARISON}.md`. House style = `research/T11/T11_SPLIT.md`,
`research/T15/T15_SPLIT.md`. Size: **S** ≤ ~100 lines; **M** one self-contained lemma; **L** a
multi-file campaign. Model: `codex-sol` = reuse/measure-theory bookkeeping, `Opus` = analytic core.

## 0. Ground rules

**Peeling rule** (from T11/T15). Every unit ends in a `theorem` that **is** an API field verbatim (or
a lemma directly consumed by one). A unit that cannot close from the tree names **exactly one**
`def … : Prop` input in `Section3/T12/`, non-tautological, satisfiable at a nonzero field, discharged
by a named later unit. **No named input for the hard analytic unit** (U3). The paper cites Taylor for
the torus critical embeddings (`appendix-b-embeddings.tex`, `lem:critical-embeddings`); there is no
Mathlib torus HLS, so the Lean proof is built here from the registered whole-space embedding.

**Route decision (evaluated per field).**

- **(a) reverse localization** — cutoff `χ` (=1 on `fundamentalCube Q`, supported in a slightly larger
  cube `Q'`), transfer a torus `L^p` norm to a whole-space `L^p` norm of `χv`, apply the **registered
  whole-space embedding**, then pull the whole-space homogeneous norm of `χv` back to the torus
  homogeneous norm of `v` through the **two proved T13 Gagliardo identities** and absorb the low-order
  remainder by `spectralGap`. **Chosen for `velocityCriticalL3`.** T13's `wholeSpace_identity`
  (`WholeSpaceIdentity.lean:509`) and `torus_identity` (`TorusIdentity.lean:1174`) are both proved but
  **only for `0 < s < 1`**, so route (a) is admissible exactly at the half-order `a = 1/2` and nowhere
  else — which fixes the routes for the other two fields.
- **(b) direct Fourier ℤ³ (periodic Riesz/HLS)** — **rejected for all three.** Mathlib has no
  Hardy–Littlewood–Sobolev, no discrete Riesz-potential `ℓ^{p'}→ℓ^p` bound, and no periodic
  fractional-integration `L^p` theory; this route rebuilds HLS from scratch (an `L+` campaign) to
  reprove what A05 already registered on ℝ³. Recorded as the fallback if (a)/(c) stall.
- **(c) integer-order derivative route (Leibniz + `hTwo_le_laplacian`)** — **chosen for `gradientLSix`**
  (`a = 1`, whole exponent `6`). Reverse-localize the **registered integer-order** whole-space
  `A05.gradient_l6` (`‖∇w‖₆ ≤ Csix‖Δw‖₂`), expanding `∇(χv)`, `Δ(χv)` by Leibniz; the cutoff
  commutators live on `Q'∖Q` and are absorbed with `hTwo_le_laplacian`. This stays at integer order,
  so it never touches the fractional `0<s<1` Gagliardo identities (which exclude `a=1` anyway).

`gradientLambdaCriticalL3` (order `3/2`) uses **neither Gagliardo at `3/2`** (out of range) nor a new
embedding: it reduces by Fourier **order-shift** to `velocityCriticalL3` at `a = 1/2` applied to each
`∂_j v` and to the `Λ`-representative `Lv`.

## 1. Units

- **U1 — Haar↔cube `L^p` transfer.** New `Section3/T12/HaarCube.lean`. For a unit-periodic `v` and any
  `p`, `eLpNorm (torusLift v) p periodicTorusMeasure = eLpNorm v p (volume.restrict fundamentalCube)`;
  and for `w` supported in `interior fundamentalCube`, `eLpNorm w p (volume.restrict fundamentalCube) =
  eLpNorm w p volume`. Route: `T13/TorusIdentity.lean:419 lintegral_fundamentalCube_ofReal`,
  `:402 fundamentalCube_ae_eq_halfOpenCube`, `:459 torusLift_torusPoint`, `:456 torusPoint_sub`
  (Haar-on-torus = Lebesgue-on-cube), generalized from `p=2` to `eLpNorm … p`. Vector version for
  `gradientTensor v : Space → WithLp 2 (Fin 3 → Space)`. **M, codex-sol.** Deps: —.

- **U2 — the cutoff `χ`.** New `Section3/T12/Cutoff.lean`. `def cutoff : SpatialField`, smooth,
  `cutoff = 1` on `fundamentalCube`, `tsupport cutoff ⊆ interior (largerCube)`, with `‖∇χ‖_∞`,
  `‖∇²χ‖_∞` finite and `∇χ`, `Δχ` supported in `Q'∖Q`. Route: a `ContDiffBump`/product of 1-D smooth
  step functions; `χ·v` is then `ContDiff ℝ ∞` with `HasCompactSupport`, hence `MemHInfty (χ·v)`.
  **M, codex-sol.** Deps: —.

  **Status (lane 365, 2026-09-18): complete.** `Cutoff.lean` uses a fixed
  `ContDiffBump` with plateau radius `5/2` and support radius 3; the documented
  `largerCube` is the open radius-4 Euclidean ball. It proves the smoothness,
  range, support, compact-support product, `MemHInfty` product, derivative
  bounds, and first/second derivative vanishing clauses. The direct closure
  probe is `research/T12/probes/cutoff_closes.lean`.

- **U3 — cutoff–Gagliardo comparison at `a = 1/2` (analytic core, no named input).** New
  `Section3/T12/CutoffGagliardo.lean`. For smooth mean-zero periodic `v` and `χ` of U2:
  `dotHomogeneousENorm (1/2) (χ·v) ≤ ENNReal.ofReal C · (eLpNorm v 2 (volume.restrict fundamentalCube)
  + periodicHomogeneousENorm (1/2) v)`. Route: `wholeSpace_identity` (`:509`) gives `IReal (1/2) (χv) =
  cFrac (1/2)·dotHomogeneousENorm (1/2)(χv)²`; `torus_identity` (`:1174`) gives `ITorus (1/2) v =
  cFrac (1/2)·periodicHomogeneousENorm (1/2)(meanZeroPartT v)²` with `meanZeroPartT v = v` (mean-zero);
  bound `IReal (1/2)(χv) ≤ C(ITorus (1/2) v + ‖v‖²_{L²(Q)})` by splitting the double difference
  `χ(x)v(x)−χ(y)v(y) = χ(x)(v(x)−v(y)) + (χ(x)−χ(y))v(y)`, a Lipschitz bound on `χ`, and a kernel
  comparison `periodicKernel` vs `fractionalRadialKernel` on the support gap; divide by `cFrac (1/2) > 0`
  and take square roots. **L, Opus.** Deps: U2.

  **Status (lane 377, 2026-09-18): COMPLETE.** `Section3/T12/CutoffGagliardo.lean` proves the two Gagliardo
  identities at `s=1/2` (`ireal_cutoffMul_eq`, `itorus_meanZero_eq`),
  `meanZeroPartT v = v` for mean-zero `v`, the `ℝ≥0∞` divide-by-`cFrac` +
  square-root step (`enn_sqrt_div_bound`), the difference split
  `IReal (1/2) (χv) ≤ 2·IA v + 2·IB v` (`ireal_cutoffMul_le_split`, with `IA`,
  `IB` the two split Gagliardo integrals), and the assembly
  `dotHomogeneousENorm_cutoffMul_le` reducing the U3 target to
  `IA v ≤ Ca·ITorus (1/2) v` and `IB v ≤ Cb·‖v‖²_{L²(Q)}` with explicit
  constant `max (√(2Ca)) (√(2Cb/cFrac (1/2)))`.  All 13 declarations carry the
  standard 3 axioms; probe `research/T12/probes/cutoff_gagliardo_closes.lean`.
  The two reverse-localization bounds are proved in the same module:
  `iA_bound : IA v ≤ 343·ITorus (1/2) v` (lattice tiling of the whole-space
  `x`-integral back to `fundamentalCube`, count `7³`) and
  `iB_bound : IB v ≤ cbConst·‖v‖²_{L²(Q)}` (`cbConst = 686·Jval`, Lipschitz
  cutoff bound + finite kernel integral `Jval_lt_top`), giving the final
  theorem `cutoff_gagliardo_half`.  The probe instantiates it on a nonzero
  smooth mean-zero periodic witness — see `research/T12/ATTEMPTS_U3.md`.

- **U4 — `velocityCriticalL3`** (probe `:148-151`). New `Section3/T12/CriticalL3.lean`. Target verbatim:
  `∀ v, MemPeriodicHomogeneous (1/2) v → periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf ·
  periodicHomogeneousENorm (1/2) v`. Route: `periodicLpENorm 3 v = eLpNorm (torusLift v) 3 Haar`
  (`MeanZeroCalculus:71`) `= eLpNorm v 3 (restrict Q) = eLpNorm (χv) 3 (restrict Q) ≤ eLpNorm (χv) 3
  volume` (U1, `χ=1` on `Q`); the **registered** whole-space `A05.velocityCriticalL3`
  (`Section4/A05/CriticalL3.lean:394`, constant `criticalL3Const:302`) with the norm rewritten by
  `Bindings/GradientL6V2.lean:44 gradientL6V2_dotHomogeneousENorm_eq` gives `≤ criticalL3Const ·
  dotHomogeneousENorm (1/2)(χv)`; U3 bounds that by `C(‖v‖_{L²}+periodicHomogeneousENorm (1/2) v)`;
  `spectralGap` (`SpectralGap.lean:331`) at `s=1/2` absorbs `‖v‖_{L²} ≤ Cgap(1/2)·periodicHomogeneousENorm
  (1/2) v`. Set `CcriticalHalf`. Approximate a general `MemPeriodicHomogeneous` `v` by smooth (U3 needs
  smoothness) or restrict to the smooth core the API supplies. **M, Opus.** Deps: U1, U3.

- **U5 — `gradientLSix`** (probe `:184-187`), route (c). New `Section3/T12/GradientLSix.lean`. Target
  verbatim: `∀ v, SmoothPeriodicT v → IsMeanZeroT v → periodicLpENorm 6 (gradientTensor v) ≤
  ENNReal.ofReal Csix · periodicLpENorm 2 (laplacian v)`. Route: `periodicLpENorm 6 (gradientTensor v) =
  eLpNorm (torusLift (gradientTensor v)) 6 Haar = eLpNorm (∇v) 6 (restrict Q) = eLpNorm (∇(χv)) 6
  (restrict Q) ≤ eLpNorm (∇(χv)) 6 volume` (U1 vector, `χ=1` on `Q`, so `∇(χv)=∇v` there); registered
  whole-space `A05.gradient_l6` (`Bindings/GradientL6.lean:42`, `A05/GradientL6.lean:64
  eLpNorm_gradTensor_six_le`) gives `≤ Csix₀·eLpNorm (Δ(χv)) 2 volume`; Leibniz `Δ(χv)=χΔv+2∇χ·∇v+vΔχ`
  splits off commutators supported in `Q'∖Q`, bounded by `‖v‖_{H²(T³)}` and thence by `‖Δv‖_{L²}` via
  `hTwo_le_laplacian` (`FourierEmbeddings.lean:165`); `χΔv` on `Q` returns `‖Δv‖_{L²(T³)}` by U1. Set
  `Csix`. **L, Opus.** Deps: U1, U2.

- **U6 — `gradientLambdaCriticalL3`** (probe `:170-175`). New `Section3/T12/GradientLambdaL3.lean`.
  Target verbatim: `∀ v Lv, SmoothPeriodicT v → MemPeriodicHomogeneous (3/2) v → IsPeriodicLambda v Lv →
  periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤ ENNReal.ofReal CcriticalThreeHalves ·
  periodicHomogeneousENorm (3/2) v`. Route: apply **U4** (`velocityCriticalL3`, `a=1/2`) to each `∂_j v`
  and to `Lv` — both are mean-zero (`∂_j`, `Λ` kill the zero mode) and lie in `MemPeriodicHomogeneous
  (1/2)`; then Fourier order-shift identities `periodicHomogeneousENorm (1/2)(∂_j v) ≤
  periodicHomogeneousENorm (3/2) v` (multiplier `2πk_j`, `|2πk_j| ≤ |2πk|`) and `periodicHomogeneousENorm
  (1/2) Lv = periodicHomogeneousENorm (3/2) v` (multiplier `2π|k|`; `IsPeriodicLambda`/`lambdaField_component`
  `FourierEmbeddings.lean:289`, `lambdaCoeff:225`), reusing the `SpectralGap.lean` weight algebra
  (`periodicFrequencyWeight_rpow_le_gap_mul_homogeneous:90`, `reweightDatum:127`); combine the three
  component `L³` norms into `periodicLpENorm 3 (gradientTensor v)`. Set `CcriticalThreeHalves`.
  **L, Opus.** Deps: U4. **Named input:** none — the `Lv` witness is a field argument and its graph
  `IsPeriodicLambda v Lv` is a hypothesis, so no vacuity guard is needed.

## 2. Waves (≤ 2 concurrent per current lane cap)

| wave | units | sizes / models |
|---|---|---|
| W1 | **U1** Haar↔cube transfer · **U2** cutoff `χ` | M sol / M sol |
| W2 | **U3** cutoff–Gagliardo core · **U5** `gradientLSix` (route c, independent of U3) | L Opus / L Opus |
| W3 | **U4** `velocityCriticalL3` | M Opus |
| W4 | **U6** `gradientLambdaCriticalL3` | L Opus |

U3 is the critical path: U4 waits on it and U6 waits on U4. U5 is off the critical path (integer-order,
needs only U1/U2). Lane numbers allocated by the lead in `PLAN.md`.

## 3. Risks

1. **The kernel comparison in U3 (highest).** `IReal (1/2)(χv) ≤ C·ITorus (1/2) v + C‖v‖²_{L²}` is the
   one genuinely new torus estimate; the danger is a `χ`-support term that is not controlled by the
   torus homogeneous norm. Mitigation: keep `Q'` only slightly larger than `Q` so `∇χ` support is a thin
   shell, and bound the shell term by `‖v‖_{L²(Q)}` (absorbed later by `spectralGap`), never by a
   frequency cutoff (`SECTION3_PLAN.md` §7 forbids finite-mode constants; `COMPARISON.md` §10 records
   that `PeriodicFiniteCriticalInterface`/`PeriodicCriticalBridge`/`PeriodicCompactSobolevL6` all lose
   uniformity — do not import them).
2. **Smoothness gap in U4.** U3 needs smooth `v`; `velocityCriticalL3` quantifies over
   `MemPeriodicHomogeneous (1/2) v`. Either the API's homogeneous membership already carries a smooth
   physical representative, or add a density/approximation step; check the `MemPeriodicHomogeneous`
   definition before writing U4 and, if a smooth core is missing, that step is its own S-M sub-lane, not
   a silent weakening of the field.
3. **`dotHomogeneousENorm` spelling.** A05's theorem uses `A05.dotHomogeneousENorm`; T13's identities use
   `Contracts.V1.HomogeneousNorm.dotHomogeneousENorm`. The `rfl` bridge
   `Bindings/GradientL6V2.lean:44` closes it — use it explicitly in U4, do not assume defeq silently.

### U1 status (lane 366 r1) — COMPLETE
`Section3/T12/HaarCube.lean` proves the actual all-`p` Haar↔cube transfer
`eLpNorm_torusLift_eq_restrict` for every `p : ℝ≥0∞` (incl. `p = 0`, `p = ⊤`), via
the single measure identity `map_torusChart` + `MeasurableEmbedding.eLpNorm_map_measure`
(no exponent case split, no hypothesised lintegral). Exposed: smooth corollary,
scalar and gradient-tensor (`WithLp 2 (Fin 3 → Space)`) specializations, the
`periodicLpENorm` bridges (`periodicLpENorm_eq_eLpNorm_torusLift` rfl,
`periodicLpENorm_eq_restrict[_gradientTensor]`), and the supported-in-cube transfer
in both `Function.support` and `tsupport` spellings (scalar + gradient-tensor). All
11 public declarations audit to `[propext, Classical.choice, Quot.sound]`; module
`lake env lean` output is empty. U4/U5 can now consume `p = 3` scalar and `p = 6`
gradient-tensor transfer directly. No named input; the periodicity hypothesis is
the paper's unit-periodic interface, unused in the proof (holds for every field).
