# ATTEMPTS — lane 146-C01-jet-paths (row E4a; the ∇p bridge booked as E4b)

Module delivered: `formalization/NSFormalization/Section4/C01/JetPaths.lean`
(namespace `NSFormalization.Section4.C01`).  Axiom audit:
`research/C01/axioms_jet_paths.lean` — all 18 declarations
`[propext, Classical.choice, Quot.sound]`, plus two non-vacuity examples on
`A04.zeroSol`.

## Result summary (E4a — DONE)

Over a compact subwindow `[0,S] ⊂ [0,T)` (`S < T`), indexed by `Icc (0:ℝ) S`
exactly like `Evolution.velocityField`, for `w : ClassicalSolutionR ν a f T` and
`hf : MemForceR f`:

* **Force path** `forcePath hf` with `forcePath_jetLp_continuous` — the line-by-line
  mirror of `velocityField_jetLp_continuous`, using `MemForceR`'s per-order datum
  path whose `ContDiffOn ℝ ∞ G futureTimes` (`.continuousOn`) is strictly stronger
  than the velocity's `ContinuousOn`.  (`forcePath` needs neither `w` nor `S < T`:
  the force is `H^∞` on all of `[0,∞)`.)
* **Advection path** `advectionPath w hST` with `advectionPath_jetLp_continuous` —
  jet-continuity by instantiating the vendor `EulerSmoothEulerEvolution.advection_jet_continuous`
  (`SmoothEulerEvolution.lean:29`) at the velocity path, transporting jets across the
  field equality (`advectionField_field` = `advection_field` at `A = B = u`) with
  `EulerLpSmoothCoefficientProduct.jetLp_congr`.  (`K = Icc 0 S` is a `CompactSpace`
  by `inferInstance`, which the vendor's `[CompactSpace K]` needs.)
* **Laplacian** `laplacianPath w hST` / `laplacianPath_jetLp_continuous`, and the
  `ν`-scaled `viscousPath w hST` / `viscousPath_jetLp_continuous`.  The generic
  `continuous_jetLp_sumField` (any `V`) + `laplacianField_jetLp_continuous` are
  written here because the identical `Source.PhysicalBesselSobolev` versions
  (`:83,105`) are stated for `SmoothL2Field ℂ` and cannot be instantiated at `Space`;
  the proof composes `continuous_jetLp_directionalField` (`LpSmoothFieldAlgebra.lean:147`)
  twice with `continuous_jetLp_addField` (`:128`) over `Finset.univ (Fin 3)`, and `ν•`
  is `mapField (ν • id)` + `continuous_jetLp_mapField` (`:119`).
* **Momentum residual** `residualPath w hf hST` / `residualPath_jetLp_continuous`, with
  the pointwise field identity `residualPath_field`
  `(residualPath t).field x = f(t.1,x) − advection u t.1 x + ν • spatialLaplacian u t.1 x`
  and, at interior times (`0 < t.1`),
  `temporalDerivative_eq_residual_sub_pressureGradient`:
  `∂ₜu(t.1,·) = residualPath t − ∇p(t.1,·)` (from `D01.temporalDerivative_slice_eq`,
  `Pressure.lean:196`).

No obstruction was hit for E4a; the three probe scripts that established the compact
subtype instance, the `jetLp_congr` advection transport and the `sumField` induction
all passed on the first corrected attempt and were folded into the module.

## E4b — the remaining `∇p`-jet obligation (NOT proved here; do not prove here)

Row E4 wants `hB` of `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt`
(`OrdinaryWordTime.lean:87`) at order 0: `∀ n, Continuous (fun t : Icc 0 S =>
(∂ₜu(t.1,·) packaged as SmoothL2Field).jetLp n)`.  By
`temporalDerivative_eq_residual_sub_pressureGradient` and the vendor `addField`/`mapField`
jet-continuity, that reduces to the **jet-continuity in time of `∇p(t.1,·)`**, which E4a
does **not** supply.  `∇p = (I−P) h` at the datum level (eq:Rpressure), where `h` is the
residual whose datum is pinned by `D01.pin_pressureGradient_datum` (`PressureJets.lean:112`)
to `Leray.lerayComplement m Am` with `Am` an order-`m` datum of exactly
`f(t,·) − advection u t + ν•spatialLaplacian u t` — token-for-token `residualPath_field`.

The obligation is a **two-directional bridge** between "carrier-B jets continuous in `t`"
(what E4a gives) and "order-`m` datum path continuous in `t`" (what `lerayComplement` and
`jetOfDatum` consume/produce):

* **Direction A — jets ⟹ order-`m` datum (MISSING; the whole E4b cost).**  Need
  `∀ m, Continuous (fun t : Icc 0 S => D01.smoothAngularDatum m (m:ℝ) (le_refl _) (residualPath w hf hST t))`
  into `RealVectorSobolev (m:ℝ)`, from `residualPath_jetLp_continuous`.  The **order-0**
  case exists: `A01.orderZeroDatumCLM : L2 →L[ℝ] RealVectorSobolev 0`
  (`DatumPathContinuity.lean:103`) with `continuous_orderZeroDatum` (`:127`).  The
  **order-`m`** generalisation is absent — `D01.smoothAngularDatum` (`SmoothDatum.lean:279`)
  and `D01.exists_isSobolevDatum_of_memLp_derivs` (`FiniteOrderConstructor.lean:269`) give
  the datum **pointwise** but no continuity/CLM in the field.  What closes it is a
  **jet-norm control of the finite-order datum** — `‖smoothAngularDatum m (m:ℝ) _ A‖ ≤
  C_m · ∑_{j≤m} ‖A.jetLp j‖` (the reverse of `sobolevENorm_le_norm_smoothAngularDatum`,
  `SmoothDatum.lean:349`) — exhibiting `smoothAngularDatum m (m:ℝ) _` as a bounded linear
  map of the jets, whence Direction A by the same squeeze as `continuous_jetLp_scaleField`.
  This is **lane 145's forthcoming `FiniteOrderNorm.lean`** (not present in this worktree).
* **Leray step (EXISTS as a CLM).**  `D01.Leray.lerayComplement (m:ℝ) :
  RealVectorSobolev (m:ℝ) →L[ℝ] RealVectorSobolev (m:ℝ)` (`LerayDatum.lean:255`,
  `mkContinuous 1`) preserves continuity, so `t ↦ lerayComplement m (Am t)` is continuous
  once Direction A holds; `pin_pressureGradient_datum` makes it `∇p`'s order-`m` datum.
* **Direction B — order-`m` datum ⟹ jets (EXISTS).**  `jetOfDatum_continuous`
  (`Evolution.lean:147`) ∘ that datum path, with `D01.jetOfDatum_ae` — verbatim the
  pattern `forcePath_jetLp_continuous` / `velocityField_jetLp_continuous` use, now on the
  `∇p` datum path instead of the class-given velocity/force one.

**Correction (review 146, notes N2/N3).** Lane 145 (merged as PR #147) does *not* supply
`‖smoothAngularDatum m m _ A‖ ≤ C_m·∑_{j≤m}‖A.jetLp j‖` directly: `FiniteOrderNorm.lean` gives
`‖A‖² ≤ 16^m·M` where `M` uniformly bounds the `eLpNorm²` of the *coordinate weak derivatives*
(`HasWeakDerivsL2Bound`, `FiniteOrderNorm.lean:352/413`).  Two glue pieces remain for E4b:
(a) `eLpNorm (∂^α Z.field) 2 ≤ ‖Z.jetLp |α|‖` for a `SmoothL2Field` (not in tree; ≈20 lines via
`jetLp_mapField` + `norm_derivative_jetLp`); (b) additivity of `smoothAngularDatum` along the
path — `isSobolevDatum_sub` needs `2 ≤ s` (`A03/VectorTameProduct.lean:186`), order 0 has
`orderZeroDatumCLM`, **order 1 is a hole**.  Also (N3): `wordEnergy_hasDerivWithinAt` takes paths on
a *closed* `Icc 0 T'` (`OrdinaryWordTime.lean:70-75`) while `temporalSliceField`/`pressureGradientField`
need `t ∈ Ioo 0 T`, so E4b must shift the window: `0 < c < S < T`, `T' := S − c`, derivative at true
interior points, `HasDerivWithinAt → HasDerivAt`.  Exact target statements: `REVIEW_JET_PATHS.md`
(`pressureGradientPath_jetLp_continuous` on `Icc c S`, `temporalSlicePath_jetLp_continuous`).

**Precise statement E4 then needs (after E4b):**
`∀ n, Continuous (fun t : Icc 0 S => (temporalSlice-path t).jetLp n)`, assembled as
`residualPath` jets (E4a) **minus** `∇p` jets (E4b) via `continuous_jetLp_addField` and the
negation `mapField` — since `∂ₜu = residualPath − ∇p`
(`temporalDerivative_eq_residual_sub_pressureGradient`).  Feeding this `hB` (with `hA` =
`velocityField_jetLp_continuous` and `hd` from `velocity_smooth`) into
`wordEnergy_hasDerivWithinAt` at order 0, then upgrading `HasDerivWithinAt (Icc …)` to
`HasDerivAt` at interior `t`, discharges the E4 value fact
`hd : d = 2⟪u,∂ₜu⟫` that `MomentumCarrierB.energyIdentity_classical` currently takes as a
hypothesis.

## Commands run

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.JetPaths` | exit 0, `Build completed successfully (10191 jobs)`, no line mentioning the module |
| `lake env lean ../formalization/NSFormalization/Section4/C01/JetPaths.lean` | exit 0, silent |
| `lake env lean ../research/C01/axioms_jet_paths.lean` | exit 0; 18/18 `[propext, Classical.choice, Quot.sound]`; both `A04.zeroSol` non-vacuity examples elaborate |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|^\s*axiom ' …/JetPaths.lean` | no output |
| `make check` | exit 0 (13 contract-policy tests OK; 30 work items consistent) |
