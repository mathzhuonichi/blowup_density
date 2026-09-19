# T17 U9 — attempts log (`Section3/T17/Energy.lean`)

Unit U9 = `correction_slice_memLp`, `correction_gradient_memLp`, `energyConst`,
`energyConst_nonneg`, `correction_energy_bound`.  All five closed; this file
records what was tried, what the brief got wrong, and what to reuse next.

## What worked (first shot, no dead ends on the main line)

1. **The slice identity is `rfl`.** `(correctionData …).correction ε` is
   `latticeLift (physicalCorrection …)` (`Transport.correctionData_correction`,
   `rfl`), and

   ```
   (fun y : Space => latticeLift W (t, y)) = T13.periodize (fun y => W (t, y))
   ```

   holds by `rfl`: `T16.latticeVector k = WithLp.toLp 2 (fun i => (k i : ℝ))`
   and `T13.latticeVector n = (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => (n i : ℝ))`
   are definitionally the same term and both `tsum`s range over
   `T10.PeriodicFrequency`.  Checked with a scratch `example … := rfl` before
   anything else was written; this is the one fact the whole unit rests on.

2. **`spatialGradient` only sees the slice.**
   `I02.spatialGradient Z t x = WithLp.toLp 2 (fun i => fderiv ℝ (fun y => Z (t,y)) x (coordinateVector i))`
   by `rfl`, so the first `calc` step of
   `eLpNorm_torusLift_correction_gradient` — replacing
   `spatialGradient (latticeLift W) t` by
   `spatialGradient (fun p : SpaceTime => periodize (slice W t) p.2) t`, which
   is the exact shape T15's `eLpNorm_torusLift_spatialGradient_periodize`
   expects — is `rfl` as well.  No `funext`/`congr` gymnastics needed.

3. **Reading `energyENormT` as a pair of Euclidean quantities.** After the two
   slicewise norm identities, `energyEssSupT` and `energyGradientT` are
   *syntactically* the two quantities that `I02.energyEssSup_le` and
   `I02.energyGradient_le` bound (`show` + `rw`/`simp_rw` of the inner
   function).  The `Contracts.V1.Data.energyENorm` route was never needed:
   `Contracts/*` cannot be imported from `formalization/`, and the two I02
   lemmas are already stated in the unfolded form (the binding
   `verification/Bindings/Correction.lean:455-466` applies them the same way).

4. **The constant is the registered one.**
   `energyConst = √A + √D` with `A` from
   `Paper1.CorrectionEnergy.physicalCorrection_uniform_energy` and `D` from
   `Paper1.InsertionEnergy.correction_gradientSquare_bound`, i.e. literally
   `Bindings/Correction.lean:349`'s `energyConst := Real.sqrt Ae + Real.sqrt De`.
   Selected by `Classical.choose`, exactly as lane 385 does for
   `correctionDerivConst`.

## Failed / rejected approaches

- **`Paper1.memLp_torusLift` directly** (`Paper1/TorusCube.lean:58`) — it is
  stated only for `f : Space → ℂ`, and both U9 `MemLp` fields need
  `Space`-valued and `WithLp 2 (Fin 3 → Space)`-valued lifts.  The `ℂ` proof
  goes through `Paper1.measurable_torusLift`, which uses `Measurable.comp` and
  therefore needs `BorelSpace`/`SecondCountableTopology` on the value type.
  Fix in §1 of the module: prove the chart measurable once
  (`measurable_torusChart`) and compose with
  `Continuous.comp_aestronglyMeasurable` instead, which needs nothing of the
  value type.  `T10.memLp_torusLift_vector` exists but is `SpatialField`-only,
  so it does not cover the gradient tensor either (same observation as
  LESSONS' lane-413 line).

- **Routing the `MemLp` fields through the Haar bridge** (the brief's
  suggestion "`MemLp … follows from HaarBridge (`memLp_torusLift_*`)") — there
  is no `memLp_torusLift_*` in `Section3/T15/HaarBridge.lean`
  (`grep -n "memLp" formalization/NSFormalization/Section3/T15/HaarBridge.lean`
  returns nothing).  The bridge only gives the `eLpNorm` *equality*, which
  supplies finiteness but not a.e.-strong-measurability, so the bridge route
  would still need the measurability lemma above.  The brief's alternative
  ("or from continuity + compactness on the torus") is what was used, and it
  is strictly shorter: the lift of a continuous field is bounded, and
  `periodicTorusMeasure` is a probability measure
  (`T10.periodicTorusMeasure_isProbabilityMeasure`), so `MemLp.of_bound` closes
  it in four lines with no support hypothesis at all.

- **`x₀ = 0` for the non-vacuity witness** (lane 425's placement) — *wrong for
  U9*.  T15's Haar bridge needs `tsupport (slice) ⊆ interior fundamentalCube`
  and `T13.fundamentalCube = {x | ∀ i, 0 ≤ x i ≤ 1}`, so a ball centred at the
  origin is **not** inside the cube (half of it has negative coordinates); the
  witness had to be re-placed at the cube centre
  (`Probe.cubeCentre = WithLp.toLp 2 (fun _ => 1/2)`, radius `1/4`,
  `Probe.closure_ball_cubeCentre`).  This is not a defect of lane 425 — its
  three fields have no cube hypothesis — but every later unit that touches a
  Haar norm inherits it.

- **`exists_threshold` alone** does not give `ε₀ ≤ 1`, which the two Paper1
  `ε³` bounds need (`∀ ε ∈ Ioc 0 1`).  Its witness *is* `min 1 (…)` but the
  existential hides that, so the non-vacuity theorem takes `min 1 ε₁` and
  re-derives both clauses (`min_le_left`, `min_le_right`).  Lane 385's
  `correction_derivative_bound` already carries the same `hε₀ : ε₀ ≤ 1`
  premise, so the assembly unit will have it anyway.

- **Two elaboration slips, both fixed in the same pass** (kept here as the
  negative record):
  - `have hsupp := physicalCorrection_slice_tsupport_cube hε hθc hηc hθsupp hηsupp hρ hcube t`
    → `don't know how to synthesize implicit argument v` / `T`: in that lemma
    `v` and `T` occur only under `physicalCorrection v x₀ T θ η ε` inside the
    *conclusion*, so a bare `have` cannot infer them.  Fixed with
    `(v := v) (T := T)`.  In term position (where the expected type is known)
    the same call elaborates fine.
  - `obtain ⟨A, hA, hAb⟩ := ⟨Classical.choose …, (Classical.choose_spec …).1, …⟩`
    → `Invalid ⟨…⟩ notation: The expected type of this term could not be
    determined`.  Anonymous constructors need an expected type; replaced by
    `have hAspec := Classical.choose_spec …` + `set A := Classical.choose … with hAdef`
    + `obtain ⟨hA, hAb⟩ := hAspec`.

## Negative probes (mutation tests, deliberately not committed)

Both are in `/tmp/u9mut` and both fail as required, printing the delivered
statement in the error:

- `ε ^ ((5:ℝ)/2)` instead of `ε ^ ((3:ℝ)/2)`:
  `error: Type mismatch … has type … ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ (3 / 2))
  but is expected to have type … * ε ^ (5 / 2)`.
- `MemLp (fun x => … (t,x)) 2 volume` instead of the Haar torus-lift form:
  `error: Type mismatch … has type … MemLp (torusLift fun x => … ) 2 periodicTorusMeasure
  but is expected to have type … MemLp (fun x => …) 2 volume`.

## Brief corrections

- `Contracts/V1/Correction.lean` line numbers in the brief/SPLIT: the
  `I02.correction_energy_bound` field is at **`:493-494`**, `energyConst` at
  `:478`, `correction_slice_memLp` at `:482`, `correction_gradient_memLp` at
  `:487` (the SPLIT says `:486`, which is a doc-comment line).
- There is no `memLp_torusLift_*` in `Section3/T15/HaarBridge.lean` (see above).
- `Section3/T10/PeriodicData.lean` energy definitions are at `:328-341`
  (`energyEssSupT :328`, `energyGradientT :334`, `energyENormT :340`), not
  `:330-341`.
