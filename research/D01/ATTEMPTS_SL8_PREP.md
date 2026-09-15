# ATTEMPTS — D01 · P2 · SL8 preparation (lane 111)

Deliverables: `Section4/D01/OrderZeroAlgebra.lean` (Group 1, order-0 datum algebra),
`Section4/D01/MomentumSlice.lean` (Group 2, slice regularity), `SL8_SPLIT.md` (Group 3, table).
Everything compiled; axioms exactly `[propext, Classical.choice, Quot.sound]`
(`axioms_sl8_prep.lean`).

## Group 1 — order-0 datum algebra (route chosen)

- **Additivity/subtractivity via uniqueness** (chosen).  `orderZeroDatum_add/_sub` proved by
  `isSobolevDatum_unique` (`ForceClass.lean:286`): both sides realize the same physical field, so
  they coincide.  The `SchwartzPairable` hypotheses that `isSobolevDatum_add`/`isSobolevDatum_sub`
  demand come free from the bare `MemLp` via `schwartzPairable_of_memLp (fun i => memLp_component hz i)`
  (`ForceClass.lean:213`, `OrderZeroDatum.lean:67`).  **No continuity hypothesis needed** — the
  `MemLp` route to `SchwartzPairable` is Hölder-only, so the "direct-from-definition by layer
  linearity" fallback the task allowed was unnecessary and was not used.
- **`isSobolevDatum_sub` was missing** from `ForceClass.lean` (only `isSobolevDatum_add:261`
  exists).  Added here as an exact mirror: `map_sub`/`integral_sub`/`PiLp.sub_apply` replacing
  `map_add`/`integral_add`/`PiLp.add_apply`.  The `rfl` coercion
  `(((A - B) i : RealSobolevHilbert s) : FourierData) = (A i : FourierData) - (B i : FourierData)`
  worked, matching how `isSobolevDatum_add` uses `rfl` for the `+` coercion.
- **`lerayComplement` linearity is one line.**  `Leray.lerayComplement 0` is a `→L[ℝ]`
  (`LerayDatum.lean:255`), so `map_sub`/`map_add` apply directly; `lerayComplementAmbientLM`
  (`LerayDatum.lean:118`, the raw `LinearMap`) was **not** needed — the bundled CLM already carries
  additivity.  (REVIEW_ORDER_ZERO §6.3 anticipated a few lines via `lerayComplementAmbientLM`; the
  CLM `map_sub` is even shorter.)
- **Namespace pitfall (recorded).**  First compile failed because `Space` in the new module
  resolved to the wrong namespace; fixed by `open ... NavierStokes.ProblemStatement` (matching
  `ForceClass.lean:91` / `OrderZeroDatum.lean:60`), which is where `Space = EuclideanSpace ℝ (Fin 3)`
  and `SchwartzPairable`/`IsSobolevDatum` expect it.

## Group 2 — momentum-slice regularity

- **`∇p ∈ L²` is literally `ClassicalSolutionR.pressure_gradient`** restricted from `Ico 0 T` to
  the interior time (`⟨le_of_lt ht.1, ht.2⟩`) — `memLp_pressureGradient_slice`.
- **`∂ₜu ∈ L²` and `∂ₜu ∈ C^∞`** both go through `temporalDerivative_slice_eq`
  (`Pressure.lean:196`, `∂ₜu = f − (u·∇)u + νΔu − ∇p`).  The `f`/`(u·∇)u`/`νΔu` block is packaged
  as one `A05.SmoothL2` via `smoothL2_add (smoothL2_sub … …) (smoothL2_const_smul … ν)`
  (`Pressure.lean:143,172,156`); `.memLp` (`SmoothJets.lean:52`) and `.1` extract `L²`/`ContDiff`,
  then `.sub` with the `∇p` fact.  `contDiff_pressureGradient_slice` (`DatumToJets.lean:504`)
  supplies the cheap spatial `C^∞` of `∇p`.  These are **not** `SmoothSquareIntegrableJets` for
  `∂ₜu` — that is the P2 gap — only `L²`/`C^∞`, which is all the seed needs.
- **div-free shape agrees by `rfl`.**  `sum_partialDeriv_temporalDerivative_eq_zero` is
  `DivergenceTime.spatialDivergence_temporalDerivative_eq_zero:131` verbatim: the transverse lemma's
  `∑ⱼ partialDeriv j z x j` (with `A03.partialDeriv`) is definitionally
  `spatialDivergence (fun p => ∂ₜu p.1 p.2) t x` (both reduce, via `lift`/`Prod.snd`/eta, to
  `∑ i, (fderiv ℝ (fun y => ∂ₜu t y) x eᵢ) i`).  Confirmed by direct `exact` (no coercion tactic),
  matching REVIEW_ORDER_ZERO §6.5.
- **curl-free of `∇p` — lane 106 NOT importable; done directly.**  `Section4/A01/PressureGauge.lean`
  and `hasSymmetricJacobian_pressureGradient` are absent from this worktree's `A01/`
  (only `ConvectionDivergence`, `ProjectedEquation`, `RadialPotential`), so the curl-free property
  was proved from `ContDiffAt.isSymmSndFDerivAt` directly — the same in-tree Clairaut route
  `DivergenceTime.lean:115` uses for `div ∂ₜu`.  Chain:
  1. `pressureGradient_apply`: `(∇p y) j = fderiv ℝ (fun z => p(t,z)) y (cv j)`.  Component of the
     sum `∑ᵢ (∂ᵢp) eᵢ` read off with `WithLp.ofLp_sum` + `Finset.sum_apply` + `PiLp.single_apply`
     + `Finset.sum_ite_eq`.
  2. `partialDeriv_gradient_eq_sndFDeriv`: `partialDeriv i ∇p x j = D²(p(t,·)) x eᵢ eⱼ`.  Pull the
     `j`-projection (`PiLp.proj (𝕜:=ℝ) 2 _ j`) through the outer `fderiv` and the `i`-th partial
     through the evaluation `ContinuousLinearMap.apply ℝ ℝ (cv j)`, both by the CLM chain rule
     `(L.hasFDerivAt.comp x hg.hasFDerivAt).fderiv`, glued by `pressureGradient_apply`.
  3. `partialDeriv_pressureGradient_symm`: `IsSymmSndFDerivAt.eq` on the smooth scalar slice.

### Failed / corrected sub-approaches (Group 2, item 5)

- **`PiLp.proj 2 (fun _ => ℝ) j` stuck** ("typeclass instance problem is stuck,
  `Fin 3 → Module (?m y) ℝ`): the scalar field `𝕜` of `PiLp.proj` cannot be inferred from the
  codomain `ℝ`.  Fixed with the explicit `(𝕜 := ℝ)` (as `DivergenceTime.lean` does).
- **`rw [hfun]` did not fire** when `hfun` was stated as a `fun y => L (g y)` lambda: `HasFDerivAt.comp …
  |>.fderiv` produces the **`Function.comp`** form `⇑L ∘ g`, which the lambda does not match
  syntactically.  Fixed by stating `hfun` with `∘` and finishing the CLM equality with
  `congrArg (fun h => fderiv ℝ h x) hfun` instead of `rw`.
- **`EuclideanSpace.single_apply` is deprecated** → emits a warning (breaks the "silent" check).
  Replaced by `PiLp.single_apply`, which matches `(EuclideanSpace.single c 1).ofLp j` and is silent.
- **`Finset.sum_ite_eq'` vs `Finset.sum_ite_eq`**: after `PiLp.single_apply` the guard is
  `if j = c` (not `if c = j`), so the primed lemma missed; the unprimed `Finset.sum_ite_eq` fires.

## Group 3 — table

`SL8_SPLIT.md` records (i) order-0 identity, (ii) order-`m` bootstrap, (iii) all-orders finish, each
row with a Lean-ready statement, size, and inputs (file:line).  `isSobolevDatum_lower_iff`
(`LerayLowering.lean:214`) checked to be exactly `IsSobolevDatum r z (lowerVectorL s r hrs A) ↔
IsSobolevDatum s z A`, so the bootstrap (row ii.4) is the ≈10-line `.mp`.  (Post-review: lanes 108
and 106 have merged, so row i.6 is now an in-tree one-liner and no row is blocked — see the "Review
response" section below and `SL8_SPLIT.md`.)  The curl-free input row i.6 needs is delivered here by
`partialDeriv_pressureGradient_symm`.

## Commands

```
cd verification && lake build NSFormalization.Section4.D01.OrderZeroAlgebra NSFormalization.Section4.D01.MomentumSlice
    → Build completed successfully (9921 jobs).
cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/OrderZeroAlgebra.lean → silent, exit 0
cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/MomentumSlice.lean    → silent, exit 0
cd verification && lake env lean ../research/D01/axioms_sl8_prep.lean
    → 12 declarations, all [propext, Classical.choice, Quot.sound]
```

## Review response (lane 111 ACCEPT-WITH-NOTES, `REVIEW_SL8_PREP.md`)

Applied in-worktree, no git:

- **F-2** — exported the momentum residual as `MomentumSlice.smoothL2_momentumResidual_slice` (body
  = the verbatim old `hpart`); `memLp_temporalDerivative_slice` and `contDiff_temporalDerivative_slice`
  now open with `have hpart := smoothL2_momentumResidual_slice u hf ht`.  Their statements are
  byte-identical to before.
- **F-6** — dropped the redundant `hg` binder of `partialDeriv_gradient_eq_sndFDeriv`; it is now
  derived inline from `hφ` (the body of `contDiff_pressureGradient_slice`: `hφ.fderiv_right` then
  `ContDiff.sum` over the gradient columns).  Only this theorem's statement changed; the sole
  caller `partialDeriv_pressureGradient_symm` drops the `hg` argument (its own `have hg` deleted, no
  statement change).  Verified via `research/D01/scratch_f6.lean` before editing (silent).
- **F-7** — module docstring and `partialDeriv_pressureGradient_symm`'s docstring now name the real
  order-0 consumer, 108's `Leray.lerayComplement_zero_orderZeroDatum_eq_self` (bare `MemLp`), and
  state explicitly that `Longitudinal.lerayComplement_eq_self_of_curl_free` cannot apply at order 0
  (needs `SmoothL2Field`, order `(m:ℝ)+1`).
- **F-1** — `SL8_SPLIT.md`: lanes 106/108 merged; row i.6 is now the in-tree one-liner
  `Leray.lerayComplement_zero_orderZeroDatum_eq_self` (`OrderZeroCurl.lean:510`, `D01.Leray`,
  signature transcribed from `git show origin/erenup/integration`); all "blocker" cells cleared;
  the `hcurl` input noted as 106's `hasSymmetricJacobian_pressureGradient … .2 x i j`; `lowerVectorL`
  noted as `D01.lowerVectorL`, not `D01.Leray`.
- **F-4** — `DatumToJets.lean:502 → 504` for `contDiff_pressureGradient_slice`, here and in
  `SL8_SPLIT.md`.
- **F-3/F-5** — informational; the 106 duplication (`pressureGradient_apply`,
  `partialDeriv_pressureGradient_symm`) is left for a SIMP lane after rebase, and the `D01.MemForceR`
  vs `A02.MemForceR` shadowing is noted in the SL8 table.
- **Probe** — the reviewer's end-to-end assembly (`/tmp/rev111/probe_assembly.lean`) is preserved
  as `research/D01/probes/sl8_assembly_probe.lean` (carries 108's corollary as a hypothesis `H108`
  and 106's `hcurl` via 111's `partialDeriv_pressureGradient_symm`, since neither module is in this
  worktree); recompiled with `lake env lean`, silent.
