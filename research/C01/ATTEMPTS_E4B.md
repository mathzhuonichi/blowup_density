# ATTEMPTS — lane 148-C01-e4b-pressure-jets (row E4b; the ∇p-jet / hB obligation)

Module delivered: `formalization/NSFormalization/Section4/C01/PressureJetPath.lean`
(namespace `NSFormalization.Section4.C01`).  Axiom audit:
`research/C01/axioms_e4b.lean` — all 12 declarations `[propext, Classical.choice, Quot.sound]`,
plus two non-vacuity examples on `A04.zeroSol`.

## Result summary (E4b — DONE, every order)

Over the interior window `[c,S] ⊂ (0,T)` (`0 < c ≤ S < T`), for `w : ClassicalSolutionR ν a f T`
and `hf : MemForceR f`:

* `pressureGradientPath_jetLp_continuous` :
  `∀ n, Continuous (fun t : Icc c S => (pressureGradientField w hf ⟨…∈Ioo 0 T…⟩).jetLp n)`.
* `temporalSlicePath_jetLp_continuous` (the **`hB`** clause of
  `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt`) :
  `∀ n, Continuous (fun t : Icc c S => (temporalSliceField w hf ⟨…⟩).jetLp n)`.

Both hold at **every** order `n`; there is **no order-1 hole** (see below).

## What closed, and how

### Glue (a) — `HasWeakDerivsL2Bound` written through the jets
Delivered not as the review's literal `eLpNorm (∂^α Z.field) 2 ≤ ‖Z.jetLp k‖` but in the
equivalent jet-`Lp`-norm language that `D01.HasWeakDerivsL2Bound` actually consumes (its
recursion uses the coordinate `directionalField`s, not `∂^α`), which avoids all
`iteratedFDeriv`/`eLpNorm` bookkeeping:

* `norm_jetPostcompose_le : ‖jetPostcompose L n‖ ≤ ‖L‖`
  (`ContinuousLinearMap.opNorm_le_bound` + `norm_compContinuousMultilinearMap_le`).
* `norm_jetLp_mapField_le : ‖(mapField L A).jetLp n‖ ≤ ‖L‖·‖A.jetLp n‖`
  (`jetLp_mapField` + `ContinuousLinearMap.norm_compLpL_le` + above).
* `norm_directionalField_jetLp_le : ‖(directionalField A v).jetLp n‖ ≤ ‖v‖·‖A.jetLp (n+1)‖`
  (`directionalField = mapField (apply ℝ Space v) A.derivative`, `‖apply ℝ Space v‖ ≤ ‖v‖`,
  `norm_derivative_jetLp`).
* `hasWeakDerivsL2Bound_of_jetLp_sq_le (m Z M) : (∀ k ≤ m, ‖Z.jetLp k‖² ≤ M) →
  D01.HasWeakDerivsL2Bound Z.field M m` — the `D01.exists_hasWeakDerivsL2Bound_smooth`
  recursion, but carrying a *fixed* `M`: at each step the directional field `Z.directionalField
  (coordinateVector j)` has `‖·.jetLp k‖ ≤ ‖Z.jetLp (k+1)‖` (via the previous bound and
  `‖coordinateVector j‖ = 1`, `PiLp.norm_single`), so the hypothesis passes down the recursion
  unchanged; the seed is `‖Z.jetLp 0‖ = (eLpNorm Z.field 2).toReal` (`norm_jetLp_zero`,
  `Lp.norm_toLp`); the pairing is verbatim `D01.smoothField_weakDeriv_pairing`.

### Item 2 — jets ⟹ datum-path continuity (every order)
* `norm_smoothAngularDatum_sub_sq_le (m A B) :
  ‖smoothAngularDatum m (m:ℝ) _ A − smoothAngularDatum m (m:ℝ) _ B‖²
    ≤ 16^m·∑_{k≤m}‖A.jetLp k − B.jetLp k‖²`.
  The datum difference is a Sobolev datum of the *field* difference `A.field − B.field` via
  **`D01.isSobolevDatum_sub`** (the `OrderZeroAlgebra` `SchwartzPairable` version), and its
  square norm is `D01.norm_isSobolevDatum_le_of_memLp_derivs` with `M = ∑_{k≤m}‖A.jetLp k −
  B.jetLp k‖²` supplied by glue (a) on `fieldSub A B` (`jetLp_fieldSub`).
* `smoothAngularDatum_path_continuous (P hP m) : Continuous (fun t : Icc c S =>
  smoothAngularDatum m (m:ℝ) _ (P t))` — a per-point squeeze (`squeeze_zero_norm`,
  `tendsto_sub_nhds_zero_iff`): `‖A_{P t} − A_{P t₀}‖ ≤ √(16^m·∑ ‖(P t).jetLp k − (P t₀).jetLp
  k‖²)`, and the RHS is continuous in `t` with value `0` at `t₀`.

### The **order-1 hole is closed** (correction to review 146 N2)
Review 146 (N2) flagged order 1 as an uncovered hole because
`A03.isSobolevDatum_sub` (`VectorTameProduct.lean:186`) carries `hs : 2 ≤ s`, order 0 has
`A01.orderZeroDatumCLM`, and structural additivity of `smoothAngularDatum` was not in tree.
The hole does **not** exist: `D01.isSobolevDatum_sub` (`OrderZeroAlgebra.lean:51`, the
subtraction partner of `ForceClass.isSobolevDatum_add`) needs only `SchwartzPairable z` /
`SchwartzPairable w`, which every `SmoothL2Field` supplies via
`D01.schwartzPairable_of_memLp (fun i => D01.memLp_component ·.memLp i)`, at **any** real order.
So item 2 (and hence the whole E4b chain) holds uniformly for all `m ≥ 0`; there was never a need
for the A03 `2≤s` lemma, `orderZeroDatumCLM`, or a raising construction.  `A01.DatumPathContinuity`
is **not** imported.

### Item 3 — the pressure-gradient jets
`pressureGradientPath_jetLp_continuous` runs the three-step chain at datum order `m = n`
(so `jetOfDatum n n` reconstructs the order-`n` jet directly — no `n+2` detour needed):
`residualPathIcc` (the row-E4a `residualPath` restricted to `Icc c S ↪ Icc 0 S`) has jets
continuous in time; item 2 gives the order-`n` datum path; `Leray.lerayComplement (n:ℝ)` (a CLM)
preserves continuity; `isSobolevDatum_pressureGradient_lerayComplement w hf _ hAm` pins it to
`∇p`s order-`n` datum with `hAm` = `smoothAngularDatum_isSobolevDatum` rewritten by
`residualPathIcc_field` (token-for-token the residual field `f − adv + ν•Δu`); then
`jetOfDatum_continuous n n _` + `D01.jetOfDatum_ae` reconstruct the jets — the exact pattern of
`forcePath_jetLp_continuous`.

### Item 4 — the derivative slice
`temporalSlicePath_jetLp_continuous` : `temporalSliceField.field = (fieldSub residualPathIcc
pressureGradientField).field` (from `temporalDerivative_eq_residual_sub_pressureGradient`),
transported by `EulerLpSmoothCoefficientProduct.jetLp_congr`, then `jetLp_fieldSub` splits into
residual jets (E4a) minus ∇p jets (E4b), each continuous — `Continuous.sub`.

## Notes / deviations recorded (updated after review 148, notes N1/N2)
* **`hcS : c ≤ S` dropped (N1).**  Review 148 confirmed (probe
  `research/C01/probes/rev148_leray_hcs.lean`) that the lane's own proof compiles verbatim with the
  `hcS` binder deleted, so `hcS` is removed from **both** `pressureGradientPath_jetLp_continuous`
  and `temporalSlicePath_jetLp_continuous` (once `pressureGradientPath` drops it, the pass-through
  in `temporalSlicePath` is the only use, so keeping it there would be inert and re-trigger the
  linter).  There is now **no `set_option linter.unusedVariables false` anywhere** in the module.
  The signatures are `(w) (hf) (hc : 0 < c) (hST : S < T) (n)`.  The E4 lane supplies `0 ≤ S − c`
  from its own `hcS` in the window-translation step; it does not need it in these signatures.
* **Non-vacuity strengthened (N2).**  `research/C01/axioms_e4b.lean` instantiates the
  **non-degenerate** window `Icc (1/2:ℝ) 1 ⊂ (0,2)` (not the one-point `Icc 1 1`) on
  `A04.zeroSol 1 2`, at jet orders `0` and `2`, so the `Continuous` witnesses are not vacuous for
  type reasons.
* **N3 window-shift is already discharged at the path level**: all E4b paths are indexed by
  `Icc c S = [c,S] ⊂ (0,T)`, off both endpoints, so `pressureGradientField`/`temporalSliceField`
  are always evaluated at interior times.

## What E4 itself still needs (not this lane) — with the exact assembly statement

The `hB` clause is now in hand.  Row **E4** (`d/dt ‖u(·)‖²_{L²} = 2⟪u,∂ₜu⟫` at an interior time)
still owes the assembly into the vendor derivative machinery, which lives on a *closed* interval
`Icc 0 T'` (`Euler/OrdinaryWordTime.lean:69–75`, variable order
`(T) (hT : 0 ≤ T) (A B : Icc 0 T → SmoothL2Field Space) (hA) (hB) (hd)` then `(s) (t)`).  Steps:

1. **Window translation.**  `T' := S − c`, `hT' : 0 ≤ T'` (from `hcS`), and the continuous shift
   `σ : Icc (0:ℝ) T' → Icc c S`, `σ r := ⟨r.1 + c, _⟩`, composed with `Icc c S ↪ Icc 0 S` for the
   velocity.  `hA := (C01.velocityField_jetLp_continuous w hST).comp σ`;
   `hB := (C01.temporalSlicePath_jetLp_continuous w hf hc hST).comp σ` (**this lane**; note: no
   `hcS` argument any more).
2. **`hd` — the pointwise `HasDerivAt` in time (N4: NOT exported).**  The only copy of the
   pointwise fact `HasDerivAt (fun s => w.velocity (s,x)) (temporalDerivative w.velocity s x) s`
   lives **inline** in `A04.timeDeriv_isSobolevDatum` (`Section4/A04/TimeDerivative.lean:182–206`),
   guarded there by `2 ≤ m` and a `ContDiffOn G` hypothesis — it is not a reusable lemma.  The E4
   lane must **re-prove it (≈7 lines) from `velocity_smooth`** (`ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)`
   → `HasDerivAt` in the time slot), then (b) the `+c` chain rule (`(hasDerivAt_id r).add_const c`,
   derivative `1`), then (c) the `projIcc` step — near an interior `r`, `projIcc 0 T' hT' ρ = ⟨ρ,_⟩`,
   so `HasDerivAt.congr_of_eventuallyEq` on `Ioo 0 T' ∈ 𝓝 r`; `(B ⟨r,…⟩).field x =
   temporalDerivative w.velocity (r+c) x` is `temporalSliceField_field` (`rfl`).
3. **The `s = 0` word bridge (N3: NO `wordEnergy_zero` lemma in the vendor).**  At `s = 0` the vendor
   produces the value `2*(∑ n ∈ range 1, ∑ w : Fin n → Fin 3, ⟪(wordField (A t) w).toLp,
   (wordField (B t) w).toLp⟫_ℝ)` and `wordEnergy 0 (A (projIcc … r))` — **not** already collapsed to
   `2⟪(A t).toLp,(B t).toLp⟫` / `‖(A t).toLp‖²`.  Collapsing both needs `wordField_zero` plus the
   singleton `Fin 0 → Fin 3` (`range 1 = {0}`, one word).
4. **`HasDerivWithinAt (Icc 0 T') → HasDerivAt`**: at interior `r ∈ Ioo 0 T'`,
   `HasDerivWithinAt.hasDerivAt` with `Icc_mem_nhds hr.1 hr.2`.
5. **Hand-off**: identify `A ⟨r,…⟩` with `MomentumCarrierB.velocitySliceField w _` — both are
   `SmoothL2Field` records with `field = fun x => w.velocity (·,x)` and `Prop`-valued
   `smooth`/`integrable`, so `rfl` (a one-line check to do first).

**Exact statement the next lane must prove** (the value fact
`C01.energyIdentity_classical`, `MomentumCarrierB.lean:254-258`, takes as its `hd` hypothesis
`hd : d = 2 * ⟪(velocitySliceField w _).toLp, (temporalSliceField w hf ht).toLp⟫`):

```lean
/-- E4.  On a window `[c,S] ⊂ (0,T)`, the `L²` energy of the velocity is differentiable in
time at every interior point, with derivative `2⟪u(t,·), ∂ₜu(t,·)⟫`. -/
theorem energyDerivative_hasDerivAt
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    HasDerivAt
      (fun ρ : ℝ =>
        ‖(velocityField w hST
            ⟨(projIcc (0:ℝ) (S - c) (by linarith) ρ).1 + c, by constructor <;> …⟩).toLp‖ ^ 2)
      (2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self
                (mem_Ioo_of_mem_Icc hc hST ⟨by linarith, by linarith⟩))).toLp,
            (temporalSliceField w hf
                (mem_Ioo_of_mem_Icc hc hST ⟨by linarith, by linarith⟩)).toLp⟫_ℝ)
      r
```

(with the two membership proofs at the time `r + c ∈ Icc c S`).  Composed with
`energyIdentity_classical` this discharges the last input of row **energyIdentity**, i.e.
`d = −2ν·∫∑ᵢ‖∂ᵢu‖² + 2·∫⟪u,f⟫`.

## Failed / discarded approaches
* **`A03.isSobolevDatum_sub` (2≤s) for item 2** — would have left order 1 open (review 146 N2).
  Discarded once `D01.isSobolevDatum_sub` (SchwartzPairable, all orders) was found; the latter is
  strictly more general and needs no `LocIntField`.
* **Datum order `m = n+2`** (to keep `m ≥ 2` for the A03 lemma) — unnecessary once order 1 closed;
  `m = n` is used, so `jetOfDatum n n` reconstructs the jet with no re-indexing.
* **Bare `Space`** — `formalization` has `autoImplicit`, so an unopened `Space` was silently bound
  as a fresh type variable (`NormedAddCommGroup Space` synthesis failures cascading everywhere);
  fixed by `open NavierStokes.ProblemStatement (… Space)`.  (Both `NavierStokes.ProblemStatement.Space`
  and `EulerSmoothLimit.Space` are `abbrev … EuclideanSpace ℝ (Fin 3)`, defeq.)
* **`Finset.single_le_sum … (Finset.mem_range.mpr (by omega))`** — `omega` saw an undetermined
  index metavariable (elaboration order); fixed with an explicit `(f := …)` and
  `Nat.lt_succ_of_le hk`.
* **`hval ▸ hbndcont.continuousAt`** — `▸` could not locate the point metavariable; replaced by
  `simpa using hbndcont.tendsto t₀`.

## Commands run

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.PressureJetPath` | exit 0, `Build completed successfully (10301 jobs)`, no line mentioning the module |
| `lake env lean …/PressureJetPath.lean` | exit 0, **0 bytes** |
| `lake env lean ../research/C01/axioms_e4b.lean` | exit 0; 12/12 `[propext, Classical.choice, Quot.sound]`; both `A04.zeroSol` examples elaborate |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|^\s*axiom ' …` | no output |
| `make check` | exit 0 (13 contract-policy tests OK; 30 work items consistent) |
