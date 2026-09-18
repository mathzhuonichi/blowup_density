# REPORT 334 — T11 / U9d2c: the classical solution of a forced mild solution

Lane `334-T11-U9d2c-classical-assembly`, branch
`erenup/334-T11-U9d2c-classical-assembly` (integration branch with lane 327
merged).  **The U9d target is closed, with no named input**: no
`def … : Prop`, no `sorry`/`admit`/`axiom`/`native_decide`, one
`set_option maxHeartbeats 400000 in` on a single declaration.

## 1. 证了哪个定理 / What is proved

**`theorem NSFormalization.Section3.T11.mild_to_classical`** — the U9d
existential target, verbatim as recorded in `EXISTENCE_ROUTE.md`:

```lean
∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
  (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
  a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
  ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
    IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
    (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
    TorusForcedMildOn C A P T u →
    ∃ w : ClassicalSolutionT ν a g T,
      PeriodicLocalRegularity ν a g T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
```

Both residuals of lanes 326/327 are proved, not assumed:

* `ContDiffOn ℝ ∞ (torusPhysicalVelocity u) (Ico 0 T ×ˢ univ)`
  (`torusPhysicalVelocity_contDiffOn`);
* `ContDiffOn ℝ ∞ (mildPressure g u) (Ico 0 T ×ˢ univ)`
  (`mildPressure_contDiffOn`);

and with them the third open clause
`PeriodicLocalRegularity.sobolev_smooth` (`ContDiffOn ℝ ∞` of the order-`m`
Sobolev datum path), which needs the same machinery.

`PersistenceInput T u` is **discharged**, not assumed
(`persistenceInput_of_mild`, from lane 330's `persistence_unconditional` through
lane 320's `physicalCoeff_eq_iff_reweight`); so is `PersistenceInput T F`
(`forcePersistenceInput`) and `ContinuousOn P (Icc 0 T)`
(`forcedLeray_continuousOn`), the two side hypotheses lane 327 carried.

**Corollary `exists_classical_of_picard`** — for every `ν > 0`, every
`a ∈ initialClassT` and every smooth unit-periodic force `g`, there is a
positive horizon `δ` and a `ClassicalSolutionT ν a g δ` with all three
regularity clauses.  Unconditional: the contract comes from lane 328's
`torusConvolutionInput_ofReal`, the horizon from lane 313/317's
`torusForcedPicard_quantitative`, the force path from `smooth_periodic_datum`
plus lane 330's `torusLerayCLM`.

**Route, in one paragraph.**  Every time derivative costs two Sobolev orders,
and lane 330 supplies every order, so the induction closes: the order-`m`
realization `v_m` of the mild solution satisfies, in `H^m`,
`v_m(b) = v_m(0) + ∫₀ᵇ (νΔ v_{m+2} + P_m − Q_m)`, where `νΔ : H^{m+2} →L H^m`
is a bounded multiplier, `P_m` is the Leray-projected order-`m` force datum
path and `Q_m` is lane 328's real-order projected convolution of `v_{m+3}`.
Coefficientwise this identity is lane 327's `mild_physicalCoeff_hasDerivAt` plus
the scalar FTC; as an identity between Banach-valued paths it gives
`HasDerivWithinAt v_m (…) (Ico 0 T) t`, hence
`ContDiffOn ℝ (j+1) v_m` from `ContDiffOn ℝ j` of the derivative, by induction
on `j` uniformly in `m` (`mildTower_contDiffOn`).  Joint smoothness on the slab
is then obtained without any `contDiffOn_tsum`: the Fourier inversion is
packaged as a **functional-valued** series
`torusEvalSeriesCLM s i x = ∑' k, χ_k(x) • (coefficient functional)`, which is
`C^n` in `x` by `contDiff_tsum` once `2n+6 ≤ s`, and the field is the bounded
bilinear evaluation of that family against the smooth path `v_s`.  The pressure
runs through the same evaluation, with datum path
`pressurePotentialCLM (F_m − Q^{unproj}_m)`.

## 2. Lean 里现在有什么 / What is in Lean

New module `formalization/NSFormalization/Section3/T11/MildClassical.lean`
(1354 lines, 77 named declarations including three explicitly named local
instances).  No existing module was modified.

| section | content |
|---|---|
| 0 | `timeDerivField` and its smoothness / periodicity / `HasDerivAt` |
| 1 | `periodicFourierCoeff_time_hasDerivAt` (differentiation under the cube integral), `datumPath_hasDerivAt`, **`datumPath_contDiff`**: the order-`m` datum path of a smooth unit-periodic space-time field is `C^∞` in time |
| 2 | `mildLaplaceCLM`, `mildTowerDeriv`, `mildTowerDeriv_coeff`, `mildTower_unique`, **`mildTower_contDiffOn`**: every order-`m` realization of a forced mild solution is `C^∞` on `Ico 0 T` |
| 3 | `torusPhysicalCoeffCLM`, `torusEvalSeriesCLM`, `torusEvalSeriesCLM_contDiff`, `fourierSlice_contDiffOn`, **`torusPhysicalVelocity_contDiffOn`** |
| 4 | `torusConvUnprojCLM`: the unprojected real-order convolution as a genuine bounded bilinear map (lane 328's bilinearity lemmas are `private`, so they are re-proved here) |
| 5 | `pressureSymbol`, `pressurePotentialCLM`: the Leray potential as a bounded operator, with `sum_pressureSymbol_eq` identifying it with lane 326's `lerayPotentialCoeff` |
| 6 | `mildSourceDatum`, `mildPressureDatum`, their coefficient identities, **`mildPressure_contDiffOn`** |
| 7 | **`mild_to_classical`**, **`exists_classical_of_picard`** |
| 8 | `mild_to_classical_affine_constant` and two `example`s (non-vacuity) |

Reusable beyond this lane: `datumPath_contDiff` (time smoothness of force datum
paths at every order), `torusEvalSeriesCLM` (Fourier inversion as a `C^n` family
of functionals), `torusConvUnprojCLM`, `pressurePotentialCLM`,
`mildClassical_summable_inv_rpow`.

Files: the module; `research/T11/probes/mild_classical_closes.lean`;
`research/T11/axioms_mild_classical.lean`;
`research/T11/ATTEMPTS_MILD_CLASSICAL.md`; this report; one appended paragraph
in `research/T11/EXISTENCE_ROUTE.md` and one line in `research/T11/T11_SPLIT.md`.

Non-vacuity: `mild_to_classical_affine_constant` instantiates **all** hypotheses
of `mild_to_classical` on the constant-force affine family
`u t = (1+t)·c` over an arbitrary horizon `T > 0`; the probe takes
`c = coordinateVector 0` and shows the produced classical velocity is nonzero at
the origin, together with the genuine `TorusForcedMildOn` witness.

## 3. 缺口是什么 / What is not proved

1. **No uniform (quantitative) lifespan.**  `exists_classical_of_picard` gives
   the Picard horizon `torusKernelTime ν (torusPicardThreshold ‖bilinear‖ (‖A‖+B))`,
   which depends on the `H³` norm of the datum and on a force supremum.  It is
   **not** `PeriodicQuantitativeLocalInput'` (the U9e target: one `δ` uniform
   over an `H¹` ball with order-wise `L¹_t H^m` force bounds), so
   `Section3/T11/Restart.lean` still consumes its named input unchanged.
2. **Smoothness of `g` is global.**  Like lane 330, the force smoothness
   hypothesis is `ContDiff ℝ ∞ g` on all of space-time; there is no
   `ContDiffOn`-on-a-slab variant of `continuous_datum_path` in the tree, and
   `datumPath_contDiff` inherits that.
3. **Uniqueness of the classical solution** is untouched here; only the
   coefficient-side uniqueness of lanes 313/315 exists.
4. No sharpness, no blow-up criterion, no continuation: those are U10/U11/U15.

No target statement was weakened; no `def … : Prop` packaging a goal or a field
was introduced.

## 4. 跑了什么命令、什么结果 / Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildClassical
  → ✔ [9993/9993] Built NSFormalization.Section3.T11.MildClassical
    Build completed successfully (9993 jobs).  0 errors; the only warnings in
    the log are pre-existing ones in Paper1/*, Source/* and vendor/HeliCorgi/*.

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/MildClassical.lean
  → no output (0 errors, 0 warnings)

cd verification && lake env lean ../research/T11/probes/mild_classical_closes.lean
  → no output; the verbatim U9d target closes by `mild_to_classical`, the two
    residual `ClassicalSolutionT` fields and `sobolev_smooth` close verbatim,
    the restart-shaped corollary closes, the nonzero affine-constant instance
    closes, and 3 embedded `#guard_msgs` axiom checks pass

cd verification && lake env lean ../research/T11/axioms_mild_classical.lean
  → no output; all 77 `#guard_msgs` pass, i.e. EVERY top-level declaration of
    the module prints exactly [propext, Classical.choice, Quot.sound]

make check   (from the worktree root)
  → check_formalization_plan / check_contracts OK; test_contract_policy 13/13 OK;
    check_work_queue: "45 work items: ownership, contract registration and task
    cards consistent."

make test    (from the worktree root)
  → all registered contracts replay: "checked; standard logical axioms only"

grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" on the module, probe
and audit → one hit: `set_option maxHeartbeats 400000 in` on
`mildTower_contDiffOn_nat` (commented, per-declaration, within budget).
```
