# REPORT_431 — T17 U8 force torus support volume / duration (Opus; transcribed by lead from the agent message, report-file guard)

Committed on `erenup/431-T17-U8-force-volume`.

## 1. What was proved

**Unit U8 of T17, complete.** Both canonical `CorrectionAPI` fields at the concrete `correctionData`, plus the constant and its nonnegativity.

The constant (`spatialVolumeConst θR = π * 4 / 3 * θR ^ 3`, i.e. the manuscript's `(4/3)π θRadius³`):

```
def spatialVolumeConst (θR : ℝ) : ℝ := Real.pi * 4 / 3 * θR ^ 3
theorem spatialVolumeConst_nonneg {θR : ℝ} (hθR : 0 ≤ θR) : 0 ≤ spatialVolumeConst θR
```

The two fields (premises identical to lane 425's `force_support`, plus `hθR : 0 ≤ θR` on the spatial one):

```
theorem force_spatial_volume (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ) (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hθR : 0 ≤ θR)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      periodicTorusMeasure (torusSpatialSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3)

theorem force_time_length (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) … :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      volume (torusTemporalSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (4 * ε ^ 2)
```

The reusable new torus lemma:

```
theorem measure_torusPoint_image_le {A : Set Space} (hA : IsCompact A) :
    periodicTorusMeasure (torusPoint '' A) ≤ volume A
```

Route: lane 425's `force_support` bounds the Euclidean `tsupport`; `torusSpaceTimeLift f z = f (z.1, torusRepr z.2)` reads the field at the `(0,1]³` representative, so a support point lands in `torusPoint '' ball x₀ (ε θR)`, enlarged to the **closed** ball so that the target is closed and survives the `closure` in `tsupport` (`torusRepr` is discontinuous — this is the one place the plan had to be adjusted). The measure bridge tests against the unit-periodic indicator of `periodicSet A`, so `T13.torusLift_torusPoint` gives the value 1 on the whole image with no representative arithmetic; T15's `lintegral_enorm_torusLift` moves it to the fundamental cube, and T13's `lintegral_eq_tsum_halfOpenCube` folds the lattice sum back into `volume A`. Constants come from `EuclideanSpace.volume_closedBall_fin_three` and `Real.volume_Icc`. The registered `I02.force_spatial_volume` turned out not to be needed.

## 2. What exists in Lean now

- `/data_8T/ping/blowup_density/.claude/worktrees/431-T17-U8-force-volume/formalization/NSFormalization/Section3/T17/ForceVolume.lean` — 25 declarations, no new module edits elsewhere.
- `/data_8T/ping/blowup_density/.claude/worktrees/431-T17-U8-force-volume/research/T17/probes/force_volume_closes.lean` — field-shape `example`s via `A.force_spatial_volume` / `A.force_time_length` / `A.spatialVolumeConst_nonneg`, the two fields closed by `exact` at `correctionData`, `fields_at_placement` at `place.x₀`/`place.T`, and `nonvacuous_force_volume` at lane 425's constant-reference witness.
- `/data_8T/ping/blowup_density/.claude/worktrees/431-T17-U8-force-volume/research/T17/axioms_u8.lean`
- `/data_8T/ping/blowup_density/.claude/worktrees/431-T17-U8-force-volume/research/T17/probes/rev431_wrong_volume_exponent.lean` and `.../rev431_wrong_time_length.lean` — negative probes (expected to fail; they do).
- `/data_8T/ping/blowup_density/.claude/worktrees/431-T17-U8-force-volume/research/T17/ATTEMPTS_U8.md`, and a U8 status paragraph in `.../research/T17/T17_SPLIT.md`.

## 3. Gaps

- **No residual goal.** Nothing is left open in U8; no `sorry`/`axiom`/named input.
- **Two premises beyond the canonical field text**, both data hypotheses that the U12 assembly discharges: `hv : ContDiff ℝ ∞ v` (the documented G1 premise, inherited *only* through lane 425's `force_support` — no step of this lane uses reference regularity again), and `hθR : 0 ≤ θR`, which is `T16.LocalPotentialAPI.theta_radius_pos`. The latter is needed because `ENNReal.ofReal` would silently erase a negative constant; I rejected `|θR|³` / `max θR 0` spellings that would make `spatialVolumeConst_nonneg` hypothesis-free, since they distort the manuscript constant.
- **Approaches tried and abandoned** (all in ATTEMPTS_U8.md): (a) the "hard direction" `torusPoint x = torusPoint y → ∃ k, x - y = latticeVector k` — true but needs a coordinatewise `QuotientAddGroup.eq_iff_sub_mem` plus choice over `Fin 3`; sidestepped by the periodic indicator; (b) translating the ball into the cube using `periodicTorusMeasure_isAddRightInvariant` — needs `|x i - c i| ≤ ‖x - c‖`, for which there is no ready `PiLp.norm_apply_le_norm` at this pin, and only yields a small-ball lemma; (c) `measure_iUnion_le` on `periodicSet A = ⋃ k (A + latticeVector k)` with an `Equiv.neg` reindexing — replaced by a pointwise majorant needing no set algebra or measurability of `periodicSet A`; (d) keeping the open ball in the lift target — `torusPoint '' ball` is not closed; (e) `funext` on `Space` fails at this pin (`WithLp` is a structure, not a Pi type — error: "could not unify the conclusion of `@funext`"), so `PiLp.ext` is used; (f) lemmas stated with `T13.latticeVector` do not `rw` inside `T16.periodicSet` goals ("Did not find an occurrence of the pattern") even though the two are `rfl`-equal, so §0 restates the lattice algebra in the T16 spelling and crosses over once in `latticeVector_eq`; (g) `push_cast` leaves `↑((-k) i) = -↑(k i)` untouched, `Pi.neg_apply` must come first.

## 4. Commands run and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.ForceVolume
  → ✔ [10018/10018] Built NSFormalization.Section3.T17.ForceVolume (3.3s)
    Build completed successfully (10018 jobs).   [0 errors]

cd verification && lake env lean ../formalization/NSFormalization/Section3/T17/ForceVolume.lean
  → 0 lines of output

cd verification && lake env lean ../research/T17/probes/force_volume_closes.lean
  → 0 lines of output

cd verification && lake env lean ../research/T17/axioms_u8.lean
  → 25 "depends on axioms" records; normalized check: 25 records, 0 non-standard
    (every one is exactly [propext, Classical.choice, Quot.sound]; the 4 probe
     theorems were checked the same way in a scratch copy and are also standard)

cd verification && lake env lean ../research/T17/probes/rev431_wrong_volume_exponent.lean
  → error: Type mismatch … has type … ofReal (spatialVolumeConst θR * ε ^ 3)
    but is expected to have type … ε ^ 2     (expected failure)

cd verification && lake env lean ../research/T17/probes/rev431_wrong_time_length.lean
  → error: Type mismatch … has type … ofReal (4 * ε ^ 2) … expected 2 * ε ^ 2
    (expected failure)

make check
  → check_formalization_plan OK; check_contracts OK; test_contract_policy: Ran 13 tests, OK;
    check_work_queue: 45 work items: ownership, contract registration and task cards consistent.

git commit → f60efeb2 on erenup/431-T17-U8-force-volume (no push, no merge, no rebase)
```


## Lead ruling after review 431 (REJECT on the extra premise `hθR : 0 ≤ θR`; merged on lead authority)

The premise is not a named input: `θR` is a raw parameter of `correctionData`, and its positivity is the threaded T16 record's field `LocalPotentialAPI.theta_radius_pos` (exactly as lane 434's `hcube` is the placement's `chartBall_in_cube`). The U12 assembly discharges it from `D.potential`; the alternative spellings (`|θR|³`, `max θR 0`) would distort the manuscript constant. The base-ref note was branch drift (`AffineVariation.lean` from #392), refreshed by the merge below. Lean, axioms and the two negative probes were accepted by the reviewer.
