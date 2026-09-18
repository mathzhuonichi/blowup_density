# REPORT 338 — T11 / U9e: the `H³`-ball existence input, proved; continuation chain re-instantiated

Lane `338-T11-U9e-existence-input-h3`, branch
`erenup/338-T11-U9e-existence-input-h3` (lane base = integration + 334, with
lane 337 merged in as the brief allows).  **The U9e target is closed with no
named input**: no `def … : Prop` standing for a goal, no `sorry`/`admit`/
`axiom`/`native_decide`, and — unlike every other lane on this line — **no
`set_option maxHeartbeats` at all**.

## 1. 证了哪个定理 / What is proved

**`theorem NSFormalization.Section3.T11.periodicQuantitativeLocalInputH3`**, i.e.
amendment 2's existence input, outright:

```lean
∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
  ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
    ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
        ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

This is `PeriodicQuantitativeLocalInput'` (`LocalExistence.lean:24`) with
`periodicSobolevENorm 3 a ≤ K` in place of `periodicSobolevENorm 1 a ≤ K` and
every other quantifier, hypothesis and conclusion unchanged — including the
order-wise `L¹_t H^m` force bounds `M`.

**The horizon is explicit and its dependence is a theorem, not a comment.**
`exists_classical_on_picardHorizon` proves the same conclusion with `δ` replaced
literally by

```lean
picardHorizon ν K M = torusKernelTime ν (torusPicardThreshold
    ‖(torusContractOf ν hν).analytic.bilinear‖ (K.toReal + (M 3).toReal))
```

a function of `ν`, `K` and `M` alone (`picardHorizon_pos`,
`picardHorizon_le_one`, `picardHorizon_eq`); the datum and the force are
supplied to it afterwards.  `periodicQuantitativeLocalInputH3` is the two-line
corollary.

**Which force orders are used: exactly `M 3`, and nothing else.**  The Picard
iteration lives in `H³ × H²`, so the only force quantity in the affine part of
the Picard map is the order-three Leray-projected datum path.  Every higher
order enters only through lane 330's unconditional `persistence_unconditional`.

**Route, in one paragraph.**  `C := torusContractOf ν hν` is lane 317's
two-space contract, a function of `ν` only.  `A` is the order-three datum of `a`
(`CriterionBridge.exists_periodicDatum_smooth`), and
`periodicSobolevENorm_eq_datum` turns `periodicSobolevENorm 3 a ≤ K` into
`‖A‖ ≤ K.toReal`.  `F₃` is lane 334's smooth order-three force datum path and
`P := torusLerayCLM 3 ∘ F₃` its Leray projection (lane 330), with
`‖P t‖ ≤ ‖F₃ t‖`.  The force hypothesis is an **`L¹`-in-time** bound
(`forceSobolevENormT 1 s f = ⨅_{datum paths G} eLpNorm G 1 (volume.restrict (Ioi 0))`),
never a supremum, so lane 313's `torus_forcedLinear_bound` is replaced by the
new `torus_forcedLinear_bound_L1`: the heat evolution is a contraction at every
order, hence `‖e^{νtΔ}A + ∫₀ᵗ e^{ν(t−s)Δ}P(s)ds‖ ≤ ‖A‖ + ∫₀^T ‖P(s)‖ds`.  That
integral is bounded by `(M 3).toReal` because the infimum defining
`forceSobolevENormT` is **attained** at every admissible path
(`forceSobolevENormT_eq_of_path`, from `T10.datum_unique`: two datum paths of
the same field agree on `[0,∞)`).  So `b := K.toReal + (M 3).toReal` dominates
the affine part uniformly over the ball, `torusPicardConstants_explicit` (313)
supplies the self-map/contraction certificate at radius `b+1` on the horizon
`picardHorizon ν K M`, `torusForcedPicard_exists` (313) gives the mild solution,
and `mild_to_classical` (334) turns it into the classical solution with all
three regularity clauses.

**Re-instantiations (all with the `PeriodicQuantitativeLocalInput'` hypothesis
removed), each the verbatim API field with the ball moved to `H³`:**

| theorem | field | remaining hypotheses |
|---|---|---|
| `restartH3` | `PeriodicContinuationAPI.restart` | **none** |
| `restartBeyondH3` | `…restartBeyond` | **none** |
| `extendsBeyondH3` | `…extendsBeyond` | `hHigh` only (U12's `higherOrderBound`, lanes 335/336), used at `m = 3` where lane 337 used `m = 1` |
| `lifespanInfiniteOfLocallyFiniteH3` | `…lifespanInfiniteOfLocallyFinite` | `hHigh` only |
| `exists_maximal_unconditional` | `PeriodicLocalTheoryAPI.exists_maximal` | **none** (this field carries no ball; lane 323's `PeriodicMaximalExistenceInput` is discharged by `periodicMaximalExistenceInput_unconditional`) |

## 2. Lean 里现在有什么 / What is in Lean

New module `formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean`
(≈ 540 lines, 24 top-level declarations including three explicitly named local
instances).

| section | content |
|---|---|
| 0 | `PeriodicQuantitativeLocalInputH3` |
| 1 | `forceSobolevENormT_eq_of_path` (the infimum is attained), `intervalIntegral_norm_le_of_forceENorm` (`L¹_t H^s` bound ⟹ `∫₀¹‖G‖ ≤ N.toReal`) |
| 2 | `torus_linearEvolution_norm_le`, **`torus_forcedLinear_bound_L1`** |
| 3 | `torusContractOf`, `torusPicardThreshold_pos`, **`picardHorizon`** + `_eq`/`_pos`/`_le_one` |
| 4 | **`exists_classical_on_picardHorizon`**, **`periodicQuantitativeLocalInputH3`** |
| 5 | `restartH3`, `exists_periodicLocalSolution_unconditional`, `periodicMaximalExistenceInput_unconditional`, `exists_maximal_unconditional`, `restartBeyondH3`, `extendsBeyondH3`, `lifespanInfiniteOfLocallyFiniteH3` |
| 6 | `nonzero_forced_witness_H3` + an `example` |

Reusable beyond this lane: `forceSobolevENormT_eq_of_path` and
`intervalIntegral_norm_le_of_forceENorm` (any consumer of an `L¹_t H^s` force
bound — T18 and T20 both will need them), `torus_forcedLinear_bound_L1`, and
`picardHorizon` as the canonical explicit horizon.

Files: the module; `research/T11/probes/existence_input_h3_closes.lean`;
`research/T11/axioms_existence_input_h3.lean`;
`research/T11/ATTEMPTS_EXISTENCE_INPUT_H3.md`; `research/T11/H1_GAP.md`; this
report; one line in `research/T11/T11_SPLIT.md` and one appended paragraph in
`research/T11/EXISTENCE_ROUTE.md`.

**One edit to an existing module, forced by a broken base.**  The lane base did
not compile: lane 334's `MildClassical.lean` was written against a pre-`2572e51b`
`MildMomentum.lean` in which `momentum_of_mildPressure` /
`projected_of_mildPressure` still took an explicit `(hF : PersistenceInput T F)`;
lane 327 later proved that argument and removed it, and the lead's merge of 334
into the 338 base combined the two incompatible files without a git conflict.
Three lines of `MildClassical.lean` are repaired (delete the `have hFI …` and
drop `hFI` from the two applications); no statement changes.  Details and the
exact error text in `ATTEMPTS_EXISTENCE_INPUT_H3.md` §0.  **This needs a
`logs/LESSONS.md` line from the lead** (the brief forbids editing that file from
a lane).

## 3. 缺口是什么 / What is not proved

1. **The `H¹` ball itself.**  `PeriodicQuantitativeLocalInput'` and the V1
   `restart`/`restartBeyond` fields with `periodicSobolevENorm 1` balls stay
   unproved.  Exact statements, the reason (subcritical Fujita–Kato local theory
   is absent from all three code bases), and the consumer checklist for U17 are
   in `research/T11/H1_GAP.md`.  Summary of §3 of that file: the only ball-using
   step inside T11 is `extendsBeyond`, and it is happy at `m = 3`; the one place
   to re-read is **T20**, whose own copy of `PeriodicContinuationAPI`
   (`research/T20/Spec.lean:402,437`) carries the `H¹` ball while its
   `eq:H1energy` route produces `H²` bounds.
2. **`hHigh` (U12's `higherOrderBound`)** is still a binder on `extendsBeyondH3`
   and `lifespanInfiniteOfLocallyFiniteH3`.  It is not a named input of this
   lane — it is an API field being closed by lanes 335/336.
3. **The horizon is not sharp.**  `picardHorizon` is the crude kernel-mass
   threshold; the manuscript's Appendix A rate in terms of `ν` and the norms is
   not extracted.
4. **Uniqueness of the classical solution** is untouched here (U5/U15).

No target statement was weakened; no `def … : Prop` packaging a goal was
introduced.  The single `def … : Prop` in the module,
`PeriodicQuantitativeLocalInputH3`, is **proved** three sections later.

## 4. 跑了什么命令、什么结果 / Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ExistenceInputH3
  → ✔ [10579/10579] Built NSFormalization.Section3.T11.ExistenceInputH3 (4.0s)
    Build completed successfully (10579 jobs).  0 errors.

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean
  → no output (0 errors, 0 warnings)

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/MildClassical.lean
  → no output (after the three-line repair; it did NOT compile before)

cd verification && lake env lean ../research/T11/probes/existence_input_h3_closes.lean
  → no output; Targets 1–6 (the amendment-2 input written out in full, the
    explicit-horizon form, and the verbatim restart / restartBeyond /
    extendsBeyond / lifespanInfiniteOfLocallyFinite / exists_maximal fields at
    the H³ ball) all close, the two non-vacuity examples close, and 3 embedded
    #guard_msgs axiom checks pass

cd verification && lake env lean ../research/T11/axioms_existence_input_h3.lean
  → no output; all 24 #guard_msgs pass, i.e. EVERY top-level declaration of the
    module (the three named local instances included) prints exactly
    [propext, Classical.choice, Quot.sound]

make check   (from the worktree root)
  → check_formalization_plan / check_contracts OK; test_contract_policy 13/13 OK;
    check_work_queue: "45 work items: ownership, contract registration and task
    cards consistent."

grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" on module, probe and
audit → no hits.
```
