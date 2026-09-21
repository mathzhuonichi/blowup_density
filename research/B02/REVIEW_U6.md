# Review — lane 068, B02 unit 6 (`lebesgueHomogeneousDatum`, and the honest `homogeneousDatumSub`)

Reviewer: independent opus reviewer, read/build only, no code changes.
Worktree: `.claude/worktrees/068-B02-unit-6`, commit `5035f03`
("[068-B02] Unit 6: homogeneous datum of an L1 ∩ L2 field …"), working tree clean
(the only file added by this review is this one).
Files under review: `formalization/NSFormalization/Section4/B02/LebesgueDatum.lean`
(451 lines), `research/B02/axioms_u6.lean`, `research/B02/ATTEMPTS_U6.md`.

## Verdict: **ACCEPT-WITH-NOTES**

Unit 6's spec field `lebesgueHomogeneousDatum` is discharged **in full — both clauses,
the verbatim spec type, the exact `SplitRange` range** — with a clean build, no
warnings from the file, and standard axioms only. The passage Schwartz → `L¹ ∩ L²`
(`homogeneousProfile_memLp`, `angularFourierDistribution_lp_apply`) is the genuine new
mathematics and it is correct and minimally hypothesised. The two composition
`example`s discharging lane 060's unit-6 and unit-7 hypotheses typecheck.

The lane's claimed spec defect in `homogeneousDatumSub` is **upheld, and is in fact
stronger than the lane claims: the spec field is *false*, not merely underivable**
(§4). The notes below are (1) a correction to the lane's written diagnosis, (2) a
downstream blocker the lane under-states — `spatialApproxHomogeneous_of` takes the
false field verbatim, so unit 9 cannot instantiate it until lane 060's statement is
weakened — and (3)–(4) cosmetics. Nothing in the delivered Lean is wrong; no note
blocks merge.

---

## 1. Commands and results

All from the worktree, after `bash scripts/lean-install.sh` + `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`, lake invoked only from `WT/verification`, one at a time.

| # | Command | Result |
|---|---------|--------|
| 1 | `bash scripts/lean-install.sh` | `== OK` |
| 2 | `cd verification && lake build NSFormalization.Section4.B02.LebesgueDatum` | `EXIT=0`, `Build completed successfully (8820 jobs).` `grep -n LebesgueDatum` over the full log → **no diagnostic mentions the module**; `grep -c error` → `0`. The only warnings in the log are pre-existing upstream ones (`Source/RealSobolev.lean`, `Paper3/RealPositiveDensity.lean`, `Paper3/RealVectorPositiveDensity.lean`). |
| 3 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/B02/LebesgueDatum.lean` | **no output at all**, `EXIT=0` (3.8 s wall) — zero warnings, zero infos from the file |
| 4 | `cd verification && lake env lean ../research/B02/axioms_u6.lean` | `EXIT=0`; both spec-typed `example`s elaborate; the five `#print axioms` → each exactly `[propext, Classical.choice, Quot.sound]` |
| 5 | `grep -nE "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" formalization/…/LebesgueDatum.lean` | **no matches** (`rc=1`) |
| 6 | same grep on `research/B02/axioms_u6.lean` | 6 hits, all legitimate: `:11` inside the `/-! … -/` header, `:48-52` the required `#print axioms` commands. No `axiom` declaration, no `set_option`, no `maxHeartbeats`. |
| 7 | `make check` | `EXIT=0` — plan check, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (`30 work items: … consistent`) |
| 8 | reviewer probe `/tmp/b068_probe.lean` (§4 below: the reduction as an **iff**, `zero_datum`, `collapse`, `spec_field_false_of_wild_pair`) | `EXIT=0` — all four statements elaborate |
| 9 | reviewer probe `/tmp/b068_probe2.lean` (§5: the two integrability side conditions at lane 060's single call site) | `EXIT=0` — both proved, ~15 lines each |
| 10 | extra axiom check on `isHomogeneousSliceDatum_sub_of_integrable`, `D01.Homogeneous.isHomogeneousSliceDatum_sub`, `D01.Homogeneous.integrable_schwartz_mul_component`, `lebesgueDatum`, `lebesgueVectorDatum`, `realSymmetry_lebesgueDatum`, `angularFourier_continuous`, `norm_angularFourier_le`, `enorm_lebesgueDatum_sq`, `lebesgueDatum_weight_ae`, `mem_realSubspace_lebesgueDatum`, `lowHighSplit` | all `[propext, Classical.choice, Quot.sound]`, `EXIT=0` |
| 11 | mutation test of ATTEMPTS §5 snag (remove the `dsimp only` before the `rw` in `homogeneousProfile_memLp`) | `rewrite failed … (fun a => …) ξ ≤ (fun a => …) ξ` — the recorded beta-redex, exactly as claimed |

## 2. Spec conformance — `lebesgueHomogeneousDatum` (`Spec.lean:454-458`)

* `research/B02/axioms_u6.lean:22-30` states the field against the **frozen**
  `Contracts.V1.Data` predicates and closes it with
  `NSFormalization.Section4.B02.lebesgueHomogeneousDatum hs.1 hs.2 k hk1 hk2`.
  Diffed token-for-token against `Spec.lean:454-458`: identical up to the inlining
  of `SplitRange s` as `(-3 / 2 < s ∧ s ≤ 0)`, which is `SplitRange`'s body verbatim
  (`Spec.lean:237`, `Cutoff.lean:269`: `def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0`).
  The range is therefore **exactly** `−3/2 < s ≤ 0`: `hs.1 : -3/2 < s` feeds the
  low-frequency half (`lowFrequencyIntegrable`), `hs.2 : s ≤ 0` the high-frequency
  half (`|ξ|^{2s} ≤ 1`). Neither is decorative and neither is widened.
* **Both clauses** are present and both are substantive. The norm clause quantifies
  over *every* datum `G` and is proved via `D01.Homogeneous.isHomogeneousSliceDatum_unique`
  (any datum equals the constructed `lebesgueVectorDatum`) plus
  `enorm_lebesgueVectorDatum` — not by an infimum dodge, and not vacuously: the
  existence clause supplies the witness that makes the ∀-clause non-empty.
* `homogeneousFourierENorm s k` in the theorem is the `Data.lean:410` literal Fourier
  integral (the `Contracts`-typed `example` in `axioms_u6.lean` accepts the B02
  theorem directly, so the B02/D01 restatements are definitionally the frozen ones).
* Composition `example`s, `LebesgueDatum.lean:433-450`: the unit-6 one is
  `hLebesgueDatum` of `Cutoff.lean:299-303` token-for-token; the unit-7 one is
  `hLowHighSplit` of `Cutoff.lean:307-311` token-for-token, closed by lane 059's
  merged `LowHigh.lean:199` `lowHighSplit` (`fun s hs k hk1 hk2 => lowHighSplit s hs.1 hs.2 k hk1 hk2`).
  Both elaborate (row 2/3 of §1: the module compiles with zero diagnostics).

## 3. Mathematical spot-checks of the new content

Read in full; the three places where a wrong hypothesis would hide:

* `homogeneousProfile_memLp` — the split is at angular radius 1 and both halves use
  their hypothesis honestly: low uses `norm_angularFourier_le` (an `L¹→L∞` bound, so
  `MemLp k 1` is needed) times `lowFrequencyIntegrable s hs` (needs `-3/2 < s`); high
  uses `Real.rpow_le_one_of_one_le_of_nonpos` (needs `s ≤ 0`) times lane 059's
  `angular_plancherel` (needs `L¹ ∩ L²`). No compact support, no Schwartz hypothesis
  anywhere — which is the whole point of the unit.
* `angularFourierDistribution_lp_apply` — the `(2π)`-dilation bookkeeping is the risky
  step; the amplitude `frequencyUnit^{3/2}` from `angularDistributionDilation_apply`
  and the Jacobian `|(c³)⁻¹|` from `Measure.integral_comp_smul` cancel to
  `frequencyUnit^{-3/2}`, which is the convention fixed at `01-introduction.tex:91`.
  Correct.
* `isHomogeneousSliceDatum_lebesgue` — the `IsSliceDistribution` clause is discharged
  with the *genuine* integral (`Lp.toTemperedDistribution_apply` + `coeFn_toLp`), not
  by totalization, and the `IsHomogeneousDatum` integrability clause is proved
  (`Integrable.mul_bdd`), not assumed. So the new witness is an honest inhabitant of
  `Data.lean:367`.

## 4. Adjudication of the claimed spec defect (`homogeneousDatumSub`, `Spec.lean:470-472`)

**Verdict on the claim: upheld — and the field is FALSE, not merely unproved.**
The lane's obstruction analysis is right; its explanation of *why it cannot be
repaired* is wrong in a way that matters for the fix.

### (a) The reduction reproduced — and it is an `iff`

Probe (`/tmp/b068_probe.lean`, elaborates, `EXIT=0`):

```lean
example (z w : SpatialField) (U V : VectorDistribution)
    (hU : IsSliceDistribution z U) (hV : IsSliceDistribution w V) :
    IsSliceDistribution (z - w) (U - V) ↔
      ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        (∫ x, ψ x * ((z x i : ℝ) : ℂ)) - (∫ x, ψ x * ((w x i : ℝ) : ℂ))
          = ∫ x, ψ x * (((z x i - w x i : ℝ)) : ℂ)
```

Both directions are `rfl`-level unfolding plus `hU`, `hV`. So the remaining obligation
is *exactly* `MeasureTheory.integral_sub`, as `ATTEMPTS_U6.md` §3 says — and being an
`iff`, there is no alternative route once the witness is fixed. The witness *is* fixed:
`IsHomogeneousVectorDatum s U'' (Z−W)` plus `Paper3.angularFourierDistribution_injective`
(`AngularSobolevClass.lean:22`) forces `U'' = U − V`. The lane's description is accurate
in every particular.

### (b) False, not merely unproved

`Data.lean:298` `IsSliceDistribution` uses the **totalized** Bochner integral (its own
docstring says so). That cuts the other way from what `ATTEMPTS_U6.md` §3 assumes: a
field so wild that `ψ · z_i` is *never* integrable satisfies `IsSliceDistribution z 0`
**vacuously**, and then carries the *zero* homogeneous datum at every order. Machine-checked:

```lean
theorem zero_datum (s : ℝ) (z : SpatialField)
    (hz : ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ), (∫ x, ψ x * ((z x i : ℝ) : ℂ)) = 0) :
    IsHomogeneousSliceDatum s z 0            -- proved, no side conditions

theorem collapse (H : <the verbatim spec field>) (z w : SpatialField)
    (hz : ∀ i ψ, (∫ x, ψ x * ((z x i : ℝ) : ℂ)) = 0)
    (hw : ∀ i ψ, (∫ x, ψ x * ((w x i : ℝ) : ℂ)) = 0) :
    ∀ i ψ, (∫ x, ψ x * (((z x i - w x i : ℝ)) : ℂ)) = 0   -- proved from H
```

(`collapse` instantiates `H` at `s = -1`, `Z = W = 0`, uses `0 - 0 = 0`, and kills the
returned witness with `angularFourierDistribution_injective`.) A counterexample to the
spec field is therefore any pair `z`, `w` of fields whose own pairings all totalize to
`0` while their difference pairs non-trivially — and such a pair exists classically:

> Let `{q_n}` enumerate `ℚ³`, `r_n = 2^{-n}`, and
> `f = Σ_n 2^{-n} |x−q_n|^{-3} · 1_{0<|x−q_n|<r_n}` (set to `0` on the null set where the
> sum diverges). `f` is measurable and a.e. finite (Borel–Cantelli: `Σ vol B(q_n,r_n) < ∞`,
> so a.e. `x` meets only finitely many balls), yet `∫_B f = ∞` for **every** ball `B`
> (each ball contains some `q_n` with `B(q_n,r_n) ⊆ B`, and `∫_{|y|<r} |y|^{-3} dy = ∞`
> logarithmically in `ℝ³`). Hence for every Schwartz `ψ ≢ 0` — pick a ball where
> `|ψ| ≥ c > 0` — `ψ·f` is not integrable, so the totalized pairing is `0`; and `ψ ≡ 0`
> gives `0` too. Take `c` a nonzero real Schwartz function, `z := (f,0,0)`,
> `w := (f − c, 0, 0)` (`f − c` is just as non-locally-integrable). Both satisfy the
> datum hypotheses with `U = V = 0`, `Z = W = 0`; but `(z−w)₀ = c` and `∫ c·c > 0`.

The final step is one line from `collapse` (`spec_field_false_of_wild_pair`, also
elaborated). So `Spec.lean:470-472` is **not** a true statement awaiting a
"temperate-growth / local-integrability development": no such development can prove it,
because it is false. `ATTEMPTS_U6.md` §3's sentence *"Physical integrability is true
whenever a genuine distribution `U` exists (a locally-integrable representative of a
tempered distribution has polynomially growing local `L¹` norms…)"* is the error: the
existence of `U` does **not** force `z` to have a locally integrable representative,
precisely because `IsSliceDistribution` totalizes.

**Fix (spec-level, outside unit 6's scope but must be scheduled):** amend
`Spec.lean:470-472` to the integrability-carrying form the lane actually proved
(`isHomogeneousSliceDatum_sub_of_integrable`, = `D01.Homogeneous.isHomogeneousSliceDatum_sub`),
or else strengthen `Data.lean:298` `IsSliceDistribution` to require
`Integrable (ψ · z_i)` (equivalently, restrict `SpatialField`s to locally integrable
ones) — the latter is the deeper repair and touches the frozen contract, so the former
is the one to take.

### (c) Does `isHomogeneousSliceDatum_sub` + `integrable_schwartz_mul_component` cover unit 9?

Mathematically yes; **as currently wired, no** — and the lane's "so the assembly is not
blocked" is too quick.

* `Cutoff.lean:304-306` (`spatialApproxHomogeneous_of`, lane 060, **already merged**)
  takes `hDatumSub` **verbatim in the spec's unhypothesised form**. A hypothesis that is
  false can never be supplied, so `spatialApproxHomogeneous_of` is, as it stands,
  uninstantiable: unit 9's diagonal *is* blocked until that statement changes.
* It is one call, `Cutoff.lean:398-399`, with concrete arguments
  `z = schwartzVector ψ` and `w = fun x => (1 − cutoff R x) • schwartzVector ψ x`. Both
  integrability side conditions are provable there; I proved both
  (`/tmp/b068_probe2.lean`, `EXIT=0`), each in ~15 lines via `χ.integrable.mul_bdd`
  with `c := SchwartzMap.seminorm ℝ 0 0 (ψ i)`:

  ```lean
  theorem integrable_schwartzVector (ψ : Fin 3 → SchwartzMap Space ℝ) (i) (χ) :
      Integrable (fun x : Space => χ x * ((schwartzVector ψ x i : ℝ) : ℂ)) volume
  theorem integrable_cutoffCompl_schwartzVector (ψ) (R : ℝ) (i) (χ) :
      Integrable (fun x : Space =>
        χ x * (((((1 - cutoff R x) • schwartzVector ψ x) i : ℝ)) : ℂ)) volume
  ```

* So the **fix is local and small**: weaken `hDatumSub` in `spatialApproxHomogeneous_of`
  to the two-side-condition form and discharge the side conditions at that one call
  site. That is an edit to lane 060's merged file, i.e. a scheduled follow-up, not a
  unit-6 defect — but it must be scheduled, and the ATTEMPTS record should say so
  instead of "the assembly is not blocked".
* A precision about `D01.Homogeneous.integrable_schwartz_mul_component`: it applies only
  to a field *given* by a `ℂ`-valued Schwartz family (`ψ i x = (z x i : ℂ)`). It covers
  the first call-site field only after producing `ℂ`-valued Schwartz components of
  `schwartzVector ψ` (the tree's only `ℝ→ℂ` Schwartz route,
  `CompactSchwartz.ofCompactSupport`, needs compact support, which `ψ` has not), and it
  does **not** apply to the second field `(1 − χ_R) • schwartzVector ψ`, which is
  bounded×Schwartz rather than a Schwartz family by hypothesis. Both are still easy —
  `Integrable.mul_bdd` directly, as above — so the conclusion stands, but the ATTEMPTS
  sentence "`integrable_schwartz_mul_component` supplies the side conditions" is
  approximately, not literally, true.

## 5. Numbered findings

| # | Severity | Declaration / file | What is wrong | Fix |
|---|----------|--------------------|---------------|-----|
| 1 | **Medium (record)** | `research/B02/ATTEMPTS_U6.md` §3, and the same sentence in the module docstring of `LebesgueDatum.lean` (§"The companion field `homogeneousDatumSub`") | The defect is mis-diagnosed as "true but not derivable, pending a temperate-growth development". Under `Data.lean:298`'s totalizing convention the field is **false** (§4b, machine-checked collapse + explicit classical counterexample). The claim "Physical integrability *is* true whenever a genuine distribution `U` exists" is wrong: `U = 0` serves for any field that never pairs integrably. | Replace the paragraph: state that the field is false as written, give the wild-field counterexample, and record the spec amendment required at `Spec.lean:470-472` (adopt the integrability-carrying form). No Lean change. |
| 2 | **Medium (downstream, not this lane's code)** | `Cutoff.lean:304-306` `spatialApproxHomogeneous_of`, hypothesis `hDatumSub` | It takes the (false) spec field verbatim, so the theorem can never be instantiated and unit 9's diagonal is blocked as wired — contrary to ATTEMPTS §3's "so the assembly is not blocked". | Follow-up task on lane 060's file: weaken `hDatumSub` to the two-integrability-hypothesis form and discharge the side conditions at the single call site `Cutoff.lean:398-399` (both proved by this review, §4c). |
| 3 | **Low** | ATTEMPTS §3 last sentence | `integrable_schwartz_mul_component` literally covers neither call-site field (needs a `ℂ`-Schwartz family; the second field is bounded×Schwartz). | One sentence: the side conditions come from `Integrable.mul_bdd`, of which `integrable_schwartz_mul_component` is the special case. |
| 4 | **Low (cosmetic)** | `research/B02/axioms_u6.lean` | (i) The `#print axioms` list omits `isHomogeneousSliceDatum_sub_of_integrable`, the second theorem the file's `example`s rely on (I checked it separately: clean). (ii) The file inlines `-3/2 < s ∧ s ≤ 0` where `axioms_u7.lean:33` / `axioms_u8.lean:67` restate `def SplitRange`. | Add the one `#print axioms` line; optionally restate `SplitRange` for consistency with the sibling conformance files. |

No finding requires a change to `LebesgueDatum.lean`'s mathematics.

## 6. Honesty spot-checks of `ATTEMPTS_U6.md`

* §5 "`lintegral_mono` leaves beta-redexes `(fun a => …) ξ`; a `dsimp only` before the
  `rw` is needed" — **confirmed by mutation**: deleting that `dsimp only` from
  `homogeneousProfile_memLp` gives
  `Tactic 'rewrite' failed: Did not find an occurrence of the pattern … in the target expression
  (fun a => ENNReal.ofReal (‖a‖ ^ (2 * s) * ‖angularFourier g a‖ ^ 2)) ξ ≤ (fun a => …) ξ`.
* §5 "`Measure.integral_comp_smul` is under `MeasureTheory.Measure`, first explicit arg
  is the measure" — **confirmed**:
  `Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:92`, inside
  `namespace MeasureTheory` / `namespace Measure`, with `variable … (μ : Measure E)`
  explicit at line 85 and signature `integral_comp_smul (f : E → F) (R : ℝ)`.
* §6 "Commands run" — reproduced verbatim, same results (rows 2 and 4 of §1),
  including the "no warnings from the module" claim (row 3: the file produces *no*
  output at all under `lake env lean`).

Both sampled snags are accurate and were evidently really hit. The `ATTEMPTS` file is
honest about the gap it did not close; the one correction is finding 1, which makes the
gap *worse*, not better — i.e. the lane under-claimed, it did not over-claim.
