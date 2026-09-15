# Review — lane 025, D01 unit L2 reverse direction (`Section4/D01/DatumToJets.lean`)

Reviewer pass over `erenup/025-D01-datum-to-jets` @ `5422a7a`, base `erenup/integration`. Proof lane, no
contract registration. Diff touches exactly two files: the module (514 lines) and
`research/D01/ATTEMPTS_DATUM_TO_JETS.md`.

## Verdict: **accept**

Builds clean and warning-free; all 29 theorems carry only the standard three axioms; every restated class is
*literally* `Iff.rfl`/`rfl`-equal to the contract it names; both consumer edges (A03 → R42, A05 → R43/R44)
close end to end from a real `Data.ClassicalSolutionR`, reproduced independently here. The four mathematical
points are sound, the gap list accurate. No fix needed.

## 1. Gates

| gate | command | result |
|---|---|---|
| module build | `cd verification && lake build NSFormalization.Section4.D01.DatumToJets` | **exit 0**, 9876 jobs; **zero** diagnostics mentioning `DatumToJets` (all 16 warnings pre-existing, in `RealSobolev`/`Paper3/*`) |
| repo gates | `make check` | **exit 0** — plan check, `check_contracts`, `test_contract_policy` (13 tests), `check_work_queue` (30 items) |
| changed-Lean | `build_changed_lean.py --base-ref erenup/integration` `--dry-run`, then without | dry-run lists `NSFormalization.Section4.D01.DatumToJets` ✓; real run **exit 0** |
| hygiene | grep `sorry`/`admit`/`axiom `/`native_decide`/`maxHeartbeats`/`unsafe`/`partial `/`@[simp]`/`decide` | **no hits** |
| declarations | — | **8 defs, 29 theorems**, 0 lemmas (brief said 6 defs; 8 = 3 restated contract classes + 5 working defs — nothing hidden) |
| axioms | `#print axioms` on all 29 theorems (scratch, deleted) | **29/29** exactly `[propext, Classical.choice, Quot.sound]` |

## 2. Definitional agreement (scratch in `verification/`'s env, deleted)

All elaborated with no error, `Iff.rfl`/`rfl` throughout — no `simp`, no `unfold`:
```lean
example (v) : D01.SmoothSquareIntegrableJets v ↔ V1.SmoothSquareIntegrableJets v         := Iff.rfl
example (v) : D01.SmoothSquareIntegrableJets v ↔ BoundedRep.SmoothSquareIntegrableJets v := Iff.rfl
example (m : ℕ) (v) : D01.SmoothJetsUpTo m v ↔ BoundedRep.SmoothJetsUpTo m v             := Iff.rfl
example (m : ℕ) (v) : D01.jetSobolevENorm m v = BoundedRep.jetSobolevENorm m v           := rfl
example (s : ℝ) (z) (A) : D01.IsSobolevDatum s z A ↔ Data.IsSobolevDatum s z A           := Iff.rfl
example (s : ℝ) (z) : D01.sobolevENorm s z = Data.sobolevENorm s z                       := rfl
-- MemHInfty is not restated; the module spells it out — so the unit-L2 iff and the
-- quantitative half are literally about the contracts' own objects:
example (a) : Data.MemHInfty a ↔ (ContDiff ℝ ∞ a ∧ ∀ m : ℕ, ∃ A, D01.IsSobolevDatum (m:ℝ) a A) := Iff.rfl
example (a) : Data.MemHInfty a ↔ V1.SmoothSquareIntegrableJets a := D01.memHInfty_iff_smoothSquareIntegrableJets
example (m : ℕ) (z) (hz : ContDiff ℝ ∞ z) : BoundedRep.jetSobolevENorm m z
    ≤ ENNReal.ofReal (D01.jetSobolevConst m) * Data.sobolevENorm (m:ℝ) z :=
  D01.jetSobolevENorm_le_sobolevENorm m hz
```

## 3. Consumer edges, end to end (same scratch; axiom-checked, all three standard)

`sobolev` is consumed with its `ContinuousOn` conjunct dropped, exactly as the hypothesis shape demands:
`sobolev_drop u := fun m => (u.sobolev m).imp fun _ h => h.2`.

```lean
theorem slice_jets2 (u : Data.ClassicalSolutionR ν a f T) (ht : t ∈ Ico (0:ℝ) T) :
    BoundedRep.SmoothJetsUpTo 2 (fun x => u.velocity (t,x)) :=
  smoothJetsUpTo_slice u.velocity_smooth (sobolev_drop u) ht 2

-- A03 → R42: eLpNormTop_le, then gcongr with jetSobolevENorm_le_sobolevENorm 2 (contDiff_slice …),
-- then ENNReal.ofReal_mul api.Cinfty_pos.le + mul_assoc — two links, ONE constant, on the
-- manuscript's own datum norm:
theorem eLpNormTop_slice_le_sobolevENorm (api : BoundedRep.BoundedRepresentativeAPI) (u …) (ht …) :
    eLpNorm (fun x => u.velocity (t,x)) ⊤ volume ≤ ENNReal.ofReal (api.Cinfty * jetSobolevConst 2)
      * Data.sobolevENorm (2:ℝ) (fun x => u.velocity (t,x))

-- A05 → R43/R44, both clauses, no massaging (hessian_slice is the same with
-- api.hessianLaplacianIdentity; initial_jets (ha : a ∈ Data.initialClassR) := memHInfty_jetClasses ha.1.1 ha.1.2):
theorem gradientLSix_slice (api : GradientL6API) (u …) (ht …) :
    eLpNorm (gradientTensor (fun x => u.velocity (t,x))) 6 volume
      ≤ ENNReal.ofReal api.Csix * eLpNorm (laplacian (fun x => u.velocity (t,x))) 2 volume :=
  api.gradientLSix _ (smoothSquareIntegrableJets_slice u.velocity_smooth (sobolev_drop u) ht)
```
The A03 chain lands a *single* `Data.sobolevENorm (2:ℝ)` on the right, and `exact h2` bridged
`Data.sobolevENorm 2` against `sobolevENorm ((2:ℕ):ℝ)` by defeq — even the numeral coercion agrees. This
reproduces §4 of the worker's notes independently; I hit the same `mul_le_mul_left'`-not-in-scope friction
recorded at its §6(7), corroborating rather than concerning.

## 4. Mathematical rulings
**(a) `(2π)^m` — correct, correctly labelled, not sharp.** In `jetDatumConst j m = (‖physicalJetLp j‖ + 1) *
frequencyUnit ^ (m:ℝ)` the only normalization-dependent factor arrives via `norm_loweredComponent_le` →
`norm_cyclesComponentOfAngular_le` → `Paper3.cyclesToAngular_symm_norm_le` (`AngularTameProduct.lean:20`,
`‖(cyclesToAngular s).symm h‖ ≤ frequencyUnit ^ |s| * ‖h‖`; `frequencyUnit = 2π`,
`FourierConvention.lean:15`), as `|s|` at `s = (m:ℝ)`, made `m` by `abs_of_nonneg (Nat.cast_nonneg m)`.
**`m` (datum order) not `j` (jet order) is right**: the angular→cycles transport happens *before*
`sobolevOrderLowering`, which is contractive (`SobolevOrderLowering.lean:39`) and adds nothing; the bound is
valid for every `j ≤ m` since `2π > 1`. *Sharpness only*: `Paper3.angularOrderLowering`
(`AngularTameProduct.lean`, below `:31`) would convert at order `j`, giving `(2π)^j`. Nothing is misstated —
the docstring says exactly "`m` = the datum order, not the jet order". `PiLp.norm_apply_le` and the
sup-vs-`PiLp 2` step are safe-way, constant one.

**(b) The infimum and the `⊤` branch — honest.** The nonempty branch goes through `ENNReal.mul_iInf` (side
goal by `ENNReal.ofReal_ne_top`) and `le_iInf`, so the bound holds against the *infimum over all data*, not
one chosen datum — what `A03/REVIEW_CONTRACT.md` §6(3) asks. No-datum branch: `IsEmpty` → `iInf_of_empty` →
`sobolevENorm = ⊤` (re-derived independently), then `ENNReal.mul_top` with `jetSobolevConst_pos`, so `⊤` is
**not** collapsed to `0` — which is what the `+ 1` in `jetDatumConst` buys, since `‖physicalJetLp j‖ ≠ 0` is
nowhere proved; the `⊤` convention is `Data.lean:189`'s own. **Worth naming** (the notes do, as gap 1): the
inequality is genuinely one-sided, and a smooth `z` with `L²` jets only up to order `m` may have no
order-`m` datum at all (lane 020's construction needs *all* orders), leaving the statement vacuous there.
Never vacuous on the consumer path: `ClassicalSolutionR.sobolev` gives a datum at every order.

**(c) `contDiff_slice` at `t = 0` — valid.** `#check @ContDiffOn.comp` at this pin: `ContDiffOn 𝕜 n g t →
ContDiffOn 𝕜 n f s → MapsTo f s t → ContDiffOn 𝕜 n (g ∘ f) s` — **no openness hypothesis on either set**;
`ContDiffOn` is a within-the-set notion and the lemma transports the `ContDiffWithinAt` Taylor data along
the inclusion. The *source* set is `univ : Set Space`, which **is** open, so `contDiffOn_univ` legitimately
upgrades to `ContDiff`; the non-open `Ico 0 T ×ˢ univ` appears only on the `g` side, where openness is not
required. Mathematically: `x ↦ (t,x)` is constant in time, so no time-direction derivative is ever extracted
and the one-sidedness at `t = 0` is never touched; the slab contains a full *spatial* neighbourhood of every
`(t,x)`, so the restricted Taylor series is a genuine spatial expansion on all of `ℝ³`. Confirmed by
instantiating the lemma at `t = 0` (`⟨le_rfl, hT⟩`). No boundary case needed.

**(d) "L2 closed in all three clauses of `RECONCILIATION.md:153`" — confirmed.** Line 153 is the **L2** row:
the iff `MemHInfty a ↔ ContDiff ℝ ∞ a ∧ ∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume`, *and* "either implies
`∃ A : SmoothL2Field Space, A.field = a`". Mapping: `⟹` = `memHInfty_jets`; `⟸` = lane 020's
`memHInfty_of_contDiff_memLp`; the pair = `memHInfty_iff_smoothSquareIntegrableJets` (shown in §2 to be
literally `Data.MemHInfty ↔ V1.SmoothSquareIntegrableJets`); third clause =
`exists_smoothL2Field_of_memHInfty`. The row's flagged "**Gap** in the `⟸` direction at non-compact data" is
genuinely closed: `exists_isSobolevDatum_of_contDiff_memLp` (`SmoothDatum.lean:290`) takes an arbitrary
smooth `z` with `L²` jets — no compact support, no decay — and produces a datum at every real `s` via
`⌈s⌉₊`. Claim accurate.

## 5. Reuse spot-check (12/12 real, at the cited lines) and gap accuracy

`FourierPhysicalJets.lean:14` (`CompactRep`), `:60` (`compactRep_directional`, the weak-equals-classical
heart), `:159` (`physicalJetLp`/`_ae`); `AngularTameProduct.lean:11` (`cyclesToAngular`), `:20`
(`_symm_norm_le`), `:31` (`angularRealization_eq_cycles`); `SobolevOrderLowering.lean:26`
(`sobolevOrderLowering`), `:39` (contractive), `:78` (realization-preserving); `SmoothDatum.lean:278`
(`smoothAngularDatum_isSobolevDatum`); `A05/SmoothJets.lean:94` (`SmoothL2.dir`);
`FourierConvention.lean:15` (`frequencyUnit = 2 * π`). Each is used as described; the module re-proves none
of the analysis — its added content is the three bookkeeping links plus the slice extraction.

**`ATTEMPTS_DATUM_TO_JETS.md` §7 — gaps accurate (5/5).** (1) **No lower bound** — no statement puts
`sobolevENorm` on the left. (2) **Integer orders only** —
`jetOfDatum`/`physicalJetLp` are `ℕ`-indexed; every datum⟹jet statement binds `{m j : ℕ}`. (3) **Pressure
gradient has no jets** — `ClassicalSolutionR.pressure_gradient` (`Data.lean:654`) is order-zero `MemLp` only
and the structure supplies no datum for `p`/`∇p`; only `contDiff_pressureGradient_slice` is offered. (4)
**Time regularity untouched** — every slice statement is at fixed `t`; the `ContinuousOn G (Ico 0 T)`
conjunct is discarded. (5) **A02 U1b(i)/(ii) untouched** — no `H² ↪ L^∞` embedding, no datum-carrier order
shift.

## 6. Issues, ranked (none blocking)
1. **Bindings uncommitted.** The §2/§3 identities live only in scratches (the worker's and mine, both
   deleted), so nothing in CI guards that `D01.SmoothJetsUpTo` stays `Iff.rfl`-equal to
   `BoundedRep.SmoothJetsUpTo` if either side drifts. `verification/Bindings/` is the right home; out of
   lane 025's scope, correctly declared by the notes (§7(7)). Highest-value follow-up.
2. **`(2π)^m` not sharp for `j < m`.** See (a). Cosmetic: the constant is free in the manuscript
   (`appendix-a-local-theory.tex:10`) and the exponent is honestly documented.
3. **Stale gate row + brief's count.** §8 of the notes records `--dry-run` → `Changed Lean modules: none`,
   true only while the module was untracked (now committed, the gate lists it correctly — verified); and
   the lane brief says 6 defs where the file has 8. Bookkeeping only.

**What remains, beyond this lane.** `sobolevENorm ≤ C · jetSobolevENorm` (the reverse inequality, i.e. norm
*equivalence*; needs `‖(iteratedBesselField m B).toLp‖ ≤ C_m ∑_k ‖B.jetLp k‖`, unstated in tree); **L1** (datum uniqueness — not needed
here: every statement is an inequality against `⨅`); pressure-gradient jets, blocked behind **L9**(c) and
U05; time regularity of the jet path (L4/L6); A02 U1b(i)/(ii). All named in §7 of the notes.
