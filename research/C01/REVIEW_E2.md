# REVIEW — lane 136-C01-e2-vocabulary (row E2, carrier-B vocabulary bridge)

Reviewer run 2026-09-13, worktree `.claude/worktrees/136-C01-e2-vocabulary`
(branch `erenup/136-C01-e2-vocabulary`, one commit `de66e89` on top of
`daab941` = merge-base with `origin/erenup/integration`).  Probes in `/tmp/rev136/`
(volatile — every load-bearing text is pasted below, per `logs/LESSONS.md`).

## Verdict: **ACCEPT-WITH-NOTES**

Nothing to fix before merge.  All seven declarations compile with the standard
three axioms, the "definitionally the spec's `l2Sq`/`gradientSq`/`pairing`" claim is
**verified in Lean** (findings 2–3), the sign/shape against E0 and the spec's
asserted derivative is right (finding 4), and both recorded errors reproduce
verbatim (finding 10).  Notes 6–9 are follow-ups, not blockers.

---

## 1. Compiles / axioms / hygiene — PASS

```
$ . scripts/lean-env.sh; cd verification
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.Vocabulary
Build completed successfully (4573 jobs).                       # EXIT 0

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/C01/Vocabulary.lean
                                                                # EXIT 0, 0 bytes of output
$ LEAN_NUM_THREADS=6 lake env lean ../research/C01/axioms_e2.lean               # EXIT 0
'NSFormalization.Section4.C01.field_normSq_integrable'   depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.l2Sq_eq_inner'             depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.norm_toLp_sq_eq_l2Sq'      depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.gradientSq_eq_sum'         depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.sqrt_dirSum_sq'            depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.pairing_eq_inner'          depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.C01.energyIdentity_of_carrierB' depends on axioms: [propext, Classical.choice, Quot.sound]

$ make check                                                    # EXIT 0
python3 experiments/test_contract_policy.py … Ran 13 tests … OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Elaboration is **silent** — no warnings, no deprecations, no linter hits.
Hygiene grep over the two new Lean files:

```
$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/C01/Vocabulary.lean research/C01/axioms_e2.lean
research/C01/axioms_e2.lean:4:  … audit for lane 136-C01-e2 …          (docstring)
research/C01/axioms_e2.lean:15-21: #print axioms <7 names>             (the audit itself)
```
Zero hits in `Vocabulary.lean`; the audit file's hits are the `#print axioms` lines.
`git status --short` clean.

## 2. Statement fidelity — the "definitionally the spec's" claim, verified in Lean — PASS

Probe `/tmp/rev136/fidelity.lean`, elaborated in the **`verification`** context with
`research/C01/Spec.lean`'s own imports (`Contracts.V1.Data`, `Contracts.V1.GradientL6`)
and opens (`NavierStokes.ProblemStatement`, `BlowupDensity.Contracts.V1`,
`BlowupDensity.Contracts.V1.Data`), with the four spec `def`s copied **verbatim** from
`Spec.lean:166,172,185,196`.  Result:

| spec quantity | bridge target | closed by |
|---|---|---|
| `l2Sq A.field` (E2a) | `∫ x, ‖A.field x‖ ^ 2` | **`rfl`** ✅ |
| `l2Sq (slice u t)` with `A.field = slice u t` | `∫ x, ‖A.field x‖ ^ 2` | `rw [h]` then `rfl` (`rw` alone leaves `l2Sq (slice u t) = ∫ x, ‖slice u t x‖^2`, since `l2Sq` is a plain `def`) ✅ |
| `pairing A.field B.field` (E2c) | `∫ x, ⟪A.field x, B.field x⟫` | **`rfl`** ✅ |
| `gradientSq A.field` (E2b) | `∫ x, ∑ i, ‖fderiv ℝ A.field x (axis i)‖ ^ 2` | **NOT `rfl`** — exactly as the lane says |

The recorded `rfl` failure, verbatim:

```
/tmp/rev136/fidelity.lean:41:90: error: Type mismatch
  rfl
has type
  ?m.59 = ?m.59
but is expected to have type
  gradientSq A.field = ∫ (x : Space), ∑ i, ‖(fderiv ℝ A.field x) (EulerOrdinarySobolev.axis i)‖ ^ 2
```

**The missing E2b tail is the claimed one-liner.**  `/tmp/rev136/tail.lean`, EXIT 0,
standard three axioms — `PiLp.norm_sq_eq_of_L2` alone suffices: `coordinateVector = axis`,
`spatialDerivative (lift z) 0 x = fderiv ℝ z x` and `gradientTensor = spatialGradient ∘ lift`
are all absorbed by defeq, so no `rw` for them is needed:

```lean
theorem gradientSq_eq_fderivSum (z : SpatialField) :
    gradientSq z = ∫ x : Space, ∑ i : Fin 3, ‖fderiv ℝ z x (axis i)‖ ^ 2 :=
  integral_congr_ae (Filter.Eventually.of_forall fun _ => PiLp.norm_sq_eq_of_L2 _ _)
```

## 3. The whole chain in spec vocabulary — PASS (seed for the Bindings lane)

`/tmp/rev136/bindseed.lean`, EXIT 0, all standard three axioms.  With the four spec
defs copied verbatim and `import NSFormalization.Section4.C01.Vocabulary`, these all
typecheck and close:

```lean
theorem spec_l2Sq_eq_inner    (A : SmoothL2Field Space) : l2Sq A.field = ⟪A.toLp, A.toLp⟫ := l2Sq_eq_inner A
theorem spec_norm_toLp_sq     (A : SmoothL2Field Space) : ‖A.toLp‖ ^ 2 = l2Sq A.field   := norm_toLp_sq_eq_l2Sq A
theorem spec_pairing_eq_inner (A B : SmoothL2Field Space) : pairing A.field B.field = ⟪A.toLp, B.toLp⟫ := pairing_eq_inner A B

theorem spec_gradientSq_eq_sum (A : SmoothL2Field Space) :
    ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 = gradientSq A.field :=
  (gradientSq_eq_sum A).trans (gradientSq_eq_fderivSum A.field).symm

/-- the spec's asserted derivative value, in the spec's own names -/
theorem spec_energyIdentity_value {ν d : ℝ} (u f Gt P : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p) (hgrad : ∀ x, P.field x = gradient p x)
    (hdiv : ∀ x, EulerSmoothLimit.divergence u.field x = 0)
    (hd : d = 2 * ⟪u.toLp, Gt.toLp⟫)
    (hmom : Gt.toLp = ν • (OrdinaryViscousStability.laplacianField u).toLp
              - (advectionField u u).toLp - P.toLp + f.toLp) :
    d = -2 * ν * gradientSq u.field + 2 * pairing u.field f.field := by
  rw [gradientSq_eq_fderivSum u.field]
  exact energyIdentity_of_carrierB u f Gt P p hp hgrad hdiv hd hmom
```
i.e. the lane's raw-integral conclusion **is** the spec's
`-2 * ν * gradientSq (slice w.velocity t) + 2 * pairing (slice w.velocity t) (slice f t)`
(`Spec.lean:348-350`) once the carrier's `.field` is the slice.  The design claim
("the final `energyIdentity` assembly must live in `Bindings`") is confirmed: the
statement above cannot be written inside `formalization/`, only the pieces can.

## 4. Sign / shape against E0 and the three cancellations — PASS

* `inner_energy_identity_deriv` (`Section4/C01/EnergyIdentity.lean:104`, lane 131)
  concludes `d = -2 * ν * grad ^ 2 + 2 * ⟪G, F⟫` from
  `hd : d = 2⟪G,Gt⟫`, `hmom : Gt = ν•L - N - P + F`, `hlap : ⟪G,L⟫ = -grad^2`,
  `hpr : ⟪G,P⟫ = 0`, `hnl : ⟪G,N⟫ = 0`.  The lane instantiates `G = u.toLp`,
  `grad = Real.sqrt (∑ᵢ ‖(u.directionalField (axis i)).toLp‖²)`; `sqrt_dirSum_sq`
  closes `grad^2 = ∑ᵢ …`.  ✅
* `hlap`: `OrdinaryViscousStability.laplacian_pairing W : ⟪W.toLp,(laplacianField W).toLp⟫_ℝ
  = -∑ i : Fin 3, ‖(W.directionalField (axis i)).toLp‖ ^ 2` — the lane's LHS of
  `gradientSq_eq_sum` is **verbatim** that sum, so the "exact shape `laplacian_pairing`
  outputs" claim is right.  Sign: dissipation enters negative, `-2ν·‖∇u‖²`. ✅
* `hnl`: `advection_inner_zero A B (hdiv on A) : ⟪(advectionField A B).toLp, B.toLp⟫ = 0`,
  used at `A = B = u` after `real_inner_comm`. ✅
* `hpr`: `gradient_pairing_zero A U p hp hgrad hdiv : ⟪A.toLp, U.toLp⟫ = 0` with
  `A = P = ∇p`, `U = u`, used after `real_inner_comm`. ✅
* `hmom`'s signs match `ClassicalSolutionR.momentum` rearranged,
  `D01.temporalDerivative_slice_eq` (`D01/Pressure.lean:196`):
  `∂ₜu = f − (u·∇)u + ν•Δu − ∇p`. ✅

**Non-vacuity — stronger than the lane's audit.**  `/tmp/rev136/nonvac.lean`, EXIT 0,
standard three axioms.  A **nonzero** carrier element exists and all four bridges
instantiate on it; the constructor is ~6 lines, contrary to `ATTEMPTS_E2.md`'s
"not cheap" (that referred to discharging `hmom`, which is indeed separate work —
but the bridges themselves needed only this):

```lean
def bumpField (φ : Space → Space) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    SmoothL2Field Space where
  field := φ
  smooth := hs
  integrable n :=
    (hs.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport (hc.iteratedFDeriv n)

def b : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩
def w : Space → Space := fun x => b x • axis 0
def W : SmoothL2Field Space := bumpField w (b.contDiff.smul contDiff_const) b.hasCompactSupport.smul_right
theorem W_ne_zero : W.field ≠ 0 := …    -- via b.one_of_mem_closedBall + axis_norm
```
and then, printed by the probe,
```
l2Sq_eq_inner      W : ∫ (x : Space), ‖W.field x‖ ^ 2 = ⟪W.toLp, W.toLp⟫
gradientSq_eq_sum  W : ∑ i, ‖(W.directionalField (axis i)).toLp‖ ^ 2 = ∫ (x : Space), ∑ i, ‖(fderiv ℝ W.field x) (axis i)‖ ^ 2
pairing_eq_inner W W : ∫ (x : Space), ⟪W.field x, W.field x⟫ = ⟪W.toLp, W.toLp⟫
norm_toLp_sq_eq_l2Sq W : ‖W.toLp‖ ^ 2 = ∫ (x : Space), ‖W.field x‖ ^ 2
```
`bumpField` is worth lifting into the tree (it is the generic "C_c^∞ ⊂ carrier B"
gadget; see note 9).

## 5. Consistency — PASS

* Imports are the four the proofs actually use (`Section4.C01.EnergyIdentity`,
  `Source.OrdinaryViscousStability`, `Euler.OrdinaryTransportCancellation`,
  `Euler.OrdinaryPressureCancellation`); `formalization → vendor` is the allowed
  direction; no `Contracts.*` import (which is what forced the raw-integral spelling).
* **No restated definitions.**  `grep -nE '^\s*(noncomputable )?(def|abbrev|structure|instance|notation) '`
  over `Vocabulary.lean` returns nothing — the module is seven theorems.  `field_inner`,
  `laplacianField`, `advectionField`, `axis`, `directionalField` are all used from upstream.
* Nothing imports `Vocabulary.lean` yet except its own audit file (new leaf), so no
  rebase/搬家 hazard.

### 6. [MINOR] `field_normSq_integrable` has a shorter, more standard proof
No in-tree duplicate exists (`EulerOrdinarySobolev` has `field_inner_integrable`;
`Euler/MeanLocalL2Energy.lean:16 integrable_norm_sq_L2` is about raw `L2` elements,
not `SmoothL2Field`).  But the Mathlib route is one line and avoids the
`real_inner_self_eq_norm_sq` congr — verified EXIT 0 in `/tmp/rev136/dup.lean`:
```lean
example (A : SmoothL2Field Space) : Integrable (fun x => ‖A.field x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm A.smooth.continuous.aestronglyMeasurable).mp A.memLp
```
Cosmetic; not worth a re-push on its own.

### 7. [INFO] `sqrt_dirSum_sq` is a named specialization of `Real.sq_sqrt`
Confirmed (`/tmp/rev136/dup.lean`, EXIT 0): the proof is exactly
`Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)`.  Keeping it named is fine —
it is the finding-4 adapter and it is what makes `energyIdentity_of_carrierB` readable —
but the ledger should not count it as mathematical content.

### 8. [MINOR] `energyIdentity_of_carrierB`'s `hp` is stronger than needed
`hp : ContDiff ℝ ∞ p` can be weakened to `Differentiable ℝ p`, because
`EulerOrdinarySobolev.potential_smooth P p hp hgrad` recovers smoothness from
`P : SmoothL2Field` + `hgrad`.  Verified under `set_option autoImplicit false`
(`/tmp/rev136/weaken.lean`, EXIT 0, standard three axioms):
```lean
theorem energyIdentity_of_carrierB' … (hp : Differentiable ℝ p) … :=
  energyIdentity_of_carrierB u f Gt P p (potential_smooth P p hp hgrad) hgrad hdiv hd hmom
```
Harmless for the C01 consumer (`ClassicalSolutionR.pressure_smooth` gives `ContDiff ∞`
anyway).  Record only.

### 9. [INFO] Module home — 6 of 7 declarations are Source-level (MAINT note)
`field_normSq_integrable`, `l2Sq_eq_inner`, `norm_toLp_sq_eq_l2Sq`, `gradientSq_eq_sum`,
`sqrt_dirSum_sq`, `pairing_eq_inner` mention no Section-4 object at all — they are facts
about `EulerLpTranslation.SmoothL2Field` and belong next to
`Source/OrdinaryViscousStability.lean`.  Only `energyIdentity_of_carrierB` is C01.
Leaving it in `Section4/C01/` is right for now (E0 lives there too, and moving modules
has burned us before — `logs/LESSONS.md` 123); queue a MAINT lane if a second consumer
outside C01 appears.  The `bumpField` gadget of finding 4 belongs in the same Source
module when it lands.

## 10. Honesty of `ATTEMPTS_E2.md` — PASS, both errors reproduce verbatim

(a) the `⟫_ℝ` notation, `/tmp/rev136/repro_notation.lean` (same opens as `Vocabulary.lean`,
i.e. `RealInnerProductSpace` but **not** `InnerProductSpace`):
```
/tmp/rev136/repro_notation.lean:8:45: error: unexpected identifier; expected ':=', 'where' or '|'
```
— character-for-character the message recorded at `ATTEMPTS_E2.md` §"Errors hit", item 1.

(b) the deprecation, `/tmp/rev136/repro_deprecated.lean` (compiles, EXIT 0, warning only):
```
/tmp/rev136/repro_deprecated.lean:11:2: warning: `MeasureTheory.integral_finset_sum` has been deprecated: Use `MeasureTheory.integral_finsetSum` instead
```
— verbatim item 2.  Item 3 (`unknown namespace 'NavierStokes.ProblemStatement'` in the
audit file) was not re-run: the audit file as committed compiles, and the claim is about a
draft state.  The `rfl`-vs-analysis table in ATTEMPTS is accurate, including "no bridge is
fully `rfl`" **on the carrier-B side** — note that on the *spec* side E2a and E2c **are**
`rfl` (finding 2), which is the complementary half and is worth adding to the record.

The `ENERGY_SPLIT.md` row-E2 rewrite matches what was delivered (checked against
`git diff daab941 HEAD -- research/C01/ENERGY_SPLIT.md`); the dependency-direction caveat
and the "one-line verification-side binding" claim are both now verified, not asserted.

---

## For the lead: the exact contents of the next C01 lane

**It is not a pure Bindings lane.**  `Bindings/EnergyAbsorptionV2.lean` can only hold the
last ~30 lines; three side facts on carrier B are still owed and need **one more
`formalization/` module** (suggest `Section4/C01/EnergyAssembly.lean`).  Also note
`verification/contracts.json`'s `C01.energy_absorption_partial` scope string explicitly
excludes `energyIdentity`/`energyDifferentialBound`/`l2Bound`, so the target is a **new
V2 contract** (`Contracts/V1/EnergyAbsorptionV2.lean` + `Bindings/EnergyAbsorptionV2.lean`
+ `Tests/`), not an edit of the frozen V1.

### Owed on carrier B (all inputs exist; no open blocker)

| # | fact | inputs, all present | size |
|---|---|---|---|
| **Ep** | package `∇p(t,·)` as `SmoothL2Field Space` and feed `gradient_pairing_zero`'s `hgrad` | `D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` (`PressureJets.lean:126`) is field-for-field `SmoothL2Field`'s `smooth`+`integrable`; **plus** the `pressureGradient p t = gradient (p t)` bridge, which is *not yet in the tree* — I proved it, 8 lines, std 3 axioms (`/tmp/rev136/pgrad.lean`, paste below) | **S**, ~15 lines |
| **E3** | `hmom` in `Lp`: `Gt.toLp = ν•(laplacianField u).toLp − (advectionField u u).toLp − P.toLp + f.toLp` | pointwise `D01.temporalDerivative_slice_eq` (`D01/Pressure.lean:196`); `laplacianField_field` (`OrdinaryViscousStability.lean:16`) and the `advectionField` field lemma identify the carrier fields with `Δu`/`(u·∇)u`; then `EulerOrdinarySobolev.field_ext` + `toLp_addField`/`toLp_fieldNeg`/smul push it through `toLp` | **S–M**, ~40 lines |
| **E4** | `hd`: `HasDerivAt (fun r => ‖(velocity r).toLp‖²) (2⟪u,∂ₜu⟫) t` on `Ioo 0 T` | `wordEnergy_hasDerivWithinAt T hT A B hA hB hd 0 t` (`Euler/OrdinaryWordTime.lean:87`) — `wordEnergy 0 A = ‖A.toLp‖²` closes by `simp [wordEnergy]` (verified, `/tmp/rev136/we0.lean` EXIT 0, via the `@[simp] wordField_zero`); `hA` = `Evolution.velocityField_jetLp_continuous` (**done**, `Evolution.lean:164`); `hB` = the same for the `∂ₜu` path — **still owed**, built from `D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` (`PressureJets.lean:148`) by copying the `velocityField_jetLp_continuous` argument; `hd` = pointwise `HasDerivAt (fun r => u(r,x)) (∂ₜu t x) t` from `ClassicalSolutionR.velocity_smooth` | **M**, ~120 lines, the real cost of the next lane |

Plus the two glue steps the earlier review already flagged: `Icc 0 S` → `Ioo 0 T`
(`projIcc` disposal, as in `EnergyIdentityHigh_core`) and
`HasDerivAt.congr_of_eventuallyEq` to move `fun s => ‖(velocity s).toLp‖²` to
`fun s => l2Sq (slice u s)` on a neighbourhood — the latter is exactly
`norm_toLp_sq_eq_l2Sq` applied at every nearby `s`, i.e. E2 already supplies it.

### Then, and only then, in `Bindings/EnergyAbsorptionV2.lean` (~30 lines)

`gradientSq_eq_fderivSum` (finding 2's one-liner), `spec_gradientSq_eq_sum`,
`spec_l2Sq_eq_inner`, `spec_pairing_eq_inner` and `spec_energyIdentity_value` exactly as
pasted in finding 3 — they are already proved and only need a home that can see both
`Contracts.V1` and `NSFormalization`.

### The Ep bridge, proved, for whoever takes the lane

```lean
theorem pressureGradient_eq_gradient (p : Space → ℝ) (x : Space) :
    ∑ i : Fin 3, (fderiv ℝ p x (axis i)) • axis i = gradient p x := by
  refine PiLp.ext fun j => ?_
  have hg : (gradient p x).ofLp j = fderiv ℝ p x (axis j) := by
    rw [← inner_gradient_left (𝕜 := ℝ) (f := p) (x := x) (y := axis j), axis,
      EuclideanSpace.inner_single_right]
    simp
  simp [axis, hg, Pi.single_apply, mul_ite]
```
(`/tmp/rev136/pgrad.lean`, EXIT 0, `[propext, Classical.choice, Quot.sound]`.
`Contracts.V1.pressureGradient` (`Packet.lean:114`) is literally this sum with
`coordinateVector i = axis i` by `rfl`.)
**Pitfall worth a LESSONS line:** `inner_gradient_left` is a `simp` lemma, so
`rw [← inner_gradient_left …]; simp` loops back to the original goal and reports
"unsolved goals" on the *unchanged* statement.  Break the loop by rewriting with
`EuclideanSpace.inner_single_right` (or `PiLp.inner_apply`) **in the same `rw`**
before any `simp`.

---

## Commands run (all from the worktree, after `. scripts/lean-env.sh`, `cd verification`)

| command | result |
|---|---|
| `LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.C01.Vocabulary` | `Build completed successfully (4573 jobs).` EXIT 0 |
| `lake env lean ../formalization/NSFormalization/Section4/C01/Vocabulary.lean` | EXIT 0, silent |
| `lake env lean ../research/C01/axioms_e2.lean` | EXIT 0, 7 × standard three axioms |
| `make check` (from worktree root) | EXIT 0 |
| `lake env lean /tmp/rev136/fidelity.lean` | EXIT 1 **by design** — E2a/E2c `rfl` ✅, E2b `rfl` fails (quoted above) |
| `lake env lean /tmp/rev136/tail.lean` | EXIT 0 — the E2b one-liner |
| `lake env lean /tmp/rev136/bindseed.lean` | EXIT 0, 3 × standard three axioms — full spec-vocabulary chain |
| `lake env lean /tmp/rev136/nonvac.lean` | EXIT 0 — nonzero carrier element, 4 bridges instantiated |
| `lake env lean /tmp/rev136/dup.lean` | EXIT 0 — findings 6 and 7 |
| `lake env lean /tmp/rev136/weaken.lean` | EXIT 0 — finding 8 |
| `lake env lean /tmp/rev136/repro_notation.lean` | EXIT 1, parse error reproduced verbatim |
| `lake env lean /tmp/rev136/repro_deprecated.lean` | EXIT 0 + deprecation warning reproduced verbatim |
| `lake env lean /tmp/rev136/pgrad.lean` | EXIT 0 — the Ep bridge |
| `lake env lean /tmp/rev136/we0.lean` | EXIT 0 — `wordEnergy 0 A = ‖A.toLp‖²` by `simp [wordEnergy]` |

`make test` / `make test-mutations` not run: the lane registers no contract and no
`Contracts/`, `Bindings/` or `Tests/` module changed (`git diff --stat` = 1 Lean file
under `formalization/` + 3 records).
