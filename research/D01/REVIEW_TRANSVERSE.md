# Review — lane 079 (D01 · P2 · SL4, Fourier transverse form)

Reviewer run against commit `ad211f1` in worktree `.claude/worktrees/079-D01-p2-sl4-transverse`.
Files reviewed: `formalization/NSFormalization/Section4/D01/Transverse.lean` (262 lines),
`research/D01/ATTEMPTS_TRANSVERSE.md`, `research/D01/axioms_transverse.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is correct and clean, the three statements are faithful, and the deliverable
(`transverse_of_divergence_free`) is **token-identical** to the hypothesis lane 081's
`lerayComplement_eq_zero_of_transverse` consumes — verified by feeding one into the other.
The notes are all in `ATTEMPTS_TRANSVERSE.md`: the **Lemma B gap paragraph is wrong in one
place, over-cautious in another, and silent about the two obstructions that actually matter**.
No code change is requested; findings 1–5 ask for a rewrite of that paragraph (corrected text
supplied in §"Corrected Lemma B gap" below).

---

## 1. Compiles — all green

| command (from `verification/`, after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `lake build NSFormalization.Section4.D01.Transverse` | `Build completed successfully (9880 jobs).` |
| `lake env lean ../formalization/NSFormalization/Section4/D01/Transverse.lean` | **silent** (no output, no warning) |
| `lake env lean ../research/D01/axioms_transverse.lean` | 3 declarations, each `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` on both files | only the docstring sentence "No `sorry`, no `axiom`" and the three `#print axioms` lines — no occurrence in code |
| `make check` (repo root of the worktree) | `Ran 13 tests … OK`; `30 work items: ownership, contract registration and task cards consistent.` |
| `make test` (extra, not requested) | all registered contracts replayed, "standard logical axioms only" |

The one unused-variable warning (`_hc`) seen in the `lake build` tail comes from an upstream
dependency, **not** from this module: `lake env lean` on `Transverse.lean` prints nothing.

## 2. Statement fidelity — all four sub-checks pass

All four were machine-checked in a scratch file (`/tmp/rev079/check1.lean`), which
**compiles silently**.

### (a) `hdiv` really is the divergence — and the lane-074 bridge is `rfl`, not "a short check"

`A03.partialDeriv j v = fun x => spatialDerivative (lift v) 0 x (coordinateVector j)`
(`Section4/A03/OuterTameProduct.lean:59`) and
`spatialDivergence u t x = ∑ i, (spatialDerivative u t x (coordinateVector i)) i`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:67`). Both of these are `rfl`:

```lean
example (v : Space → Space) (x : Space) :
    (∑ j : Fin 3, partialDeriv j v x j) = spatialDivergence (lift v) 0 x := rfl

example (u : SpaceTime → Space) (t : ℝ) (x : Space) :
    (∑ j : Fin 3, partialDeriv j (fun y => deriv (fun r => u (r, y)) t) x j)
      = spatialDivergence (fun p : SpaceTime => temporalDerivative u p.1 p.2) t x := rfl
```

(the second works because `deriv f t` *is* `fderiv ℝ f t 1` and `spatialDerivative` only ever
evaluates its field at the fixed time, so the `lift`/`time 0` ↔ `time t` bookkeeping is invisible).
Consequently lane 074 feeds Lemma A with **no bridge lemma at all**:

```lean
example {ν a f T} (w : ClassicalSolutionR ν a f T) {t} (ht : t ∈ Ioo (0:ℝ) T) :
    ∀ x : Space, ∑ j : Fin 3,
      partialDeriv j (fun y => deriv (fun r => w.velocity (r, y)) t) x j = 0 :=
  fun x => DivergenceTime.spatialDivergence_temporalDerivative_eq_zero w ht x   -- typechecks
```

The worker's ATTEMPTS says this "needs a short `show`/defeq check". It needs nothing.

### (b) Conclusion is token-identical to the consumer's hypothesis

`LerayDatum.lean:316` does not exist on this branch; the consumer lives on
`erenup/081-D01-p2-leray-datum` (`git show 310fbb5:…/LerayDatum.lean`), hypothesis

```lean
(htr : ∀ᵐ ξ ∂(volume : Measure MNS2.R3),
  ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (((h j : FourierData)) ξ) = 0)
```

`MNS2.R3` is `abbrev R3 := EuclideanSpace ℝ (Fin 3)`
(`vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:11`), i.e. reducibly `Space`
(`ProblemStatement.lean:30`). Transcribing that hypothesis verbatim and discharging it with
lane 079's theorem typechecks:

```lean
example {Z : SmoothL2Field Space} (hdiv …) (m : ℕ) {A : RealVectorSobolev ((m:ℝ)+1)} (hA …) :
    ∀ᵐ ξ ∂(volume : Measure MNS2.R3),
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (((A j : FourierData)) ξ) = 0 :=
  transverse_of_divergence_free hdiv m hA        -- typechecks, no coercion, no massage
```

Paper check: eq:Rpressure (`paper/sections/02-preliminaries.tex:90`) is
`∇p = (I−P)(f − ∇·(u⊗u))`, obtained by applying `(I−P)` to the momentum equation and killing
`(I−P)∂ₜu` and `(I−P)νΔu` — SL4 is exactly the first of those two, and this is the shape proved.

### (c) The `c^{-3/2}` / `c⁻¹ • ξ` normalization is right — verified independently

`angularFrequencyDilation` is an isometric extension of `schwartzAngularDilation`
(`Paper3/AngularFourierDilation.lean:80`), whose **defining** formula is
`schwartzAngularDilation φ ξ = c ^ (-3/2 : ℝ) • φ (c⁻¹ • ξ)` — `rfl`
(`AngularFourierDilation.lean:16, 25`). Via `angularFrequencyDilation_toLp` (`:87`) this gives,
with no reference to the worker's proof:

```lean
example (φ : SchwartzMap Space ℂ) :
    (angularFrequencyDilation (φ.toLp 2 volume) : Space → ℂ) =ᵐ[volume]
      fun ξ => (frequencyUnit ^ (-3/2 : ℝ) : ℝ) • φ (frequencyUnit⁻¹ • ξ) := by
  rw [angularFrequencyDilation_toLp]
  filter_upwards [(schwartzAngularDilation φ).coeFn_toLp 2 volume] with ξ h
  rw [h]; exact schwartzAngularDilation_apply φ ξ          -- typechecks
```

and the worker's `angularFrequencyDilation_coeFn` instantiated at `φ.toLp` agrees with it
(checked in the same scratch, transporting the `toLp` a.e. identity across `ξ ↦ c⁻¹ • ξ` with
`MeasurePreserving.quasiMeasurePreserving.ae` — the composition is not a plain `rw`).
Independent sanity check on the exponent: the operator is defined as an **isometry**, and
`∫ |c^{-3/2} h(c⁻¹ξ)|² dξ = c^{-3}·c³ ∫|h|²` only for the exponent `-3/2` in dimension 3
(`amplitude_sq_jacobian : (c^{-3/2})² · c³ = 1`, `AngularFourierDilation.lean:35`). A wrong
power would contradict the definition, not merely cancel.

### (d) Not vacuous

`hA` is never the obstruction — every `SmoothL2Field` has a datum at every real order
(`SmoothDatum.lean:289 exists_isSobolevDatum_of_contDiff_memLp`), and the full hypothesis set is
inhabited; both were constructed in Lean:

```lean
example (m : ℕ) : ∃ (Z : SmoothL2Field Space) (A : RealVectorSobolev ((m : ℝ) + 1)),
    (∀ x, ∑ j : Fin 3, partialDeriv j Z.field x j = 0) ∧ IsSobolevDatum ((m:ℝ)+1) Z.field A
```
(zero field + `exists_isSobolevDatum_of_contDiff_memLp`; typechecks). Mathematically non-trivial
witnesses exist too (curl of any Schwartz field), and `hdiv` is used essentially in the proof
(`hdiv x` inside the `hsum0` calc), so the theorem is not a disguised tautology.

## 3. Consistency — clean

* Imports: `Transverse.lean` imports exactly one module, `NSFormalization.Section4.D01.DerivativeDatum`. Canonical.
* **Zero `def` / `abbrev` / `structure`** in the module — no restated definitions, nothing to
  drift. All three declarations are theorems.
* No `NSFormalization.Paper3` decl is shadowed; `grep` over `formalization/` finds **no**
  pre-existing `angularFrequencyDilation_coeFn` (nor one on `erenup/integration`), so this is
  not a duplicate.

## 4. Honesty of ATTEMPTS — accurate on the route, **wrong on the Lemma B gap**

Route section, step-by-step: accurate. Every cited declaration opens where claimed
(`DerivativeDatum.lean:141, 245`; `AngularFourierDilation.lean:80, 126`;
`SobolevDirectionalDerivative.lean:10, 59`; `OuterTameProduct.lean:59`;
`LpSmoothField.lean:31`). The "what did NOT work" section is a genuine negative record and its
central observation — that `angularDirectionalDerivative` is dilation-*conjugated*, so the naive
mid-symbol coefficient is at `c⁻¹ξ` and not at `ξ` — is correct and worth keeping.

The claim **"no `Lp` dilation coeFn existed anywhere" is TRUE**: grepping
`formalization/NSFormalization` for `angularFrequencyDilation` turns up only `_toLp`,
`_toDistribution`, `_realSymmetry` and uses; `vendor/HeliCorgi`'s `compMeasurePreserving`
lemmas (`R3YoungL2L1Bochner.lean:57`, `R3ConjugationReflection.lean:120`) are about translation
and reflection, not dilation.

### Numbered findings

**F1 — [minor / honesty] `ATTEMPTS_TRANSVERSE.md`, Lemma B gap (b): "order-lowering of a datum … does not exist as a packaged declaration" is FALSE.**
It exists at exactly the datum level: `A03.IsScalarSobolevDatum.lower`
(`Section4/A03/ScalarTameProduct.lean:114`), and `A03.isSobolevDatum_iff`
(`Section4/A03/VectorTameProduct.lean:54`) is `Iff.rfl`. The vector version is one term, which
I compiled:
```lean
example {s r : ℝ} (hrs : r ≤ s) {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) :
    IsSobolevDatum r z (WithLp.toLp 2 fun i => lowerDatum s r hrs (A i)) :=
  (isSobolevDatum_iff r z _).mpr fun i =>
    IsScalarSobolevDatum.lower hrs ((isSobolevDatum_iff s z A).mp hA i)   -- typechecks
```
So orders 0 and 1 of the `memHInfty_jets` requirement are **not** a blocker: lower from `m = 2`.
*Fix:* delete the claim; cite the two lemmas.

**F2 — [minor / honesty] Lemma B gap (a) is real but S-sized, not a blocker.**
Nothing merged provides all-orders spatial smoothness of the time-derivative slice (grep
confirms), but it is ~25 lines from what is already there. I proved it
(`/tmp/rev079/check2.lean`, compiles silently):
```lean
theorem contDiff_temporalDerivative_slice {T : ℝ} {v : ℝ × Space → Space}
    (hv : ContDiffOn ℝ ∞ v (Ico (0:ℝ) T ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    ContDiff ℝ ∞ (fun x : Space => deriv (fun r => v (r, x)) t)
```
Route: restrict to the **open** sub-slab `Ioo 0 T ×ˢ univ` → `ContDiffAt ℝ ∞ v (t,x)` for every
`x`; rewrite the slice as `x ↦ fderiv ℝ v (t,x) (1,0)` by
`DivergenceTime.deriv_time_slice` (`:77`); then `ContDiffAt.fderiv_right (m := ∞) (by simp)`
(the same idiom `LpSmoothField.lean:49` already uses) composed with `x ↦ (t,x)` and
`ContinuousLinearMap.apply ℝ Space (1,0)`. The ATTEMPTS' remark that lane 074's exchange lemmas
"handle only the first order" is beside the point — the all-orders statement does not go through
them. *Fix:* restate as "S-sized, route known", with the sketch.

**F3 — [minor / honesty] Line 16's attribution to lane 076 is wrong on both halves.**
Lane 076's `angularDirectionalMid_coeFn` (`Section4/A04/LaplacianPairing.lean:67` on
`erenup/076-A04-sl3-pairing`) is the coefficient of the **middle multiplier `M_s`**, not of the
dilation `U = angularFrequencyDilation`; it would not have supplied this lemma. And lane 076 **is**
merged to `erenup/integration` (PR #78, `05128d7`) — it is simply not an ancestor of this
worktree's HEAD, which is why it was invisible here. *Fix:* say "not available in this worktree
(076 is not an ancestor of this branch); and 076's lemma is about `M_s`, a different operator."

**F4 — [moderate / omission] Lemma B's missing hypothesis is not recorded: D2 needs a *smooth* datum path that `ClassicalSolutionR` does not supply.**
`A04.TimeDerivative.timeDeriv_isSobolevDatum` (`:182`) takes
`hGc : ContDiffOn ℝ ∞ G (Ico (0:ℝ) T)` alongside `hGd`. `ClassicalSolutionR.sobolev`
(`Section4/A02/SolutionClass.lean:132-134`) supplies only `ContinuousOn G (Ico 0 T)`. So D2's
`hA` is **not** free from the solution class — a smooth-Sobolev-path hypothesis has to be
carried in (as A02's energy-field lemmas do). The ATTEMPTS says D2 "delivers … matches Lemma A's
`hA` verbatim", which is true of the *conclusion* and silent about this input.

**F5 — [moderate / omission] The `SmoothL2Field` wrapper for `∂ₜu(t,·)` is, in the P2 context, equivalent to P2's own target.**
`SmoothL2Field Space` with field `z` is exactly `SmoothSquareIntegrableJets z`
(`DatumToJets.lean:298 memHInfty_iff_smoothSquareIntegrableJets`, `:374 exists_smoothL2Field_of_memHInfty`).
And `Section4/D01/Pressure.lean` proves both directions, given the force slice:
`pressureGradient_slice_smoothL2_of` (`:317`) and `temporalDerivative_slice_smoothL2_of` (`:336`).
Hence `SmoothSquareIntegrableJets (∂ₜu(t,·)) ↔ SmoothSquareIntegrableJets (∇p(t,·))` for
`MemForceR f` — the P2 target. **Lemma B therefore cannot be the step that produces P2's jets**;
it can only run downstream of SL7's non-circular seed. This is the load-bearing fact about
Lemma B and the ATTEMPTS does not mention it; framing the blocker as "a `SmoothL2Field` wrapper"
makes it sound like bookkeeping.

**F6 — [nit] `angularFrequencyDilation_coeFn` sits in the wrong namespace.**
It is a Paper3-level fact about `NSFormalization.Paper3.angularFrequencyDilation` living in
`namespace NSFormalization.Section4.D01`. It belongs next to its subject in
`formalization/NSFormalization/Paper3/AngularFourierDilation.lean`. **SIMP-lane item, not a
blocker for this merge.** Checked `erenup/085-D01-p2-sl7c-commute` and `erenup/086-SIMP-A04`:
neither carries a copy today, so there is no duplicate yet — but if 085 does copy it, the two
should be deduplicated in favour of a promoted Paper3 lemma.

**F7 — [nit] Nothing imports `Transverse.lean` yet**, and `formalization/NSFormalization.lean`
(the default lake target) lists no `Section4/*` module at all, so neither `lake build` (default)
nor CI (`.github/workflows/*.yml` runs only `make check`) compiles it. Pre-existing convention
for Section4 modules, not a lane-079 regression; it just means the module's health depends on
lane 081/085 pulling it in.

**F8 — [nit] `logs/LESSONS.md` not updated.** CLAUDE.md rule 4 asks for a one-line cross-task
entry; the dilation-conjugation trap in "what did NOT work" is exactly the kind of thing that
belongs there.

---

## Corrected Lemma B gap paragraph (replacement text for `ATTEMPTS_TRANSVERSE.md`)

> ## Lemma B — status: NOT proved. What it actually needs.
>
> Lemma B would be `transverse_of_divergence_free (Z := wrapper) hdiv m hA` with
> `Z.field = fun x => deriv (fun r => u.velocity (r,x)) t`.
>
> **`hdiv` is free.** `∑ⱼ partialDeriv j Z.field x j` is *definitionally*
> `spatialDivergence (fun p => temporalDerivative u.velocity p.1 p.2) t x` (checked `rfl`), so
> lane 074's `DivergenceTime.spatialDivergence_temporalDerivative_eq_zero w ht x` discharges it
> directly — no bridge lemma, no `show`.
>
> **`hA` is not free.** `A04.TimeDerivative.timeDeriv_isSobolevDatum` at order `m+1` (needs
> `2 ≤ m+1`) delivers the right conclusion, but requires a datum path `G` that is
> `ContDiffOn ℝ ∞ G (Ico 0 T)`. `ClassicalSolutionR.sobolev` (`SolutionClass.lean:132`) supplies
> only `ContinuousOn G`, so the smooth-path hypothesis must be carried in by the caller.
>
> **The wrapper `Z : SmoothL2Field Space` is the real obstruction, and it is P2's own target.**
> `SmoothL2Field` with field `z` is exactly `SmoothSquareIntegrableJets z`
> (`DatumToJets.lean:298`, `:374`), and for `MemForceR f`
> `SmoothSquareIntegrableJets (∂ₜu(t,·)) ↔ SmoothSquareIntegrableJets (∇p(t,·))` by
> `Pressure.lean`'s `pressureGradient_slice_smoothL2_of` / `temporalDerivative_slice_smoothL2_of`.
> So **Lemma B cannot be the step that establishes P2's jets** — it must run after SL7's
> non-circular order-0 seed has produced them. That, not a technical wrapper, is why Lemma B is
> deferred.
>
> Of the two sub-items the wrapper needs, neither is hard:
> * **(a) all-orders spatial smoothness of the time-derivative slice** — not merged anywhere, but
>   S-sized (~25 lines, verified by the reviewer): restrict to the open sub-slab `Ioo 0 T ×ˢ univ`,
>   rewrite the slice as `x ↦ fderiv ℝ v (t,x) (1,0)` via `DivergenceTime.deriv_time_slice`, then
>   `ContDiffAt.fderiv_right (m := ∞)` composed with `x ↦ (t,x)` and
>   `ContinuousLinearMap.apply ℝ Space (1,0)`. Parallel to `D01.contDiff_slice`
>   (`DatumToJets.lean:366`).
> * **(b) square-integrability of every spatial jet** — via `memHInfty_jets` this needs a datum at
>   *every* natural order, and D2 gives only `m ≥ 2`. Orders 0 and 1 follow by **datum order
>   lowering, which already exists**: `A03.IsScalarSobolevDatum.lower`
>   (`ScalarTameProduct.lean:114`) plus `A03.isSobolevDatum_iff` (`VectorTameProduct.lean:54`,
>   `Iff.rfl`) give the vector form in one term. Not a gap.

---

## Commands run (reviewer)

```
bash scripts/lean-install.sh                                   # idempotent, "== OK"
. scripts/lean-env.sh ; export LEAN_NUM_THREADS=6
cd verification && lake build NSFormalization.Section4.D01.Transverse
                                                               # Build completed successfully (9880 jobs)
cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/Transverse.lean
                                                               # silent
cd verification && lake env lean ../research/D01/axioms_transverse.lean
                                                               # 3 decls, [propext, Classical.choice, Quot.sound]
grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats' <both files>   # docstring + #print axioms only
make check                                                     # 13 tests OK; 30 work items consistent
make test                                                      # all registered contracts: standard axioms only
cd verification && lake env lean /tmp/rev079/check1.lean        # silent — 2(a)(b)(c)(d) + F1 all typecheck
cd verification && lake env lean /tmp/rev079/check2.lean        # silent — F2's missing lemma, proved
git show 310fbb5:formalization/NSFormalization/Section4/D01/LerayDatum.lean   # lane 081 consumer
git merge-base --is-ancestor 05128d7 HEAD                      # false: lane 076 not in this branch
```
