# Review — lane 067, task D01, P2 sub-lemma SL7a

**Subject.** `formalization/NSFormalization/Section4/D01/OrderZeroDatum.lean`,
`exists_isSobolevDatum_zero_of_memLp` (89 lines, one theorem), plus
`research/D01/axioms_sl7a.lean` and `research/D01/ATTEMPTS_SL7A.md`.

**Verdict: ACCEPT-WITH-NOTES.**

The theorem is exactly what P2's SL7 asked for, it is proved from `MemLp z 2 volume`
alone, and the reality step is a genuine density argument — no `L¹`, no smoothness, no
pointwise Fourier transform, no dependence on lane 059's `L¹ ∩ L²` bridge. Every finding
below is LOW or a NOTE; none blocks the merge.

---

## 1. Commands and results

Environment: `bash scripts/lean-install.sh` (exits `== OK`), `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, no `-j`. All `lake` invocations from `verification/`, one at a time.

| # | Command (cwd) | Result |
|---|---|---|
| 1 | `verification$ lake build NSFormalization.Section4.D01.OrderZeroDatum` | `Build completed successfully (9872 jobs).` **exit 0** |
| 2 | grep `warning` in the build log | 14 warnings, **all pre-existing in other files** (`Source/RealSobolev.lean`, `Paper3/SpatiallyCompactTime.lean`, `Paper3/RealPositiveDensity.lean`, `Paper3/RealVectorPositiveDensity.lean`). `grep "warning.*D01"` → **no matches**. |
| 3 | `verification$ lake env lean ../research/D01/axioms_sl7a.lean` | **exit 0**, no errors; the `Contracts.V1.Data.IsSobolevDatum 0 z A` `example` typechecks; `#print axioms` → `[propext, Classical.choice, Quot.sound]` **exactly** |
| 4 | `grep -n "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" OrderZeroDatum.lean` | **no matches** |
| 5 | same grep on `research/D01/axioms_sl7a.lean` | 3 hits, all benign: two in the header comment, one is the `#print axioms` line itself |
| 6 | `WT$ make check` | **exit 0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` ("30 work items: ownership, contract registration and task cards consistent") |
| 7 | scratch `example` applying the theorem to `ClassicalSolutionR.pressure_gradient` (see §3) | **exit 0**, typechecks; scratch deleted |
| 8 | `formalization/.lake/packages` | **symlink** → `/data_8T/ping/blowup_density/verification/.lake/packages`. Not a fresh clone. See NOTE 6. |

## 2. Statement — CONFIRMED

`#check` gives the signature with nothing hidden:

```
@NSFormalization.Section4.D01.exists_isSobolevDatum_zero_of_memLp :
  ∀ {z : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space},
    MeasureTheory.MemLp z 2 MeasureTheory.volume →
      ∃ A, NSFormalization.Section4.D01.IsSobolevDatum 0 z A
```

* **Only hypothesis is `MemLp z 2 volume`.** No `Integrable`, no `ContDiff`, no
  `HasCompactSupport`, no extra instance arguments.
* **`IsSobolevDatum` is the realization predicate.** `Contracts/V1/Data.lean:160` and
  `Section4/D01/SmoothDatum.lean:237` are token-identical apart from the binder type
  (`SpatialField` vs its unfolding `Space → Space`); both read
  `∀ i ψ, angularRealization s (A i) ψ = ∫ x, ψ x * ((z x i : ℝ) : ℂ)`. The `example` in
  `axioms_sl7a.lean` discharges the *contract* form with the theorem by `exact`, which is
  the defeq bridge, and it typechecks (command 3).
* **`RealVectorSobolev 0` is the right carrier.** `Paper3/RealVectorPositiveDensity.lean:15`,
  `abbrev RealVectorSobolev (s : ℝ) := Product (Fin 3) (RealSobolevHilbert s)` — the same
  carrier `Contracts.V1.Data.IsSobolevDatum`, `sobolevENorm` and `ClassicalSolutionR.sobolev`
  all use.

## 3. Usability for P2 — CONFIRMED

The following scratch file typechecked (`lake env lean`, exit 0) and was deleted:

```lean
example (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ A : RealVectorSobolev 0,
      IsSobolevDatum 0
        (fun x => NavierStokes.ProblemStatement.pressureGradient u.pressure t x) A :=
  exists_isSobolevDatum_zero_of_memLp (u.pressure_gradient t ht)
```

So P2 can seed `∇p(t,·)`'s order-0 datum directly from `A02.ClassicalSolutionR.pressure_gradient`
(`SolutionClass.lean:137`, an `L²` fact only) with a one-line application. This was the point
of the sub-lemma and it lands.

## 4. Route audit — CLEAN, no hidden `L¹`

1. **`Paper3.sobolevRealization_zero` (`SobolevHilbertModel.lean:130-134`).** States
   `sobolevRealization 0 h = ((𝓕⁻ h : Lp ℂ 2 volume) : 𝓢'(Space, ℂ))`. This is Mathlib's
   `L²` inverse Fourier transform (`Lp.instFourierTransform`) embedded as a tempered
   distribution — an abstract-isometry statement with no integrability hypothesis and no
   pointwise Fourier integral. Confirmed as claimed.
2. **Reality — the step I was asked to scrutinise. It is a genuine density argument.**
   `SmoothDatum.fourier_conjugation` (`SmoothDatum.lean`, `𝓕 (conjugation u) = realSymmetry (𝓕 u)`
   for arbitrary `u : L²`) is proved by
   `SchwartzMap.denseRange_toLpCLM … |>.induction_on u (isClosed_eq …) …`: the predicate is
   closed because both sides are composites of continuous maps (`fourierCLM`, `conjugation`,
   `realSymmetry`), and on the dense Schwartz subspace it reduces to the pointwise
   `Source.RealSobolev.fourier_conjugate` (`RealSobolev.lean:61`), where the Fourier integral
   is legitimate because `φ` is Schwartz. **The pointwise transform is never assumed for a
   general `L²` function.** No `L¹` hypothesis appears anywhere in the chain.
   The file then uses it correctly: `conjugation_ae` (`SmoothDatum.lean:98`) + `Complex.conj_ofReal`
   give `conjugation (zc i) = zc i`, and
   `rw [mem_realSubspace_iff, ← fourier_conjugation (zc i), hconj i]` closes
   `𝓕 (zc i) ∈ realSubspace 0` by `rfl`.
3. **Convention transport.** `Paper3.cyclesToAngularRealVector` (`AngularRealVectorBochner.lean:15`)
   and `angularRealization_cyclesToAngularRealVector` (`:40`,
   `angularRealization s (cyclesToAngularRealVector s v i) = sobolevRealization s (v i)`) move
   cycles → angular *without changing the realized distribution*. Used exactly as intended.
4. **Real projection.** `realProjectionTo` (`RealPositiveDensity.lean:31`) and
   `realProjection_eq_self` (`RealSobolev.lean:131`) — the projection is the identity on an
   element already in `realSubspace`, so the physical distribution is untouched. Correct.
5. **Lane 059's `L¹ ∩ L²` bridge is absent.** I computed the full transitive import closure of
   `OrderZeroDatum` (1378 repo-local modules resolved). `B02` / `LowHigh` appear **nowhere**;
   the only `Section4` modules in the closure are `Section4.D01.SmoothDatum` and
   `Section4.D01.OrderZeroDatum` itself. `B02/LowHigh.lean:86`'s
   `coeFn_l2Fourier_ae (g) (hg1 : Integrable g volume) …` is therefore not reachable.
6. **Proof body re-checked by hand.** The `rw` chain
   `realProjection_eq_self (hmem i) → sobolevRealization_zero → fourierInv_fourier_eq →
   Lp.toTemperedDistribution_apply → integral_congr_ae` is sound; the `show` on line 81 is a
   defeq reduction of `WithLp.toLp 2 f i` and of the `RealSobolevHilbert → FourierData`
   coercion, which is why the `let` (rather than `set`) for `zc` matters. Nothing suspicious.

## 5. Findings

### F1 — LOW — the omitted norm identity is *not* one line, and the lane is right about that

**Declaration.** `exists_isSobolevDatum_zero_of_memLp`; the missing `‖A‖ = ‖z‖_{L²}`.

I was asked to judge whether the identity is one line from `Lp.norm_fourier_eq` plus the
Euclidean Pythagorean sum. **It is not.** The identity *is true with constant exactly 1* —
`Paper3.angularFrequencyDilation` (`AngularFourierDilation.lean:80`) is a
`≃ₗᵢ[ℂ]`, and `angularWeightEquiv` carries the two-sided bounds
`angularWeightEquiv_norm_le` / `angularWeightEquiv_symm_norm_le` with constant
`frequencyUnit ^ |s|`, which is `1` at `s = 0`; so `cyclesToAngular 0` is an isometry. But
the proof needs two pieces that are not in the tree:

* **(a) An order-0 isometry statement for the angular transport.**
  `cyclesToAngularRealVector_symm_norm_le` **does not exist** (verified: `unknown identifier`);
  only the scalar `cyclesToAngularReal_symm_norm_le` does. Worse, I tried the obvious scalar
  squeeze in a default-heartbeat scratch file and it **fails with
  `(deterministic) timeout at 'isDefEq', maximum number of heartbeats (200000)`** on
  `(cyclesToAngularReal 0).symm_apply_apply` — `cyclesToAngularReal` is an
  `ofSubmodules` of a `restrictScalars`, so that unification is expensive. This is presumably
  why `Paper3/AngularRealVectorBochner.lean` already carries `set_option maxHeartbeats 800000`.
  The lemma therefore belongs in that `Paper3` file, not in `OrderZeroDatum.lean`.
* **(b) The Euclidean-valued Pythagorean `L²` identity**
  `eLpNorm z 2 volume ^ 2 = ∑ i, eLpNorm (fun x => (z x i : ℝ)) 2 volume ^ 2`, which needs
  `EuclideanSpace.norm_eq` plus a `lintegral` finite-sum interchange with per-component
  measurability side conditions. No such lemma exists in the tree.

`Lp.norm_fourier_eq` (`Mathlib/Analysis/Fourier/LpSpace.lean:89`, `‖𝓕 f‖ = ‖f‖`, unconditional)
and `PiLp.norm_sq_eq_of_L2` are both available and are each one line, but they are the easy
half. Realistic cost: ~25-50 lines across `Paper3/AngularRealVectorBochner.lean` and a new
`eLpNorm` helper.

**Fix.** Add it in the next touch on this area, since I03 U7c's `sobolevENorm 0 = eLpNorm 2`
wants it (`A04/Forcing.lean:126` `sobolevENorm_eq` supplies the other half:
`IsSobolevDatum s z A → sobolevENorm s z = ‖A‖ₑ`). **The lane's own "Not done" entry in
`ATTEMPTS_SL7A.md` describes this correctly as "a separate chunk" — that assessment is
accurate and is the one to trust.**

### F2 — LOW — the theorem returns only `∃`, so the norm identity cannot even be *stated*

**Declaration.** `exists_isSobolevDatum_zero_of_memLp`.

The datum is built explicitly in the proof but discarded behind `∃`. Downstream
(`sobolevENorm_eq` and F1's norm identity) needs a named `A` to talk about `‖A‖`.

**Fix.** In the same touch as F1, expose
`def orderZeroDatum {z} (hz : MemLp z 2 volume) : RealVectorSobolev 0` (the term already on
lines 76-77) and `theorem isSobolevDatum_orderZeroDatum`, keeping
`exists_isSobolevDatum_zero_of_memLp` as the `⟨_, _⟩` corollary. Not urgent: existence is
what P2 needs today, and `Exists.choose` plus `sobolevENorm_eq` is a workable stopgap.

### F3 — LOW — module docstring advertises a norm identity the file does not prove

**Declaration.** `OrderZeroDatum.lean` module header, line 37:
"The Plancherel norm identity is `Lp.norm_fourier_eq` (constant `1` at order `0`)."

The file proves no norm statement. A reader of the module alone could reasonably conclude
`‖A‖ = ‖z‖₂` is available here. The honest "Not done" note lives only in
`research/D01/ATTEMPTS_SL7A.md`, which is not shipped with the module.

**Fix.** One sentence in the header: the norm identity is deliberately not proved in this
module; see F1 for what it costs.

### F4 — NOTE — the module is a leaf and is outside the default build targets

Nothing imports `NSFormalization.Section4.D01.OrderZeroDatum` (verified by grep over
`formalization/` and `verification/`), it is not in `formalization/NSFormalization.lean`
(which carries **no** `Section4.D01` imports at all — so this matches the existing convention,
`SmoothDatum` and friends are likewise absent), and `verification`'s
`defaultTargets = ["Tests", "Contracts"]` do not reach it. Section-4 results enter CI through a
`Bindings` module (`Bindings/DatumLemmas.lean` pulls in `DatumToJets`, `HomogeneousWitness`,
`ForceClass`; `Bindings/DatumLemmasV2.lean` pulls in `HalfOrder`).

**Consequence.** `make test` / a default `lake build` does **not** currently regress-check this
file; it only compiles when named explicitly. This is normal for a P2 *sub*-lemma with no
contract field of its own and will resolve when P2's binding lands — recording it so it is not
forgotten.

### F5 — NOTE — process: `lake -d ../formalization`, verified harmless

`ATTEMPTS_SL7A.md:48` records the build as
`lake -d ../formalization build NSFormalization.Section4.D01.OrderZeroDatum`, against the lane
rule "lake only from `verification/`". Checked and benign:

* `formalization/.lake/packages` is a **symlink** to `/data_8T/ping/blowup_density/verification/.lake/packages`
  — no fresh Mathlib clone was made.
* `formalization/.lake/build` (1.4 GB) is where `NSFormalization` oleans live under the
  canonical build as well (verification `require`s the package at path `../formalization`), so no
  duplicate tree was created. `.gitignore:12` has `**/.lake/`, and `git status` is clean, so
  nothing leaks into the PR.
* The canonical `cd verification && lake build …` was re-run for this review and exits 0
  (command 1).

**Fix.** None needed in code; just use the canonical invocation next time and record that one.

## 6. Honesty spot-check — ACCURATE

`research/D01/ATTEMPTS_SL7A.md` reports no failed attempts ("PROVED (first attempt compiled)").
I checked its load-bearing claim, that `SmoothDatum.exists_isSobolevDatum_of_contDiff_memLp`
could not be reused:

```
theorem exists_isSobolevDatum_of_contDiff_memLp {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume) (s : ℝ) :
    ∃ A : RealVectorSobolev s, IsSobolevDatum s z A
```

The claim is **correct, and in fact the log picks the stronger of the two reasons.** The
`ContDiff ℝ ∞ z` half is arguably obtainable for `∇p` from `ClassicalSolutionR.pressure_smooth`
(modulo a `ContDiffOn`-to-`ContDiff` slice argument), but the `∀ n, MemLp (iteratedFDeriv ℝ n z) 2`
half is genuinely unavailable: `ClassicalSolutionR` gives `∇p ∈ L²` at order **zero only**
(`SolutionClass.lean:137`), and nothing in the class bounds the higher jets of the pressure.
So the all-jets hypothesis really is the blocker, exactly as written.

The log's other substantive claims also check out: the no-`L¹` route (§4 above), the reason the
`let`/`set` distinction mattered, and the honest "Not done" scoping of the norm identity (F1).

## 7. Verdict

**ACCEPT-WITH-NOTES.** Builds clean, standard axioms only, statement is exactly SL7a with
`MemLp z 2 volume` as the sole hypothesis, no hidden `L¹` or smoothness anywhere in the route,
and it applies to `ClassicalSolutionR.pressure_gradient` in one line as P2 needs. Carry F1-F3
into the next touch on this area; F4 and F5 are notes only.
