# C01 unit U2 — "Force class to slices" — attempts log

> **Superseded sections (reviewer note, 2026-09-13):** the sections "Route that worked", "Cast handling" and snag 3 below describe the *pre-rewire* proof through `A02.sliceLp` / `Comparison.continuous_slice_of_continuousOn`, which no longer exists in the committed module; the authoritative description is the final section "Rewire to D01". Snag 2's actual failure mode is `rw` reporting "did not find an occurrence of the pattern" (the spec `l2Sq` and vendor `Comparison.l2Sq` are defeq but not syntactically equal); the committed `show` fix at `ForceSlices.lean:117` is correct.

Spec field: `EnergyAbsorptionAPI.forceTimeRegularity` (`research/C01/Spec.lean:326-329`).
Goal: from `MemForceR f`, for every `t ≥ 0` get `MemLp (slice f t) 2 volume`, and
`ContinuousOn (fun s => l2Norm (slice f s)) (Ici 0)`.

Module: `formalization/NSFormalization/Section4/C01/ForceSlices.lean`.
Conformance: `research/C01/axioms_u2.lean`.

## Result

Both conjuncts proved. **Continuity holds on the full closed half line `Ici 0`,
endpoint `t = 0` included** — no reduction to `Ioi 0` was needed. The reason: the
`m = 0` datum path `G` supplied by `MemForceR` is `ContDiffOn ℝ ∞ G futureTimes`
with `futureTimes = Ici 0` (`Data.lean:548, 113`), hence `ContinuousOn G (Ici 0)`
at the endpoint too. The task brief anticipated a possible `t = 0` gap; there is
none, because the datum path — not just the physical field — is smooth at `0`.

## Route that worked

Both conjuncts reduce to the order-0 datum-to-slice machinery lane 040 already
built in `Section4/A02/Energy.lean`, plus the vendor `L²`-norm bridge.

* **First conjunct.** `NavierStokesR3.Comparison.continuous_slice_of_continuousOn`
  (`ComparisonFiniteEnergy.lean:31`) makes `slice f t` continuous from
  `ContDiffOn ℝ ∞ f futureDomain` (`futureDomain = Ici 0 ×ˢ univ`); then
  `A02.memLp_of_isSobolevDatum` (order-0, `Continuous` hypothesis) transports
  `IsSobolevDatum 0 (slice f t) (G t)` to `MemLp (slice f t) 2 volume`.

* **Continuity conjunct.** The identity `l2Norm (slice f s) = ‖A02.sliceLp (G s)‖`
  at each `s ≥ 0`, via:
  - `NavierStokesR3.LpNormTools.lpNorm_two_eq_sqrt_l2Sq` : for `MemLp z 2`,
    `comparisonLpNorm 2 z = √(Comparison.l2Sq z)`, and `Comparison.l2Sq` is
    definitionally the spec's `l2Sq` (`∫ ‖z x‖^2`);
  - `A02.sliceLp_ae` : `sliceLp (G s) =ᵐ slice f s`, so `lpNorm_congr_ae` moves
    `comparisonLpNorm` onto `sliceLp (G s)`;
  - `Lp.norm_def` : `comparisonLpNorm 2 (⇑(sliceLp (G s))) = ‖sliceLp (G s)‖`.
  `A ↦ ‖sliceLp A‖` is continuous because `sliceLp` is a composition of bundled
  continuous linear maps (`PiLp.continuous_apply` for the `RealVectorSobolev`
  projection, `continuous_subtype_val` for `RealSobolevHilbert 0 → FourierData`,
  `(cyclesToAngular 0).symm.continuous`, `(physicalLp 0 le_rfl).continuous`,
  `vectorLpReassembly.continuous`). Composing with `ContinuousOn G (Ici 0)` and
  `ContinuousOn.congr` gives the result.

Interval integrability of `s ↦ ‖f(s)‖₂` / `‖f(s)‖₂²` on each `[0,t]` is not
proved: the spec field's docstring states it is a consequence of the continuity
conjunct (continuous on `Ici 0` ⇒ continuous on compact `[0,t]` ⇒ interval
integrable) and deliberately not a separate obligation.

## Cast handling

`MemForceR`'s `m = 0` witness has order `((0 : ℕ) : ℝ)`, while `sliceLp` and the
order-0 lemmas are stated at literal `(0 : ℝ)`. Handled exactly as
`A02.uniformFiniteEnergy_of_sobolevDatumPath`: an auxiliary lemma carries the
order as a variable `s` with `hs : s = 0`, then `subst hs`; the main theorem
calls it with `s := ((0:ℕ):ℝ)` and `hs := Nat.cast_zero`.

## Small failures fixed along the way

1. `PiLp.continuous_apply i` in term mode did not unify against the expected
   `Continuous (fun A : RealVectorSobolev 0 => A i)` (leftover `∀ β …` in the
   inferred type). Fixed by supplying implicits explicitly:
   `PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => RealSobolevHilbert 0) i`.
   (`(coord i).continuous` and `by fun_prop` also work — verified in a probe.)
2. After `rw [lpNorm_two_eq_sqrt_l2Sq hmem]` the residual
   `√(l2Sq z) = √(Comparison.l2Sq z)` was not closed by `rw`'s auto-`rfl`
   (instances transparency does not unfold the two `def`s). Fixed by `show`ing
   the goal directly in `Comparison.l2Sq` form (default transparency unfolds the
   defeq), then `exact (lpNorm_two_eq_sqrt_l2Sq hmem).symm`.
3. `continuous_slice_of_continuousOn` is in namespace `NavierStokesR3.Comparison`;
   used unqualified at first (unknown identifier), then fully qualified.

No approach was abandoned as unworkable; the datum-norm route was the intended
one and succeeded. No `sorry`, no new axiom.

## Commands

- `lake build NSFormalization.Section4.C01.ForceSlices` (from `verification/`) —
  `Build completed successfully`, and `lake env lean` on the file emits no
  diagnostics.
- `lake env lean ../research/C01/axioms_u2.lean` —
  `depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Rewire to D01 (post-review, before merge)

The coordinator flagged that the first version reused `sliceLp`, `sliceLp_ae`,
`memLp_of_isSobolevDatum`, `componentLp`, `cyclesComponent` from
`Section4/A02/Energy.lean` §1–2 — the pre-dedupe helpers that lane 040 (PR #43)
deletes and rewires to `Section4/D01/DatumToJets.lean`. After #43 the module
would have failed to compile. Rewired so the module depends only on D01 and
`SolutionClass`.

**Imports before → after**

- before: `NSFormalization.Section4.A02.Energy`,
  `NavierStokes.R3.ComparisonFiniteEnergy`, `NavierStokes.R3.LpNormTools`.
- after: `NSFormalization.Section4.A02.SolutionClass`
  (only `MemForceR`/`IsSobolevPath`/`IsSobolevDatum`/field-type restatements —
  no `Energy` helpers), `NSFormalization.Section4.D01.DatumToJets`,
  `NavierStokes.R3.LpNormTools`.
  Verified no import path reaches `A02.Energy` (the only textual match is a
  docstring line in `SolutionClass.lean`).

**What changed in the proof**

- First conjunct: `A02.memLp_of_isSobolevDatum` (needed only `Continuous`) →
  `D01.memLp_of_isSobolevDatum` (`DatumToJets.lean:267`, needs `ContDiff ℝ ∞`),
  fed the smooth slice from `D01.contDiff_slice` (`:366`) via a small
  `contDiff_slice_future` that `.mono`s `ContDiffOn ℝ ∞ f (Ici 0 ×ˢ univ)` down
  to the horizon `[0,t+1)`. This replaces the old
  `Comparison.continuous_slice_of_continuousOn`, so `ComparisonFiniteEnergy` is
  no longer imported.
- Continuity identity: `l2Norm z = ‖A02.sliceLp A‖` →
  `l2Norm z = ‖D01.jetOfDatum 0 0 (le_refl 0) A‖`, proved with
  `lpNorm_two_eq_sqrt_l2Sq` (→ `(eLpNorm z 2).toReal`),
  `eLpNorm_congr_norm_ae` + `norm_iteratedFDeriv_zero` (order-0 jet has the same
  norm as the field), and `jetOfDatum_ae` (`:202`) + `Lp.norm_def`.
- Continuity of the realization: `continuous_sliceLp` →
  `continuous_jetOfDatum_zero`. Same composition-of-CLMs argument, but through
  D01's building blocks `physicalJetLp 0`, `sobolevOrderLowering`,
  `(cyclesToAngular _).symm`, plus `PiLp.continuous_apply` and
  `continuous_subtype_val`. (`sobolevOrderLowering` is a `→L[ℂ]`,
  `physicalJetLp` a `→L[ℝ]`; scalar field is irrelevant to `.continuous`.)

**Cast device.** D01's lemmas are indexed by a *nat* order `m` and produce
`RealVectorSobolev (m : ℝ)` / `IsSobolevDatum (m : ℝ)`, while `MemForceR`'s
`m = 0` witness has order exactly `((0 : ℕ) : ℝ)`. So instead of `subst`ing to
`(0 : ℝ)`, the whole proof is carried at the nat-cast order `((0 : ℕ) : ℝ)` and
every D01 call is at `m := 0` (`jetOfDatum 0 0 (le_refl 0)`), which needs no
`((0 : ℕ) : ℝ) = 0` transport at all — the cleanest resolution of the cast
issue the coordinator warned about.

**Result unchanged.** Still fully proved on `Ici 0` (endpoint `t = 0` included),
no `sorry`/axiom.

**Commands after rewire**

- `lake build NSFormalization.Section4.C01.ForceSlices` → `Build completed
  successfully (9879 jobs)`; `lake env lean` on the file → no diagnostics.
- `lake env lean ../research/C01/axioms_u2.lean` →
  `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `make check` → exit 0 (plan/contract-policy/work-queue all consistent).
