# ATTEMPTS — T11 / U9e (lane 338, `ExistenceInputH3.lean`)

Positive and negative record.  Nothing here is generated; append only.

## 0. A broken base — the 338 worktree did not compile before any of my work

`lake build NSFormalization.Section3.T11.MildClassical` on the lane base
(`0c03030c merge 334 into 338 base`, before my merge of lane 337) fails with

```
error: NSFormalization/Section3/T11/MildClassical.lean:1305:50: Application type mismatch: The argument
  hFI
has type
  PersistenceInput T F
but is expected to have type
  ∀ (t : ℝ), 0 ≤ t → IsPeriodicLerayDatum (?m.143 t) (P t)
in the application
  momentum_of_mildPressure hu hPc hPI hFI
error: NSFormalization/Section3/T11/MildClassical.lean:1319:47: (the same for projected_of_mildPressure)
```

Cause: lane 334 branched from a 327 state in which
`momentum_of_mildPressure` / `projected_of_mildPressure` still took an explicit
`(hF : PersistenceInput T F)`.  Commit `2572e51b [327-T11] MildMomentum:
discharge force persistence` later **removed** that argument
(`persistenceInput_force_of_smooth` proves it), and
`git merge-base --is-ancestor 2572e51b f6c4d91e` = NO.  The lead's merge of 334
into the 338 base took integration's newer `MildMomentum.lean` together with
334's older `MildClassical.lean`; git reported no conflict because the two files
are different files.

**Repair (the only edit this lane makes to an existing module):** three lines of
`MildClassical.lean` — delete the now-unused
`have hFI : PersistenceInput T F := forcePersistenceInput hg hgp hF T` and drop
`hFI` from the two applications.  Nothing else changed; `mild_to_classical` and
`exists_classical_of_picard` keep their exact statements, and
`lake env lean MildClassical.lean` is then silent (0 errors, 0 warnings).
`forcePersistenceInput` survives as an unused (but still correct) theorem.

This is worth an entry in `logs/LESSONS.md` — *the lane brief said `MildClassical`
was available; it was present but unbuildable* — but the brief forbids editing
that file, so it is recorded here and in `REPORT_338.md` instead.

## 1. The force bound is `L¹` in time, not a supremum — the one real obstacle

`torusForcedPicard_quantitative` (313) takes `(hFB : ∀ t ∈ Icc 0 1, ‖F t‖ ≤ B)`
and `exists_classical_of_picard` (334) produces `B` by compactness of `[0,1]`,
i.e. `B` depends on the *force itself*.  The predicate's force hypothesis is
`forceSobolevENormT 1 (m : ℝ) g ≤ M m`, and
`forceSobolevENormT q s f = ⨅ G (datum path), eLpNorm G q forceTimeMeasure`
with `forceTimeMeasure = volume.restrict (Ioi 0)` — an **`L¹_t H^s_x`** norm.
An `L¹` bound never bounds a supremum, so the sup route is dead: a force
concentrated in a short time bump has small `L¹_t H³` norm and arbitrarily large
`sup_t ‖F t‖_{H³}`.

**What works instead.**  The Picard self-map certificate only needs a bound `b`
on the *affine* part `L(t) = e^{νtΔ}A + ∫₀ᵗ e^{ν(t−s)Δ}F(s) ds`, and the heat
evolution is a contraction at every order, so

```
‖L(t)‖ ≤ ‖A‖ + ∫₀ᵗ ‖F(s)‖ ds ≤ ‖A‖ + ∫₀^T ‖F(s)‖ ds .
```

That is `torus_forcedLinear_bound_L1` in the new module — the `L¹` analogue of
`LocalExistence.torus_forcedLinear_bound`, which bounds the integral by `B·t`
from a supremum.  With it, `b := K.toReal + (M 3).toReal` is admissible for
*every* datum in the `H³` ball and every force obeying the bounds, and the
horizon `torusKernelTime ν (torusPicardThreshold ‖bilinear‖ b)` is chosen before
the data.  **Only `M 3` is used**; all higher orders enter through lane 330's
unconditional `persistence_unconditional`.

## 2. The infimum in `forceSobolevENormT` has to be *attained*

`forceSobolevENormT 1 s g ≤ M 3` is an infimum bound, but the affine estimate
needs the bound for the *particular* path `F₃` produced by
`exists_smooth_forceDatumPath` (334).  The `≤` in the wrong direction is not
enough.  `forceSobolevENormT_eq_of_path` fixes this: two admissible paths agree
at every `t ≥ 0` by `T10/DatumBasics.datum_unique` (the datum's coefficients are
determined by the field), hence a.e. for `volume.restrict (Ioi 0)`, hence their
`eLpNorm`s are equal — so the infimum is attained at *every* admissible path and
`forceSobolevENormT 1 s g = eLpNorm F₃ 1 forceTimeMeasure`.

Chain used (all from Mathlib):
`eLpNorm_one_eq_lintegral_enorm` → `ofReal_norm` →
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` →
`lintegral_mono_set Ioc_subset_Ioi_self` → `ENNReal.toReal_mono` +
`ENNReal.toReal_ofReal`.

## 3. Errors actually hit, and their fixes

1. **`failed to synthesize Module ℂ ↥(PeriodicSobolev s)` / `(deterministic)
   timeout at whnf, 200000 heartbeats`** at the first `eLpNorm`/`AEStronglyMeasurable`
   goal, and `failed to synthesize Norm (↥(PeriodicSobolev 3) →L[ℝ] ↥(PeriodicSobolev 3)
   →L[ℝ] ↥(PeriodicSobolev 2))` at every occurrence of `‖C.analytic.bilinear‖`.
   The global instance search on the `lp`-based submodule carrier is too slow.
   **Fix:** the three *named* (never anonymous, per `logs/LESSONS.md` 2026-09-17)
   local instances `existenceInputH3NormedGroup` / `NormedSpace` /
   `SecondCountableTopologyEither`, copied in shape from
   `MildClassical.lean`'s `mildClassical*` ones.  After that the whole module
   elaborates inside the default heartbeat budget — **no `set_option
   maxHeartbeats` anywhere in this lane**.

2. **`add_le_add_right hAK _` type mismatch**: at this Mathlib pin
   `add_le_add_right (h : b ≤ c) (a) : a + b ≤ a + c` adds on the *left*.
   Replaced by `linarith`.

3. **`unknown constant ENNReal.sup_ne_top`** in the non-vacuity witness.
   Avoided entirely by taking `K := periodicSobolevENorm 3 a` (finite by
   `periodicSobolevENorm_ne_top_smooth`) and `le_rfl` for the ball, instead of a
   `⊔` of the `H¹` and `H³` norms.

4. **`No goals to be solved`** after `simp only [ofReal_norm]` in the `eLpNorm`
   calc step: the trailing `rfl` was already done by `simp only`; deleted.  (The
   `forceTimeMeasure` abbreviation unfolds to `volume.restrict (Ioi 0)`
   definitionally, so no `show` is needed.)

5. **`Classical.choose` does not reduce to the supplied witness.**  A probe
   example that tried to say "the `δ` of the theorem *is* `picardHorizon ν K M`"
   through `Classical.choose_spec` fails with a type mismatch.  **Fix:** the
   module now proves the explicit-horizon statement
   `exists_classical_on_picardHorizon` first, and
   `periodicQuantitativeLocalInputH3` is a two-line corollary of it.  The probe
   checks the horizon claim against that theorem, not against a choice term.

## 4. Paths considered and rejected

* **Re-proving 332/337 generically in the ball order `s`.**  Rejected: `restart`,
  `restartBeyond`, `extendsBeyond` are *verbatim* API fields; parametrizing them
  by `s` would change the statements.  The lane copies each statement with the
  changed ball and repeats the (unchanged) proof, exactly as amendment 2 §3
  prescribes.
* **Deriving `PeriodicQuantitativeLocalInput'` from the `H³` version by an
  `H¹ → H³` norm comparison.**  Impossible in the correct direction:
  `‖·‖_{H¹} ≤ ‖·‖_{H³}`, so an `H¹` ball is *larger*.  See `H1_GAP.md` §2.
* **Making `picardHorizon` depend on the whole family `M` through a sum or a
  supremum over orders.**  Unnecessary: only `M 3` is consumed, and a smaller
  dependence is a stronger statement.
