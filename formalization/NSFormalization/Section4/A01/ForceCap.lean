import NSFormalization.Section4.A01.Propagation
import NSFormalization.Section4.A04.Continuity

/-!
# A01 unit A3 row `A3-L1·f` — the forcing integral cap `Bbnd`

`research/A01/A3_SPLIT.md` row **A3-L1·f** (`§0 step 4`, `appendix-a-local-theory.tex:146-147`):
the Grönwall assembly `gronwall_bddAbove_Ico` (`Section4/A01/Propagation.lean`) consumes, for
the forcing term `b := fun s => sobolevNormAt m f s = ‖f(s,·)‖_{H^m}`, a single real cap
`Bbnd` with

```
∀ t ∈ Ico 0 T₀, ∫ s in 0..t, sobolevNormAt m f s ≤ Bbnd
```

together with the two side facts `ContinuousOn b (Ico 0 T₀)` and `0 ≤ b s` that the same
hypothesis bundle needs.  This module produces both caps and the two side facts, straight from
`MemForceR` (`Section4/D01/ForceClass.lean`), and shows the slot fits `gronwall_bddAbove_Ico`.

## Two caps

* `forceCap` — the **route-robust** cap.  On a finite horizon `[0,T₀]` the force norm is
  continuous (`A04.continuousOn_sobolevNormAt_force`, which holds on `Ico 0 T` for *every* `T`,
  so on the closed `Icc 0 T₀ ⊆ Ico 0 (T₀+1)`), hence interval integrable, so
  `Bbnd := ∫ s in 0..T₀, sobolevNormAt m f s` dominates every `∫ s in 0..t` by monotonicity of
  the integral of a nonnegative integrand (`intervalIntegral.integral_mono_interval`).  This is
  the cap the manuscript's `F_R = C^∞([0,∞);H^∞)` always supplies, needing only continuity in
  time, and is what `gronwall_bddAbove_Ico` is plugged with below.

* `intervalIntegral_le_forceSobolevENormL1` / `..._of_memForceR` — the **manuscript-literal**
  cap `∫ s in 0..t, ‖f(s,·)‖_{H^m} ≤ ‖f‖_{L¹_tH^m}` (`A04.forceSobolevENormL1`).  The formalized
  `F_R` (`02-preliminaries.tex:17`, eq:Rclasses) is not merely `C^∞([0,∞);H^∞)` but additionally
  requires `‖f‖_{L¹_tH^m} + ‖f‖_{L²_tH^m} < ∞` at every integer order; `MemForceR` encodes this
  as the `MemLp G 1 forceTimeMeasure` clause, so the finiteness hypothesis is discharged for
  free by `A04.memL1Hm_of_memForceR`.  The bound holds for every nonnegative `t` at once, so it
  gives the *uniform* cap `Bbnd := (forceSobolevENormL1 m f).toReal` (`forceCap_L1`).

  On the `⊤ ↦ 0` totalization: in `intervalIntegral_le_forceSobolevENormL1` the hypothesis
  `forceSobolevENormL1 m f ≠ ⊤` is **derivable from `hf`** (`A04.memL1Hm_of_memForceR`), hence a
  provably redundant argument; it is kept only to make the argument visible and to guard a
  possible future weakening of `MemForceR`.  The `⊤ ↦ 0` collapse would falsify a *different*
  statement — the one that also drops `hf` — and only for a force that *has* slice data but is
  not `L¹` in time: a nonzero time-independent `g` has `∫₀^∞‖g‖_{H^m} = ∞`, so
  `forceSobolevENormL1 = ⊤`, RHS `= 0`, LHS `> 0`; such a `g` is **not** in `F_R`, which is
  exactly why `hfin` cannot be violated for `f ∈ F_R`.  (Dually, a field with *no* datum path has
  `sobolevENorm = ⊤`, so `sobolevNormAt = ⊤.toReal = 0` on the **left** as well and the
  inequality is vacuously true — the counterexample must have slice data.)

## Why `0 ≤ y_m 0` needs no bridge

`sobolevNormAt s u t = (sobolevENorm s _).toReal` (`A04.Forcing.lean`), a `.toReal`, hence
`≥ 0` by `ENNReal.toReal_nonneg`; `sobolevNormAt_nonneg` records the one-liner.  The Grönwall
base `0 ≤ y_m 0 = 0 ≤ ‖u(0)‖_{H^m}` is the same fact for the velocity, needing no order-0 datum
bridge (`research/A01/A3_SPLIT.md` §3a finding F7).
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

namespace NSFormalization.Section4.A01

open NSFormalization.Section4.A04
open NSFormalization.Section4.D01
  (MemForceR IsSobolevPath IsSobolevDatum sobolevENorm forceTimeMeasure)

/-- `sobolevNormAt s u t = (sobolevENorm s _).toReal` is nonnegative: a `.toReal` is `≥ 0`
(`ENNReal.toReal_nonneg`).  This is `hbnn`/`hy0` of `gronwall_bddAbove_Ico` for both the forcing
term and the velocity, so `0 ≤ y_m 0` needs no separate bridge (F7). -/
theorem sobolevNormAt_nonneg (s : ℝ) (u : VelocityField) (t : ℝ) :
    0 ≤ sobolevNormAt s u t :=
  ENNReal.toReal_nonneg

/-- **A3-L1·f, route-robust cap.**  For `f ∈ F_R`, order `m`, and a finite horizon `T₀ > 0`,
the forcing term `b := fun s => sobolevNormAt m f s` satisfies the three `gronwall_bddAbove_Ico`
hypotheses on `Ico 0 T₀`: it is continuous, nonnegative, and its running integral
`∫ s in 0..t` is capped by the single constant `Bbnd := ∫ s in 0..T₀, sobolevNormAt m f s`.

Continuity on the *closed* `[0,T₀]` (needed for interval integrability) comes from
`A04.continuousOn_sobolevNormAt_force` at horizon `T₀+1`, since `Icc 0 T₀ ⊆ Ico 0 (T₀+1)`.  The
cap is then monotonicity of the integral of a nonnegative integrand
(`intervalIntegral.integral_mono_interval`, with `[0,t] ⊆ [0,T₀]`). -/
theorem forceCap {f : VelocityField} (hf : MemForceR f) (m : ℕ) {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ Bbnd : ℝ,
      ContinuousOn (fun s => sobolevNormAt (m : ℝ) f s) (Ico (0 : ℝ) T₀) ∧
      (∀ t ∈ Ico (0 : ℝ) T₀, 0 ≤ sobolevNormAt (m : ℝ) f t) ∧
      (∀ t ∈ Ico (0 : ℝ) T₀, (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s) ≤ Bbnd) := by
  have hint : IntervalIntegrable (fun s => sobolevNormAt (m : ℝ) f s) volume 0 T₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT₀.le]
    exact (continuousOn_sobolevNormAt_force hf m (T₀ + 1)).mono
      (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩)
  refine ⟨∫ s in (0 : ℝ)..T₀, sobolevNormAt (m : ℝ) f s,
      continuousOn_sobolevNormAt_force hf m T₀,
      fun t _ => sobolevNormAt_nonneg (m : ℝ) f t, ?_⟩
  intro t ht
  refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2.le ?_ hint
  exact ae_of_all _ (fun x => sobolevNormAt_nonneg (m : ℝ) f x)

/-- **A3-L1·f, manuscript-literal cap (conditional).**  `∫ s in 0..t, ‖f(s,·)‖_{H^m} ≤
‖f‖_{L¹_tH^m}` for any `t ≥ 0`, given that the `L¹_t H^m` norm is finite.  The proof passes to
`ℝ≥0∞`: for every datum path `G` in the infimum defining `forceSobolevENorm 1 m f`,
`∫ s in 0..t, sobolevNormAt m f s = ∫ s in Ioc 0 t, ‖G s‖` (uniqueness of the slice datum,
`A04.sobolevNormAt_eq`), whose `ENNReal.ofReal` is `∫⁻ s in Ioc 0 t, ‖G s‖ₑ ≤ ∫⁻ s in Ioi 0,
‖G s‖ₑ = ‖G‖_{L¹} = eLpNorm G 1 forceTimeMeasure`; taking `.toReal` (finite by hypothesis) gives
the claim.

The `hfin` argument is **derivable from `hf`** here (`A04.memL1Hm_of_memForceR`) — see
`intervalIntegral_le_forceSobolevENormL1_of_memForceR` for the version that discharges it — so it
is redundant for `f ∈ F_R`.  It is kept explicit so the honest conditional argument is visible
and so the lemma survives a hypothetical weakening of `MemForceR`; the `⊤ ↦ 0` collapse would
falsify only the statement that *also* drops `hf`, and then only for a force with slice data that
is not `L¹` in time (see the module docstring). -/
theorem intervalIntegral_le_forceSobolevENormL1
    {f : VelocityField} (hf : MemForceR f) (m : ℕ)
    (hfin : forceSobolevENormL1 (m : ℝ) f ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s) ≤ (forceSobolevENormL1 (m : ℝ) f).toReal := by
  have hgnn : ∀ s, 0 ≤ sobolevNormAt (m : ℝ) f s := fun s => sobolevNormAt_nonneg (m : ℝ) f s
  have hint : IntervalIntegrable (fun s => sobolevNormAt (m : ℝ) f s) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le ht]
    exact (continuousOn_sobolevNormAt_force hf m (t + 1)).mono
      (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 (by linarith)⟩)
  -- Step 1: `ofReal` of the interval integral is bounded by the `L¹_t H^m` enorm.
  have hstep1 :
      ENNReal.ofReal (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s)
        ≤ forceSobolevENormL1 (m : ℝ) f := by
    refine le_iInf ?_
    rintro ⟨G, hpath, _hmeas⟩
    show ENNReal.ofReal (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s)
        ≤ eLpNorm G 1 forceTimeMeasure
    rw [intervalIntegral.integral_of_le ht]
    have hintOn : Integrable (fun s => sobolevNormAt (m : ℝ) f s) (volume.restrict (Ioc 0 t)) := by
      simpa [IntegrableOn] using hint.1
    rw [ofReal_integral_eq_lintegral_ofReal hintOn (ae_of_all _ (fun s => hgnn s))]
    have hcongr :
        (∫⁻ s in Ioc 0 t, ENNReal.ofReal (sobolevNormAt (m : ℝ) f s) ∂volume)
          = ∫⁻ s in Ioc 0 t, ‖G s‖ₑ ∂volume := by
      refine setLIntegral_congr_fun measurableSet_Ioc ?_
      intro s hs
      show ENNReal.ofReal (sobolevNormAt (m : ℝ) f s) = ‖G s‖ₑ
      rw [sobolevNormAt_eq (hpath s (le_of_lt hs.1)), ofReal_norm]
    rw [hcongr, eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_mono' (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) le_rfl
  -- Step 2: descend to `ℝ` through `.toReal`.
  have hnn : 0 ≤ ∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s :=
    intervalIntegral.integral_nonneg ht (fun s _ => hgnn s)
  calc (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s)
      = (ENNReal.ofReal (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s)).toReal :=
        (ENNReal.toReal_ofReal hnn).symm
    _ ≤ (forceSobolevENormL1 (m : ℝ) f).toReal := ENNReal.toReal_mono hfin hstep1

/-- **A3-L1·f, manuscript cap for `f ∈ F_R`.**  The finiteness hypothesis of
`intervalIntegral_le_forceSobolevENormL1` is free from `MemForceR`, via
`A04.memL1Hm_of_memForceR` (the `L¹_t H^m` clause of the formalized `F_R`,
`02-preliminaries.tex:17`). -/
theorem intervalIntegral_le_forceSobolevENormL1_of_memForceR
    {f : VelocityField} (hf : MemForceR f) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s) ≤ (forceSobolevENormL1 (m : ℝ) f).toReal :=
  intervalIntegral_le_forceSobolevENormL1 hf m (memL1Hm_of_memForceR hf m) ht

/-- **The Grönwall bundle with the manuscript L¹ cap as `Bbnd`.**  A version of `forceCap`
whose single cap is the order-`m` `L¹_t H^m` norm `(forceSobolevENormL1 m f).toReal`, uniform
over all `t` (not just `t < T₀`).  For `f ∈ F_R` this norm is finite, so the cap is a genuine
real constant. -/
theorem forceCap_L1 {f : VelocityField} (hf : MemForceR f) (m : ℕ) (T₀ : ℝ) :
    ContinuousOn (fun s => sobolevNormAt (m : ℝ) f s) (Ico (0 : ℝ) T₀) ∧
    (∀ t ∈ Ico (0 : ℝ) T₀, 0 ≤ sobolevNormAt (m : ℝ) f t) ∧
    (∀ t ∈ Ico (0 : ℝ) T₀,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (m : ℝ) f s) ≤ (forceSobolevENormL1 (m : ℝ) f).toReal) :=
  ⟨continuousOn_sobolevNormAt_force hf m T₀,
   fun t _ => sobolevNormAt_nonneg (m : ℝ) f t,
   fun _ ht => intervalIntegral_le_forceSobolevENormL1_of_memForceR hf m ht.1⟩

/-- **The slot fits.**  `forceCap` drops straight into `gronwall_bddAbove_Ico` as the forcing
data `b := fun s => sobolevNormAt m f s`, discharging `hb`, `hbnn`, `hbbnd` in one line; the
remaining Grönwall hypotheses (on `y`, `k`, `Cgron`, the step inequality) are left as variables. -/
example {f : VelocityField} (hf : MemForceR f) (m : ℕ)
    {T₀ Cgron Kbnd : ℝ} {y k : ℝ → ℝ}
    (hCgron : 0 ≤ Cgron) (hy0 : 0 ≤ y 0) (hT₀ : 0 < T₀)
    (hy : ContinuousOn y (Ico 0 T₀)) (hk : ContinuousOn k (Ico 0 T₀))
    (hknn : ∀ t ∈ Ico 0 T₀, 0 ≤ k t)
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, k s) ≤ Kbnd)
    (hstep : ∀ t ∈ Ico 0 T₀, y t ≤ y 0 +
        ∫ s in (0 : ℝ)..t, (Cgron * k s * y s + sobolevNormAt (m : ℝ) f s)) :
    ∃ Bbnd : ℝ, ∀ t ∈ Ico 0 T₀, y t ≤ (y 0 + Bbnd) * Real.exp (Cgron * Kbnd) := by
  obtain ⟨Bbnd, hbc, hbnn, hbbnd⟩ := forceCap hf m hT₀
  exact ⟨Bbnd, gronwall_bddAbove_Ico hCgron hy0 hy hk hbc hknn hbnn hkbnd hbbnd hstep⟩

end NSFormalization.Section4.A01
