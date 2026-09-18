import NSFormalization.Section3.T20.CriticalRegularity
import NSFormalization.Section3.T12.SpectralGap
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Section3.T11.MeanIdentity

/-!
# T20 unit U3 — `bIntegral` (`03-torus.tex:442-444`, `eq:bintegral`)

This module proves the reconciled `CriticalRegularityTAPI.bIntegral` field
verbatim:
`criticalBIntegral (meanFreeForce g) ≤ criticalRho g` for `g ∈ forceClassT`.

Mathematically this is the torus mirror of R43's
`forceHomogeneousENorm_le_forceSobolevENormL1`
(`Section4/R43/ForcePath.lean`): removing the spatial zero mode is contractive
on the inhomogeneous `H^{1/2}` datum path.  At the level of Fourier data the
mean-free force slice `h(t,·) = meanZeroPartT (g(t,·))` shares every nonzero
coefficient with `g(t,·)`, and the homogeneous weight `(4π²|k|²)^{s/2}` (which
is `0` at `k=0`) is dominated by the inhomogeneous Bessel weight
`(1+4π²|k|²)^{s/2}` at nonnegative order.  The bounded even reweighting
`T12.reweightDatum` turns each inhomogeneous datum path slice `G t` of `g` into
a homogeneous datum of `h(t,·)` of no larger norm; a slicewise
`lintegral_mono` then transports the bound through the time integral to the
`L¹_t H^{1/2}_x` datum-path infimum `criticalRho g`.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators ComplexConjugate

/-- The order-`1/2` homogeneous/inhomogeneous Fourier reweighting multiplier
used to build a homogeneous datum of the mean-free force from an inhomogeneous
datum of the force. -/
private def bWeight (k : PeriodicFrequency) : ℝ :=
  homogeneousDatumWeight (1 / 2) k / periodicFrequencyWeight k ^ ((1 / 2 : ℝ) / 2)

private theorem periodicFrequencyWeight_pos' (k : PeriodicFrequency) :
    0 < periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have : 0 ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  linarith

private theorem homogeneousDatumWeight_nonneg' (s : ℝ) (k : PeriodicFrequency) :
    0 ≤ homogeneousDatumWeight s k := by
  by_cases hk : k = 0
  · simp [homogeneousDatumWeight, hk]
  · simp only [homogeneousDatumWeight, hk, ↓reduceIte]
    exact Real.rpow_nonneg (by unfold periodicAngularFrequencySq; positivity) _

private theorem bWeight_nonneg (k : PeriodicFrequency) : 0 ≤ bWeight k :=
  div_nonneg (homogeneousDatumWeight_nonneg' _ k)
    (Real.rpow_nonneg (periodicFrequencyWeight_pos' k).le _)

private theorem bWeight_abs_le_one (k : PeriodicFrequency) : |bWeight k| ≤ 1 := by
  rw [abs_of_nonneg (bWeight_nonneg k)]
  refine (div_le_one₀ (Real.rpow_pos_of_pos (periodicFrequencyWeight_pos' k) _)).2 ?_
  exact homogeneousDatumWeight_le_periodicFrequencyWeight_rpow (1 / 2) (by norm_num) k

private theorem bWeight_even (k : PeriodicFrequency) : bWeight (-k) = bWeight k := by
  unfold bWeight homogeneousDatumWeight periodicFrequencyWeight periodicAngularFrequencySq
  simp [neg_eq_zero]

-- Slicewise contraction: at every time `t`, an inhomogeneous order-`1/2`
-- datum `A` of the force slice `g(t,·)` yields (by the bounded even reweighting)
-- a homogeneous datum of the mean-free force slice of no larger norm, so the
-- homogeneous `Ḣ^{1/2}` norm `criticalB (meanFreeForce g) t` is at most `‖A‖`.
-- The `maxHeartbeats` bump only covers the `IsPeriodicHomogeneousDatum`
-- reconstruction over the nested `PiLp`/`lp` datum carrier.
set_option maxHeartbeats 400000 in
private theorem bIntegral_slice (g : SpaceTimeField) (t : ℝ)
    (A : PeriodicSobolev (1 / 2))
    (hdat : IsPeriodicDatum (1 / 2) (fun x => g (t, x)) A) :
    criticalB (meanFreeForce g) t ≤ ‖A.1‖ₑ := by
  have hi_gt : ∀ i : Fin 3,
      Integrable (torusLift (fun x => ((g (t, x) i : ℝ) : ℂ))) periodicTorusMeasure :=
    fun i => hdat.integrable_component i
  have hB : IsPeriodicHomogeneousDatum (1 / 2) (fun x => meanFreeForce g (t, x))
      ⟨reweightDatum bWeight 1 zero_le_one bWeight_abs_le_one A.1,
       reweightDatum_real bWeight 1 zero_le_one bWeight_abs_le_one bWeight_even A⟩ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x j
      exact congrArg (· - forceMeanT g t) (hdat.1 x j)
    · exact hdat.2.1.sub (integrable_const (forceMeanT g t))
    · change meanT (fun x => g (t, x) - forceMeanT g t) = 0
      rw [NSFormalization.Section3.T11.MeanIdentity.meanT_sub_const hdat.2.1 (forceMeanT g t)]
      exact sub_eq_zero.mpr rfl
    · intro i k
      show reweightDatum bWeight 1 zero_le_one bWeight_abs_le_one A.1 i k =
        (homogeneousDatumWeight (1 / 2) k : ℂ) •
          periodicFourierCoeff (fun x => ((meanFreeForce g (t, x) i : ℝ) : ℂ)) k
      rw [reweightDatum_apply]
      by_cases hk : k = 0
      · subst hk
        have hw0 : bWeight 0 = 0 := by simp [bWeight, homogeneousDatumWeight]
        rw [hw0]
        simp [homogeneousDatumWeight]
      · rw [hdat.2.2 i k]
        have hsplit : (fun x => ((meanFreeForce g (t, x) i : ℝ) : ℂ)) =
            (fun x => ((g (t, x) i : ℝ) : ℂ) - ((forceMeanT g t i : ℝ) : ℂ)) := by
          funext x
          rw [show (meanFreeForce g (t, x)) i = g (t, x) i - forceMeanT g t i from rfl,
            Complex.ofReal_sub]
        have hcoeff : periodicFourierCoeff (fun x => ((meanFreeForce g (t, x) i : ℝ) : ℂ)) k =
            periodicFourierCoeff (fun x => ((g (t, x) i : ℝ) : ℂ)) k := by
          rw [hsplit, periodicFourierCoeff_sub (hi_gt i) (integrable_const _),
            periodicFourierCoeff_const]
          simp [hk]
        rw [hcoeff]
        have hp : periodicFrequencyWeight k ^ ((1 / 2 : ℝ) / 2) ≠ 0 :=
          (Real.rpow_pos_of_pos (periodicFrequencyWeight_pos' k) _).ne'
        change
          ((homogeneousDatumWeight (1 / 2) k /
                periodicFrequencyWeight k ^ ((1 / 2 : ℝ) / 2) : ℝ) : ℂ) *
              (((periodicFrequencyWeight k ^ ((1 / 2 : ℝ) / 2) : ℝ) : ℂ) *
                periodicFourierCoeff (fun x => ((g (t, x) i : ℝ) : ℂ)) k) =
            ((homogeneousDatumWeight (1 / 2) k : ℝ) : ℂ) *
              periodicFourierCoeff (fun x => ((g (t, x) i : ℝ) : ℂ)) k
        rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hp]
  have henorm : ‖reweightDatum bWeight 1 zero_le_one bWeight_abs_le_one A.1‖ₑ ≤ ‖A.1‖ₑ := by
    have hnorm : ‖reweightDatum bWeight 1 zero_le_one bWeight_abs_le_one A.1‖ ≤ ‖A.1‖ := by
      simpa using reweightDatum_norm_le bWeight 1 zero_le_one bWeight_abs_le_one A.1
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hnorm
  have hmember : periodicHomogeneousENorm (1 / 2) (fun x => meanFreeForce g (t, x)) ≤
      ‖reweightDatum bWeight 1 zero_le_one bWeight_abs_le_one A.1‖ₑ :=
    iInf_le (fun A' : {A' : PeriodicSobolev (1 / 2) //
        IsPeriodicHomogeneousDatum (1 / 2) (fun x => meanFreeForce g (t, x)) A'} => ‖A'.1‖ₑ)
      ⟨⟨reweightDatum bWeight 1 zero_le_one bWeight_abs_le_one A.1,
        reweightDatum_real bWeight 1 zero_le_one bWeight_abs_le_one bWeight_even A⟩, hB⟩
  exact le_trans hmember henorm

/-- `03-torus.tex:441-444`, `eq:bintegral`:
`∫₀^∞ ‖h(t)‖_{Ḣ^{1/2}} dt ≤ ρ`. -/
theorem bIntegral : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    criticalBIntegral (meanFreeForce g) ≤ criticalRho g := by
  intro g _hg
  unfold criticalBIntegral criticalRho forceSobolevENormT
  refine le_iInf (fun G => ?_)
  rw [eLpNorm_one_eq_lintegral_enorm]
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
  exact bIntegral_slice g t (G.1 t) (G.2.1 t (le_of_lt ht))

end NSFormalization.Section3.T20
