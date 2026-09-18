import NSFormalization.Section3.T12.FourierEmbeddings

/-!
# Lane 341 probe: the three targeted fields of `MeanZeroSobolevCalculusAPI` close

Each `example` below is the field of
`research/T12/probes/api_on_canonical.lean` copied verbatim, with the API's
data fields `Cinfty` and `CHtwo` replaced by the explicit constants
`linftyConst` and `hTwoConst` of
`NSFormalization/Section3/T12/FourierEmbeddings.lean`, and is closed by the
proved theorem.  The last section exhibits a single-mode field satisfying every
hypothesis of the three fields and different from the zero field, so none of
them is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11 (torusScalarSeries)
open scoped ENNReal BigOperators ContDiff

/-! ## 1. The three fields, verbatim -/

/-- `boundedRepresentative`, with `Cinfty := linftyConst`. -/
example :
    ∀ v : SpatialField, MemPeriodicHmVector 2 v →
      periodicLpENorm ⊤ v ≤
        ENNReal.ofReal linftyConst * periodicSobolevENorm 2 v :=
  boundedRepresentative

/-- `Cinfty_pos`. -/
example : 0 < linftyConst := linftyConst_pos

/-- `lambda_exists`. -/
example :
    ∀ v : SpatialField, SmoothPeriodicT v →
      ∃ Lv : SpatialField, IsPeriodicLambda v Lv :=
  lambda_exists

/-- `hTwo_le_laplacian`, with `CHtwo := hTwoConst`. -/
example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) :=
  hTwo_le_laplacian

/-- `CHtwo_pos`. -/
example : 0 < hTwoConst := hTwoConst_pos

/-! ## 2. Single-mode non-vacuity

The hypotheses of the three fields are satisfied by a field different from
zero, so none of the three statements is vacuously true.  The witness is the
real single Fourier mode `x ↦ (e^{2πi x₁} + e^{-2πi x₁}) e` of
`torusScalarSeries`. -/

/-- The first lattice basis vector. -/
def modeFreq : PeriodicFrequency := fun j ↦ if j = 0 then 1 else 0

theorem modeFreq_ne_zero : modeFreq ≠ 0 := by
  intro h
  have h0 : modeFreq 0 = (0 : PeriodicFrequency) 0 := congrFun h 0
  simp [modeFreq] at h0

/-- The conjugate-symmetric coefficients of one real Fourier mode. -/
def modeCoeff : PeriodicFrequency → ℂ :=
  fun k ↦ if k = modeFreq ∨ k = -modeFreq then 1 else 0

theorem modeCoeff_neg (k : PeriodicFrequency) : modeCoeff (-k) = star (modeCoeff k) := by
  have hiff : (-k = modeFreq ∨ -k = -modeFreq) ↔ (k = modeFreq ∨ k = -modeFreq) := by
    rw [neg_eq_iff_eq_neg, neg_eq_iff_eq_neg, neg_neg]
    exact or_comm
  unfold modeCoeff
  simp only [hiff]
  split_ifs <;> simp

theorem modeCoeff_zero : modeCoeff 0 = 0 := by
  have hne : ¬((0 : PeriodicFrequency) = modeFreq ∨ (0 : PeriodicFrequency) = -modeFreq) := by
    rintro (h | h)
    · exact modeFreq_ne_zero h.symm
    · exact modeFreq_ne_zero (neg_eq_zero.mp h.symm)
  simp only [modeCoeff, hne, ↓reduceIte]

theorem modeCoeff_modeFreq : modeCoeff modeFreq = 1 := by
  simp only [modeCoeff, true_or, ↓reduceIte]

theorem modeCoeff_weighted_summable (N : ℕ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖modeCoeff k‖) := by
  classical
  refine summable_of_ne_finset_zero
    (s := ({modeFreq, -modeFreq} : Finset PeriodicFrequency)) fun k hk ↦ ?_
  have hzero : modeCoeff k = 0 := by
    have hne : ¬(k = modeFreq ∨ k = -modeFreq) := by
      rintro (h | h) <;> exact hk (by simp [h])
    simp only [modeCoeff, hne, ↓reduceIte]
  simp [hzero]

theorem modeCoeff_summable : Summable (fun k ↦ ‖modeCoeff k‖) := by
  simpa using modeCoeff_weighted_summable 0

/-- The single-mode witness field. -/
def modeField : SpatialField := fun x ↦
  NavierStokes.PeriodicIntegration.toSpace
    (fun _ ↦ (torusScalarSeries modeCoeff x).re)

theorem modeField_component (i : Fin 3) :
    (fun x ↦ ((modeField x i : ℝ) : ℂ)) = torusScalarSeries modeCoeff :=
  funext fun x ↦ Complex.conj_eq_iff_re.mp
    (NSFormalization.Section3.T11.torusScalarSeries_conj modeCoeff_neg x)

theorem modeField_smoothPeriodic : SmoothPeriodicT modeField := by
  constructor
  · have hpi : ContDiff ℝ ∞ (fun x : Space ↦
        (fun _ ↦ (torusScalarSeries modeCoeff x).re :
          NavierStokes.PeriodicIntegration.Coords)) :=
      contDiff_pi.mpr fun _ ↦ Complex.reCLM.contDiff.comp
        (NSFormalization.Section3.T11.torusScalarSeries_contDiff modeCoeff_weighted_summable)
    exact (NavierStokes.PeriodicIntegration.toSpace :
      NavierStokes.PeriodicIntegration.Coords →L[ℝ] Space).contDiff.comp hpi
  · intro x j
    show NavierStokes.PeriodicIntegration.toSpace
        (fun _ ↦ (torusScalarSeries modeCoeff (x + coordinateVector j)).re) =
      NavierStokes.PeriodicIntegration.toSpace
        (fun _ ↦ (torusScalarSeries modeCoeff x).re)
    congr 1
    funext _
    rw [NSFormalization.Section3.T11.torusScalarSeries_periodic modeCoeff x j]

theorem modeField_coeff (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((modeField x i : ℝ) : ℂ)) k = modeCoeff k := by
  rw [modeField_component i,
    NSFormalization.Section3.T11.torusScalarSeries_coeff modeCoeff_summable k]

theorem modeField_meanZero : IsMeanZeroT modeField := by
  have hint : Integrable (torusLift modeField) periodicTorusMeasure :=
    (memLp_torusLift_vector modeField_smoothPeriodic.1.continuous 1).integrable le_rfl
  have hz : ∀ i : Fin 3, meanT modeField i = 0 := by
    intro i
    have h := periodicFourierCoeff_zero_eq_mean_component hint i
    rw [modeField_coeff i 0, modeCoeff_zero] at h
    exact_mod_cast h.symm
  show meanT modeField = 0
  apply WithLp.ofLp_injective 2
  funext i
  simpa using hz i

theorem modeField_memHmVector : MemPeriodicHmVector 2 modeField := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum ((2 : ℕ) : ℝ)
    modeField_smoothPeriodic.1 modeField_smoothPeriodic.2
  exact ⟨modeField_smoothPeriodic.2,
    memLp_torusLift_vector modeField_smoothPeriodic.1.continuous 2,
    by rw [periodicSobolevENorm_eq hA]; exact enorm_ne_top⟩

theorem modeField_ne_zero : modeField ≠ 0 := by
  intro h
  have h1 := modeField_coeff 0 modeFreq
  rw [modeCoeff_modeFreq, h] at h1
  rw [show (fun x : Space ↦ (((0 : SpatialField) x 0 : ℝ) : ℂ)) = (fun _ : Space ↦ (0 : ℂ)) from
    rfl, periodicFourierCoeff_const] at h1
  simp at h1

/-- Non-vacuity: a field different from zero satisfies every hypothesis of the
three proved fields. -/
example : modeField ≠ 0 ∧ SmoothPeriodicT modeField ∧ IsMeanZeroT modeField ∧
    MemPeriodicHmVector 2 modeField :=
  ⟨modeField_ne_zero, modeField_smoothPeriodic, modeField_meanZero, modeField_memHmVector⟩

/-- The conclusion of `lambda_exists` at the single mode. -/
example : ∃ Lv : SpatialField, IsPeriodicLambda modeField Lv :=
  lambda_exists modeField modeField_smoothPeriodic

/-! ## 3. Transitive axioms of the witness facts -/

#print axioms modeFreq_ne_zero
#print axioms modeCoeff_neg
#print axioms modeCoeff_zero
#print axioms modeCoeff_modeFreq
#print axioms modeCoeff_weighted_summable
#print axioms modeCoeff_summable
#print axioms modeField_component
#print axioms modeField_smoothPeriodic
#print axioms modeField_coeff
#print axioms modeField_meanZero
#print axioms modeField_memHmVector
#print axioms modeField_ne_zero

end NSFormalization.Section3.T12
