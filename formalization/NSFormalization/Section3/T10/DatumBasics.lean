import NSFormalization.Section3.T10.PeriodicData

/-!
# Elementary coefficient-side facts for periodic data

This module proves uniqueness and conjugate symmetry of the weighted Fourier
datum and constructs the datum of the mean-zero part by deleting its zero
mode.  The only analytic input beyond `PeriodicData` is the integrability
conjunct of `IsPeriodicDatum`.
-/

noncomputable section

namespace NSFormalization.Section3.T10

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal BigOperators ComplexConjugate

local instance unitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Every complexified scalar component of an integrable torus-valued field
is integrable. -/
theorem IsPeriodicDatum.integrable_component {s : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) (i : Fin 3) :
    Integrable (torusLift (fun x ↦ ((z x i : ℝ) : ℂ))) periodicTorusMeasure := by
  change Integrable (fun y : PeriodicTorus ↦ ((torusLift z y i : ℝ) : ℂ))
    periodicTorusMeasure
  simpa [Function.comp_def] using
    (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).integrable_comp hA.2.1

/-- The integral of a multivariate Fourier monomial is one at frequency zero
and zero at every other frequency. -/
theorem integral_mFourier (k : PeriodicFrequency) :
    ∫ x : PeriodicTorus, UnitAddTorus.mFourier k x ∂periodicTorusMeasure =
      if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 3))) (0 : PeriodicFrequency) k
  simpa [ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    RCLike.inner_apply, eq_comm] using h

/-- The Fourier coefficient of a constant on the probability torus is
supported at frequency zero. -/
theorem periodicFourierCoeff_const (c : ℂ) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun _ ↦ c) k = if k = 0 then c else 0 := by
  change UnitAddTorus.mFourierCoeff (fun _ : PeriodicTorus ↦ c) k = _
  unfold UnitAddTorus.mFourierCoeff
  rw [integral_smul_const,
    integral_mFourier]
  simp

/-- Fourier coefficients commute with subtraction for integrable scalar
fields. -/
theorem periodicFourierCoeff_sub {f g : Space → ℂ}
    (hf : Integrable (torusLift f) periodicTorusMeasure)
    (hg : Integrable (torusLift g) periodicTorusMeasure)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x - g x) k =
      periodicFourierCoeff f k - periodicFourierCoeff g k := by
  change Integrable (torusLift f)
    (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) at hf
  change Integrable (torusLift g)
    (Measure.pi fun _ : Fin 3 ↦ AddCircle.haarAddCircle) at hg
  change UnitAddTorus.mFourierCoeff
      (fun y : PeriodicTorus ↦ torusLift f y - torusLift g y) k =
    UnitAddTorus.mFourierCoeff (torusLift f) k -
      UnitAddTorus.mFourierCoeff (torusLift g) k
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_sub]
  rw [integral_sub]
  · unfold MeasureTheory.MeasureSpace.pi
    have hm : AEStronglyMeasurable
        (fun x : PeriodicTorus ↦ UnitAddTorus.mFourier (-k) x)
        periodicTorusMeasure :=
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    have hb : ∀ᵐ x : PeriodicTorus ∂periodicTorusMeasure,
        ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      filter_upwards with x
      simpa only [UnitAddTorus.mFourier_norm] using
        (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
    convert hf.bdd_smul (φ := fun x ↦ UnitAddTorus.mFourier (-k) x) 1 hm hb using 1 <;>
      rfl
  · unfold MeasureTheory.MeasureSpace.pi
    have hm : AEStronglyMeasurable
        (fun x : PeriodicTorus ↦ UnitAddTorus.mFourier (-k) x)
        periodicTorusMeasure :=
      (UnitAddTorus.mFourier (-k)).continuous.aestronglyMeasurable
    have hb : ∀ᵐ x : PeriodicTorus ∂periodicTorusMeasure,
        ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      filter_upwards with x
      simpa only [UnitAddTorus.mFourier_norm] using
        (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
    convert hg.bdd_smul (φ := fun x ↦ UnitAddTorus.mFourier (-k) x) 1 hm hb using 1 <;>
      rfl

/-- At frequency zero, the scalar Fourier coefficient is the corresponding
coordinate of the vector-valued torus mean. -/
theorem periodicFourierCoeff_zero_eq_mean_component {z : SpatialField}
    (hz : Integrable (torusLift z) periodicTorusMeasure) (i : Fin 3) :
    periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) 0 =
      ((meanT z i : ℝ) : ℂ) := by
  have hreal : Integrable (fun y : PeriodicTorus ↦ torusLift z y i)
      periodicTorusMeasure := hz.eval_piLp i
  change UnitAddTorus.mFourierCoeff
      (fun y : PeriodicTorus ↦ ((torusLift z y i : ℝ) : ℂ)) 0 = _
  unfold UnitAddTorus.mFourierCoeff
  simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
  rw [meanT, MeasureTheory.eval_integral_piLp (fun j ↦ hz.eval_piLp j) i]
  simpa only [Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.integral_comp_comm hreal

/-- The ambient coefficient vector consisting only of the zero mode of `A`. -/
def periodicZeroModePart (A : PeriodicVectorData) : PeriodicVectorData :=
  WithLp.toLp 2 (fun i ↦ lp.single 2 (0 : PeriodicFrequency) (A i 0))

/-- Deleting the zero mode preserves conjugate-reflection symmetry. -/
theorem periodicZeroModePart_mem (A : realPeriodicSubmodule) :
    periodicZeroModePart A.1 ∈ realPeriodicSubmodule := by
  intro i k
  change (lp.single 2 (0 : PeriodicFrequency) (A.1 i 0) : PeriodicScalarData) (-k) =
    star ((lp.single 2 (0 : PeriodicFrequency) (A.1 i 0) : PeriodicScalarData) k)
  by_cases hk : k = 0
  · subst k
    simpa using A.2 i 0
  · rw [lp.single_apply_ne 2 0 _ (neg_ne_zero.mpr hk),
      lp.single_apply_ne 2 0 _ hk]
    simp

/-- Weighted Fourier data representing the same physical field are equal. -/
theorem datum_unique :
    ∀ (s : ℝ) (z : SpatialField) (A B : PeriodicSobolev s),
      IsPeriodicDatum s z A → IsPeriodicDatum s z B → A = B := by
  intro s z A B hA hB
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  rw [hA.2.2 i k, hB.2.2 i k]

/-- Every periodic datum has the conjugate-reflection symmetry built into the
real coefficient carrier. -/
theorem datum_real :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i (-k) = star (A.1 i k) := by
  intro s z A _ i k
  exact A.2 i k

/-- Removing the physical mean is represented at every Sobolev order by
deleting the zero frequency of the weighted datum. -/
theorem meanZero_datum :
    ∀ (s : ℝ) (z : SpatialField) (A : PeriodicSobolev s),
      IsPeriodicDatum s z A →
        ∃ B : PeriodicSobolev s,
          IsPeriodicDatum s (meanZeroPartT z) B ∧ B ∈ meanZeroPeriodicSobolev s := by
  intro s z A hA
  let C : PeriodicSobolev s := ⟨periodicZeroModePart A.1, periodicZeroModePart_mem A⟩
  refine ⟨A - C, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x j
      simp only [meanZeroPartT]
      rw [hA.1 x j]
    · change Integrable
        (fun y : PeriodicTorus ↦ torusLift z y - meanT z) periodicTorusMeasure
      exact hA.2.1.sub (integrable_const (meanT z : Space))
    · intro i k
      have hi := hA.integrable_component i
      have hc : Integrable
          (torusLift (fun _ : Space ↦ ((meanT z i : ℝ) : ℂ)))
          periodicTorusMeasure := integrable_const _
      rw [show (A - C).1 i k = A.1 i k - C.1 i k by rfl]
      rw [hA.2.2 i k]
      change _ - (lp.single 2 (0 : PeriodicFrequency) (A.1 i 0) : PeriodicScalarData) k = _
      rw [show periodicFourierCoeff
          (fun x ↦ (((meanZeroPartT z x) i : ℝ) : ℂ)) k =
          periodicFourierCoeff
              (fun x ↦ ((z x i : ℝ) : ℂ) - ((meanT z i : ℝ) : ℂ)) k by
            congr 1
            funext x
            simp [meanZeroPartT]]
      rw [periodicFourierCoeff_sub hi hc k, periodicFourierCoeff_const]
      by_cases hk : k = 0
      · subst k
        rw [lp.single_apply_self]
        rw [hA.2.2 i 0, periodicFourierCoeff_zero_eq_mean_component hA.2.1 i]
        simp [periodicFrequencyWeight]
      · rw [lp.single_apply_ne 2 0 _ hk]
        simp [hk]
  · intro i
    change A.1 i 0 -
      (lp.single 2 (0 : PeriodicFrequency) (A.1 i 0) : PeriodicScalarData) 0 = 0
    rw [lp.single_apply_self, sub_self]

/-! The hypotheses are inhabited: the zero physical field has the zero datum
at every Sobolev order. -/

example (s : ℝ) :
    IsPeriodicDatum s (0 : SpatialField) (0 : PeriodicSobolev s) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    rfl
  · change Integrable (fun _ : PeriodicTorus ↦ (0 : Space)) periodicTorusMeasure
    exact integrable_const 0
  · intro i k
    change (0 : ℂ) = (periodicFrequencyWeight k) ^ (s / 2) •
      periodicFourierCoeff (fun _ : Space ↦ (0 : ℂ)) k
    rw [periodicFourierCoeff_const]
    simp

end NSFormalization.Section3.T10
