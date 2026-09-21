import NSFormalization.Section3.T11.Restart
import NSFormalization.Section3.T17.Sobolev
import NSFormalization.Paper1.PeriodicHigherSobolev

/-!
# Exact periodic H¹/H² energies and compact shifted-force caps

For the registered torus Bessel weight, smooth periodic real vector fields
satisfy `H¹² = L²² + ∇²` and `H²² = L²² + 2∇² + ∇²²`.  The final section
records precisely what the Route B restart argument may use after translating
a torus force: global smoothness, spatial periodicity, and a common finite
`L²` cap.  It deliberately does not claim that a positive translate remains
in `forceClassT`, whose compact time support must lie strictly in `(0,∞)`.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial cubeIntegral)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12 (periodicLpENorm)
open scoped ContDiff ENNReal BigOperators

/-! ## 1. Physical derivative energies on the unit torus -/

/-- The physical squared `L²(T³)` energy, in the normalized cube convention. -/
def periodicL2Energy (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, cubeIntegral
    (fun x : Space => ‖((z x i : ℝ) : ℂ)‖ ^ 2)

/-- The physical squared Frobenius gradient energy on `T³`. -/
def periodicGradientEnergy (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, cubeIntegral
    (fun x : Space => ‖spatialPartial j (fun y : Space => ((z y i : ℝ) : ℂ)) x‖ ^ 2)

/-- The physical energy of all ordered second spatial partials on `T³`. -/
def periodicHessianEnergy (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    cubeIntegral (fun x : Space =>
      ‖spatialPartial k (spatialPartial j (fun y : Space => ((z y i : ℝ) : ℂ))) x‖ ^ 2)

/-! ## 2. Registered periodic norms -/

/-- At every natural order, the registered vector norm squared is the sum of
the three exact scalar integer Bessel energies. -/
theorem periodicSobolevENorm_nat_toReal_sq_eq (m : ℕ) {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm (m : ℝ) z).toReal ^ 2 =
      ∑ i : Fin 3, NSFormalization.Paper1.periodicIntegerEnergy m
        (fun x : Space => ((z x i : ℝ) : ℂ)) := by
  obtain ⟨A, hA⟩ := smooth_periodic_datum (m : ℝ) hz hp
  rw [periodicSobolevENorm_eq hA, toReal_enorm]
  change ‖A.1‖ ^ 2 = _
  rw [NSFormalization.Section3.T17.norm_datum_eq_sqrt (m : ℝ) hz hA,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
      NSFormalization.Section3.T17.periodicSobolevSq_nonneg (m : ℝ)
        (fun x : Space => ((z x i : ℝ) : ℂ)))]
  apply Finset.sum_congr rfl
  intro i _
  apply NSFormalization.Paper1.periodicSobolevSq_nat m
  · exact (Complex.ofRealCLM.contDiff.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hz)).of_le (by simp)
  · intro x j
    exact congrArg (fun y : Space => ((y i : ℝ) : ℂ)) (hp x j)

/-- The registered periodic `H¹` norm is exactly value plus gradient energy. -/
theorem periodicSobolevENorm_one_toReal_sq_eq {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 1 z).toReal ^ 2 =
      periodicL2Energy z + periodicGradientEnergy z := by
  have h := periodicSobolevENorm_nat_toReal_sq_eq 1 hz hp
  norm_num at h
  rw [h]
  simp only [NSFormalization.Paper1.periodicH1Energy, periodicL2Energy,
    periodicGradientEnergy, Finset.sum_add_distrib]

/-- The registered periodic `H²` norm has the exact Bessel normalization
`L² + 2∇² + ∇²²`. -/
theorem periodicSobolevENorm_two_toReal_sq_eq {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 2 z).toReal ^ 2 =
      periodicL2Energy z + 2 * periodicGradientEnergy z + periodicHessianEnergy z := by
  have h := periodicSobolevENorm_nat_toReal_sq_eq 2 hz hp
  norm_num at h
  rw [h]
  simp only [NSFormalization.Paper1.periodicH2Energy, periodicL2Energy,
    periodicGradientEnergy, periodicHessianEnergy, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- Equivalent recurrence form of the order-two identity. -/
theorem periodicSobolevENorm_two_eq_one_add_gradient_hessian {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    (periodicSobolevENorm 2 z).toReal ^ 2 =
      (periodicSobolevENorm 1 z).toReal ^ 2 +
        periodicGradientEnergy z + periodicHessianEnergy z := by
  rw [periodicSobolevENorm_two_toReal_sq_eq hz hp,
    periodicSobolevENorm_one_toReal_sq_eq hz hp]
  ring

/-! ## 3. The compact-window force cap -/

/-- The actual supremum of the periodic spatial `L²` norm on `[0,S+1]`. -/
def forceL2CapT (f : SpaceTimeField) (S : ℝ) : ℝ≥0∞ :=
  ⨆ t : Icc (0 : ℝ) (S + 1), periodicLpENorm 2 (fun x : Space => f (t.1, x))

/-- The cap of a torus test force is finite. -/
theorem forceL2CapT_ne_top {f : SpaceTimeField} (hf : MemForceT f)
    {S : ℝ} (_hS : 0 ≤ S) : forceL2CapT f S ≠ ⊤ := by
  obtain ⟨G, hG, hGc, _hcompact, _hmeas, _hpath, _hLp⟩ := force_coefficient_path hf 0
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S + 1)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hcap : forceL2CapT f S ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro t
    have hdatum := hG t.1
    have hs : ContDiff ℝ ∞ (fun x : Space => f (t.1, x)) :=
      hf.1.comp (contDiff_const.prodMk contDiff_id)
    have hp : IsPeriodicSpatial (fun x : Space => f (t.1, x)) :=
      fun x i => hf.2.1 t.1 (mem_univ _) x i
    change eLpNorm (torusLift (fun x : Space => f (t.1, x))) 2 periodicTorusMeasure ≤ _
    rw [← sobolevENorm_zero_eq hs hp]
    have hdatum' : IsPeriodicDatum (0 : ℝ) (fun x : Space => f (t.1, x)) (G t.1) := by
      refine ⟨hdatum.1, hdatum.2.1, ?_⟩
      intro i k
      simpa only [Nat.cast_zero] using hdatum.2.2 i k
    have he : periodicSobolevENorm (0 : ℝ) (fun x : Space => f (t.1, x)) = ‖G t.1‖ₑ :=
      periodicSobolevENorm_eq hdatum'
    calc
      periodicSobolevENorm 0 (fun x : Space => f (t.1, x)) = ‖G t.1‖ₑ := he
      _ = ENNReal.ofReal ‖G t.1‖ := (ofReal_norm (G t.1)).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC t.1 t.2)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap

/-- Every slice in every translated unit window is controlled by the common
cap on `[0,S+1]`. -/
theorem force_slice_le_forceL2CapT {f : SpaceTimeField} {S t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) 1) :
    periodicLpENorm 2 (fun x : Space => f (t₀ + t, x)) ≤ forceL2CapT f S := by
  let r : Icc (0 : ℝ) (S + 1) :=
    ⟨t₀ + t, by constructor <;> linarith [ht₀.1, ht₀.2, ht.1, ht.2]⟩
  exact le_iSup (fun r : Icc (0 : ℝ) (S + 1) =>
    periodicLpENorm 2 (fun x : Space => f (r.1, x))) r

/-- Literal iterated-supremum form of the periodic cap. -/
theorem iSup_shifted_force_slice_le_forceL2CapT {f : SpaceTimeField} {S : ℝ} :
    (⨆ t₀ : Icc (0 : ℝ) S, ⨆ t : Icc (0 : ℝ) 1,
      periodicLpENorm 2 (fun x : Space => f (t₀.1 + t.1, x))) ≤ forceL2CapT f S := by
  apply iSup_le
  intro t₀
  apply iSup_le
  intro t
  exact force_slice_le_forceL2CapT t₀.2 t.2

/-- The translated force obeys the same unit-window cap. -/
theorem timeShiftT_force_slice_le_forceL2CapT {f : SpaceTimeField} {S t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) 1) :
    periodicLpENorm 2 (fun x : Space => timeShiftT t₀ f (t, x)) ≤ forceL2CapT f S := by
  simpa only [timeShiftT, NSFormalization.Section4.A04.timeShift, add_comm] using
    force_slice_le_forceL2CapT (f := f) ht₀ ht

/-- The exact regularity package needed by Route B after a torus time shift.
No `MemForceT (timeShiftT t₀ f)` conclusion is asserted. -/
theorem timeShiftT_smooth_periodic {f : SpaceTimeField} (hf : MemForceT f) (t₀ : ℝ) :
    ContDiff ℝ ∞ (timeShiftT t₀ f) ∧ IsPeriodicOn univ (timeShiftT t₀ f) :=
  ⟨timeShiftT_contDiff hf.1 t₀, timeShiftT_periodic hf.2.1 t₀⟩

end NSFormalization.Section3.T11
