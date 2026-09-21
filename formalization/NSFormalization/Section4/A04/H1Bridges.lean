import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Section4.A04.ForceShift
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section3.T22.CutoffMultiplierField
import NSFormalization.Section3.T22.OrderZero
import NSFormalization.Paper1.PeriodicScalarForceEndpoints

/-!
# Exact whole-space H¹/H² energies and compact shifted-force caps

For a smooth compactly supported real vector field, the registered angular
Bessel norm has the exact physical normalization

* `H¹² = L²² + ∇²`, and
* `H²² = L²² + 2 ∇² + ∇²²`.

Thus the useful recurrence is `H²² = H¹² + ∇² + ∇²²`; with the registered
weight `(1 + |ξ|²)²`, the second formula is not `H¹² + ∇²²`.

The second part packages the elementary compactness fact needed by Route B:
one fixed force has a finite `L²` cap on every family of translated unit
windows with restart time in a compact interval.
-/

noncomputable section

namespace NSFormalization.Section4.A04

open Set MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Paper1.PeriodicScalarForceEndpoints
open NSFormalization.Section4.A02
open NavierStokesR3.HarmonicTestFunctionals (partialCLM partialCLM_apply)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Homogeneous
  (compactSchwartzComponents compactSchwartzComponents_apply contDiff_component
    hasCompactSupport_component)
open scoped ContDiff ENNReal SchwartzMap BigOperators

/-! ## 1. Physical derivative energies -/

/-- The physical squared `L²(R³)` energy of a real three-vector field. -/
def l2EnergyR (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, ∫ x : Space, ‖((z x i : ℝ) : ℂ)‖ ^ 2

/-- The physical squared Frobenius `L²(R³)` energy of the spatial gradient. -/
def gradientEnergyR (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ x : Space, ‖spatialPartial j (fun y : Space => ((z y i : ℝ) : ℂ)) x‖ ^ 2

/-- The physical squared `L²(R³)` energy of all ordered second partials. -/
def hessianEnergyR (z : SpatialField) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    ∫ x : Space,
      ‖spatialPartial k (spatialPartial j (fun y : Space => ((z y i : ℝ) : ℂ))) x‖ ^ 2

/-! ## 2. The compact Schwartz datum and its registered norm -/

/-- Conjugate reflection sends an angular Schwartz datum to the datum of the
pointwise conjugate Schwartz function. -/
theorem realSymmetry_angularDatum (s : ℝ) (φ : SchwartzMap Space ℂ) :
    realSymmetry (angularDatum s φ) = angularDatum s (conjugateSchwartz φ) :=
  NSFormalization.Section3.T22.realSymmetry_angularDatum s φ

/-- The normalized angular datum of a compact smooth real vector field. -/
def compactAngularDatumR (s : ℝ) {z : SpatialField} (hz : ContDiff ℝ ∞ z)
    (hc : HasCompactSupport z) : RealVectorSobolev s :=
  WithLp.toLp 2 fun i =>
    ⟨angularDatum s (compactSchwartzComponents hz hc i),
      (mem_realSubspace_iff s _).mpr (by
        rw [realSymmetry_angularDatum]
        congr 1
        ext x
        rw [conjugateSchwartz_apply, compactSchwartzComponents_apply,
          Complex.conj_ofReal])⟩

@[simp] theorem compactAngularDatumR_apply (s : ℝ) {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) (i : Fin 3) :
    ((compactAngularDatumR s hz hc i : RealSobolevHilbert s) : FourierData) =
      angularDatum s (compactSchwartzComponents hz hc i) := rfl

/-- The compact angular datum represents the original physical field. -/
theorem isSobolevDatum_compactAngularDatumR (s : ℝ) {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    NSFormalization.Section4.D01.IsSobolevDatum s z (compactAngularDatumR s hz hc) := by
  intro i ψ
  change angularRealization s (angularDatum s (compactSchwartzComponents hz hc i)) ψ = _
  rw [angularRealization_datum, SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [compactSchwartzComponents_apply, smul_eq_mul]

/-- Its real norm squared is the sum of the three scalar angular Fourier
energies. -/
theorem compactAngularDatumR_norm_sq (s : ℝ) {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    ‖compactAngularDatumR s hz hc‖ ^ 2 =
      ∑ i : Fin 3, angularSobolevSq s (fun x => ((z x i : ℝ) : ℂ)) := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖angularDatum s (compactSchwartzComponents hz hc i)‖ ^ 2 = _
  rw [norm_angularDatum, angularSobolevNorm,
    Real.sq_sqrt (angularSobolevSq_nonneg s _)]
  rfl

/-- Exact registered-norm/Fourier-energy identity for every real order on the
compact smooth core. -/
theorem sobolevENorm_toReal_sq_eq_angular (s : ℝ) {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (sobolevENorm s z).toReal ^ 2 =
      ∑ i : Fin 3, angularSobolevSq s (fun x => ((z x i : ℝ) : ℂ)) := by
  rw [NSFormalization.Section4.A03.sobolevENorm_eq
    (isSobolevDatum_compactAngularDatumR s hz hc), toReal_enorm]
  exact compactAngularDatumR_norm_sq s hz hc

/-! ## 3. Orders one and two -/

/-- Scalar order two in the registered angular convention. -/
theorem angularSobolevSq_two_eq_physical (φ : SchwartzMap Space ℂ) :
    angularSobolevSq 2 (φ : Space → ℂ) =
      (∫ x : Space, ‖φ x‖ ^ 2) +
        2 * (∑ j : Fin 3, ∫ x : Space, ‖partialCLM j φ x‖ ^ 2) +
        (∑ j : Fin 3, ∑ k : Fin 3,
          ∫ x : Space, ‖partialCLM k (partialCLM j φ) x‖ ^ 2) := by
  have h₁ (ψ : SchwartzMap Space ℂ) :
      angularSobolevSq 1 (ψ : Space → ℂ) =
        (∫ x : Space, ‖ψ x‖ ^ 2) +
          ∑ j : Fin 3, ∫ x : Space, ‖partialCLM j ψ x‖ ^ 2 := by
    simpa only [zero_add, angularSobolevSq_zero_eq_physical] using
      angular_succ_energy 0 ψ
  rw [show (2 : ℝ) = 1 + 1 by norm_num, angular_succ_energy]
  simp_rw [h₁]
  rw [Finset.sum_add_distrib]
  ring

/-- The registered whole-space `H¹` norm is exactly value plus gradient
energy on the compact smooth core. -/
theorem sobolevENorm_one_toReal_sq_eq {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (sobolevENorm 1 z).toReal ^ 2 = l2EnergyR z + gradientEnergyR z := by
  rw [sobolevENorm_toReal_sq_eq_angular 1 hz hc]
  simp_rw [angularSobolevSq_one_eq_physical
    (contDiff_component hz _) (hasCompactSupport_component hc _)]
  simp only [l2EnergyR, gradientEnergyR, Finset.sum_add_distrib]

/-- The registered whole-space `H²` norm has the exact Bessel normalization
`L² + 2∇² + ∇²²`. -/
theorem sobolevENorm_two_toReal_sq_eq {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (sobolevENorm 2 z).toReal ^ 2 =
      l2EnergyR z + 2 * gradientEnergyR z + hessianEnergyR z := by
  rw [sobolevENorm_toReal_sq_eq_angular 2 hz hc]
  change (∑ i : Fin 3,
    angularSobolevSq 2 (compactSchwartzComponents hz hc i : Space → ℂ)) = _
  simp_rw [angularSobolevSq_two_eq_physical]
  have hcomp (i : Fin 3) :
      (compactSchwartzComponents hz hc i : Space → ℂ) =
        fun y : Space => ((z y i : ℝ) : ℂ) := by
    funext y
    exact compactSchwartzComponents_apply hz hc i y
  have hpartial (i j : Fin 3) :
      (partialCLM j (compactSchwartzComponents hz hc i) : Space → ℂ) =
        spatialPartial j (fun y : Space => ((z y i : ℝ) : ℂ)) := by
    funext y
    rw [partialCLM_apply, hcomp]
  simp only [l2EnergyR, gradientEnergyR, hessianEnergyR,
    compactSchwartzComponents_apply, partialCLM_apply, Finset.sum_add_distrib,
    Finset.mul_sum, hcomp, hpartial]

/-- Equivalent recurrence form of the order-two identity. -/
theorem sobolevENorm_two_eq_one_add_gradient_hessian {z : SpatialField}
    (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (sobolevENorm 2 z).toReal ^ 2 =
      (sobolevENorm 1 z).toReal ^ 2 + gradientEnergyR z + hessianEnergyR z := by
  rw [sobolevENorm_two_toReal_sq_eq hz hc, sobolevENorm_one_toReal_sq_eq hz hc]
  ring

/-! ## 4. The compact-window force cap -/

/-- The actual supremum of the force's spatial `L²` norm on `[0,S+1]`. -/
def forceL2CapR (f : SpaceTimeField) (S : ℝ) : ℝ≥0∞ :=
  ⨆ t : Icc (0 : ℝ) (S + 1), eLpNorm (fun x : Space => f (t.1, x)) 2 volume

/-- A nonnegative-time slice of a whole-space force is globally smooth in
the spatial variables. -/
theorem forceSlice_contDiffR {f : SpaceTimeField}
    (hf : NSFormalization.Section4.A02.MemForceR f)
    {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ∞ (fun x : Space => f (t, x)) := by
  rw [← contDiffOn_univ]
  exact hf.1.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

/-- The cap is finite, by continuity of any registered order-zero datum path
on the compact interval. -/
theorem forceL2CapR_ne_top {f : SpaceTimeField}
    (hf : NSFormalization.Section4.A02.MemForceR f)
    {S : ℝ} (_hS : 0 ≤ S) : forceL2CapR f S ≠ ⊤ := by
  obtain ⟨G, hG, hGc, _hG1, _hG2⟩ := hf.2 0
  have hcont : ContinuousOn G (Icc (0 : ℝ) (S + 1)) :=
    (hGc.continuousOn.mono fun t ht => ht.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hcap : forceL2CapR f S ≤ ENNReal.ofReal C := by
    apply iSup_le
    intro t
    have hdatum := hG t.1 t.2.1
    have hdatum' : NSFormalization.Section4.D01.IsSobolevDatum 0
        (fun x : Space => f (t.1, x)) (G t.1) := by
      intro i ψ
      simpa only [Nat.cast_zero] using hdatum i ψ
    have hmem := memLp_of_isSobolevDatum (forceSlice_contDiffR hf t.2.1) hdatum
    rw [← NSFormalization.Section3.T22.sobolevENorm_zero_eq_eLpNorm hmem]
    change NSFormalization.Section4.D01.sobolevENorm 0
      (fun x : Space => f (t.1, x)) ≤ ENNReal.ofReal C
    have he : NSFormalization.Section4.D01.sobolevENorm 0
        (fun x : Space => f (t.1, x)) = ‖G t.1‖ₑ :=
      NSFormalization.Section4.A03.sobolevENorm_eq hdatum'
    calc
      NSFormalization.Section4.D01.sobolevENorm 0 (fun x : Space => f (t.1, x))
          = ‖G t.1‖ₑ := he
      _ = ENNReal.ofReal ‖G t.1‖ := (ofReal_norm (G t.1)).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (hC t t.2)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap

/-- Every slice in every translated unit window is controlled by the one
cap on `[0,S+1]`. -/
theorem force_slice_le_forceL2CapR {f : SpaceTimeField} {S t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) 1) :
    eLpNorm (fun x : Space => f (t₀ + t, x)) 2 volume ≤ forceL2CapR f S := by
  let r : Icc (0 : ℝ) (S + 1) :=
    ⟨t₀ + t, by constructor <;> linarith [ht₀.1, ht₀.2, ht.1, ht.2]⟩
  exact le_iSup (fun r : Icc (0 : ℝ) (S + 1) =>
    eLpNorm (fun x : Space => f (r.1, x)) 2 volume) r

/-- Literal iterated-supremum form of the preceding cap. -/
theorem iSup_shifted_force_slice_le_forceL2CapR {f : SpaceTimeField} {S : ℝ} :
    (⨆ t₀ : Icc (0 : ℝ) S, ⨆ t : Icc (0 : ℝ) 1,
      eLpNorm (fun x : Space => f (t₀.1 + t.1, x)) 2 volume) ≤ forceL2CapR f S := by
  apply iSup_le
  intro t₀
  apply iSup_le
  intro t
  exact force_slice_le_forceL2CapR t₀.2 t.2

/-- The consumer-facing statement for the translated force itself. -/
theorem timeShift_force_slice_le_forceL2CapR {f : SpaceTimeField} {S t₀ t : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) 1) :
    eLpNorm (fun x : Space => timeShift t₀ f (t, x)) 2 volume ≤ forceL2CapR f S := by
  simpa only [timeShift, add_comm] using force_slice_le_forceL2CapR (f := f) ht₀ ht

end NSFormalization.Section4.A04
