import NSFormalization.Section4.R44.Endpoint
import NSFormalization.Section4.R44.EnergyIdentity
import NSFormalization.Section4.R44.TrilinearJ
import NSFormalization.Section4.R44.Pieces

/-!
# R44 row S1d (adapted from lane 228): Young absorption for the `J`-weighted energy identity

The derivative function below is the explicit value from `energy_identity` on
the open classical lifespan and zero elsewhere.  Its local integrability does
not require separately developing continuity for every displayed pairing:
uniqueness of the derivative identifies it on the open interval with the
continuous one-sided derivative of the smooth half-order datum path.
-/
noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open scoped ContDiff RealInnerProductSpace

namespace NSFormalization.Section4.R44

open A02 (SpatialField SpaceTimeField ClassicalSolutionR)
open D01

/-! ## Slice data and the sibling-pairing bridge -/

/-- The standard advection package on every interior classical slice. -/
def advectionJDatumPath {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    AdvectionJDatum (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩) where
  velocity_memHInfty := C01.velocity_slice_memHInfty w ⟨ht.1.le, ht.2⟩
  advectionNegHalf := energyDatum (-1 / 2) (fun x => advection w.velocity t x)
  advectionNegHalf_isDatum := by
    change IsSobolevDatum (-1 / 2) (fun x => advection w.velocity t x) _
    exact energyDatum_isDatum (advection_slice_smoothL2 w ht)

/-- The energy-identity and trilinear modules use the same nonlinear pairing.
Datum uniqueness is the only bridge between their independently selected
negative-half-order representatives. -/
theorem energyAdvectionJPairing_eq {u f : SpatialField} (h : JWeightDatum u f)
    (ha : AdvectionJDatum h) (N : RealVectorSobolev (-1 / 2))
    (hN : IsSobolevDatum (-1 / 2) (advectionFieldJ u) N) :
    energyAdvectionJPairing h N = advectionJPairing h ha := by
  rw [energyAdvectionJPairing, advectionJPairing,
    isSobolevDatum_unique hN ha.advectionNegHalf_isDatum]

/-- The datum-uniqueness bridge specialized to the canonical solution path. -/
theorem energyAdvectionJPairing_path_eq {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f T)
    (hf : A02.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    energyAdvectionJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
        (energyDatum (-1 / 2) (fun x => advection w.velocity t x)) =
      advectionJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
        (advectionJDatumPath w hf t ht) := by
  apply energyAdvectionJPairing_eq
  change IsSobolevDatum (-1 / 2) (fun x => advection w.velocity t x) _
  exact energyDatum_isDatum (advection_slice_smoothL2 w ht)

/-! ## Universal constants -/

/-- The universal smallness threshold.  It is chosen so that
`2 * trilinearConstJ * thetaAbs = 1/2`. -/
def thetaAbs : ℝ := (4 * trilinearConstJ)⁻¹

/-- The coefficient of `ν Y²` after the cubic and `BY` terms are estimated. -/
def C₂Abs : ℝ := 2 * trilinearConstJ * thetaAbs + 1

/-- The coefficient of `ν⁻¹ B²` contributed by `BZ` and `BY`.
The harmless zero multiple records that this is universal with the same
trilinear constant fixed above. -/
def C₃Abs : ℝ := 3 + 0 * trilinearConstJ

theorem thetaAbs_pos : 0 < thetaAbs := by
  unfold thetaAbs
  positivity [trilinearConstJ_pos]

theorem trilinear_theta : 2 * trilinearConstJ * thetaAbs = 1 / 2 := by
  unfold thetaAbs
  (field_simp [ne_of_gt trilinearConstJ_pos]; ring)

theorem C₂Abs_nonneg : 0 ≤ C₂Abs := by
  rw [C₂Abs, trilinear_theta]
  norm_num

theorem C₂Abs_pos : 0 < C₂Abs := by
  rw [C₂Abs, trilinear_theta]
  norm_num

theorem C₃Abs_pos : 0 < C₃Abs := by
  unfold C₃Abs
  norm_num

theorem C₃Abs_nonneg : 0 ≤ C₃Abs := C₃Abs_pos.le

/-! ## The explicit derivative and pointwise Young absorption -/

/-- The value displayed by `energy_identity`, extended by zero outside
`Ioo 0 T`. -/
def rcritical2EnergyDerivative {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionR ν a f T) (hf : A02.MemForceR f) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) T then
    -2 * ν * Z (C01.slice w.velocity t) ^ 2 -
      2 * energyAdvectionJPairing
        (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
        (energyDatum (-1 / 2) (fun x => advection w.velocity t x)) +
      2 * forceJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
  else 0

theorem rcritical2EnergyDerivative_eq {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f T)
    (hf : A02.MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    rcritical2EnergyDerivative w hf t =
      -2 * ν * Z (C01.slice w.velocity t) ^ 2 -
        2 * energyAdvectionJPairing
          (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩)
          (energyDatum (-1 / 2) (fun x => advection w.velocity t x)) +
        2 * forceJPairing (jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩) := by
  rw [rcritical2EnergyDerivative, dite_eq_left ht]

/-- The explicit formula is the derivative of the paper's `Y²`. -/
theorem rcritical2EnergyDerivative_hasDerivAt {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (hf : A02.MemForceR f)
    (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => Y (C01.slice w.velocity s) ^ 2)
      (rcritical2EnergyDerivative w hf t) t := by
  rw [rcritical2EnergyDerivative_eq w hf ht]
  exact energy_identity hν hf w ht

/-- The scalar Young inequalities used in the paper, with all coefficients
fixed explicitly. -/
theorem young_absorption {ν Y₀ Z₀ B₀ A F : ℝ}
    (hν : 0 < ν) (hsmall : Y₀ ≤ thetaAbs * ν)
    (hA : |A| ≤ trilinearConstJ * Y₀ * (Y₀ ^ 2 + Z₀ ^ 2))
    (hF : |F| ≤ B₀ * (Y₀ + Z₀)) :
    (-2 * ν * Z₀ ^ 2 - 2 * A + 2 * F) + ν * Z₀ ^ 2 ≤
      C₂Abs * ν * Y₀ ^ 2 + C₃Abs * ν⁻¹ * B₀ ^ 2 := by
  have hC : 0 ≤ trilinearConstJ := trilinearConstJ_pos.le
  have hnu0 : ν ≠ 0 := ne_of_gt hν
  have hinv : ν * ν⁻¹ = 1 := mul_inv_cancel₀ hnu0
  have h2C : 0 ≤ 2 * trilinearConstJ := mul_nonneg (by norm_num) hC
  have hadvZ : 2 * trilinearConstJ * Y₀ * Z₀ ^ 2 ≤ ν / 2 * Z₀ ^ 2 := by
    have hsmallZ := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Z₀)
    have hscale := mul_le_mul_of_nonneg_left hsmallZ h2C
    calc
      2 * trilinearConstJ * Y₀ * Z₀ ^ 2 =
          (2 * trilinearConstJ) * (Y₀ * Z₀ ^ 2) := by ring
      _ ≤ (2 * trilinearConstJ) * (thetaAbs * ν * Z₀ ^ 2) := hscale
      _ = ν / 2 * Z₀ ^ 2 := by
        rw [show (2 * trilinearConstJ) * (thetaAbs * ν * Z₀ ^ 2) =
            (2 * trilinearConstJ * thetaAbs) * ν * Z₀ ^ 2 by ring,
          trilinear_theta]
        ring
  have hadvY : 2 * trilinearConstJ * Y₀ * Y₀ ^ 2 ≤
      (2 * trilinearConstJ * thetaAbs) * ν * Y₀ ^ 2 := by
    have hsmallY := mul_le_mul_of_nonneg_right hsmall (sq_nonneg Y₀)
    have hscale := mul_le_mul_of_nonneg_left hsmallY h2C
    calc
      2 * trilinearConstJ * Y₀ * Y₀ ^ 2 =
          (2 * trilinearConstJ) * (Y₀ * Y₀ ^ 2) := by ring
      _ ≤ (2 * trilinearConstJ) * (thetaAbs * ν * Y₀ ^ 2) := hscale
      _ = (2 * trilinearConstJ * thetaAbs) * ν * Y₀ ^ 2 := by ring
  have hBY : 2 * B₀ * Y₀ ≤ ν * Y₀ ^ 2 + ν⁻¹ * B₀ ^ 2 := by
    nlinarith [sq_nonneg (ν * Y₀ - B₀)]
  have hBZ : 2 * B₀ * Z₀ ≤ ν / 2 * Z₀ ^ 2 + 2 * ν⁻¹ * B₀ ^ 2 := by
    nlinarith [sq_nonneg (ν * Z₀ - 2 * B₀)]
  have hsignA : -2 * A ≤ 2 * |A| := by nlinarith [neg_le_abs A]
  have hsignF : 2 * F ≤ 2 * |F| := by nlinarith [le_abs_self F]
  have hraw :
      (-2 * ν * Z₀ ^ 2 - 2 * A + 2 * F) + ν * Z₀ ^ 2 ≤
        -ν * Z₀ ^ 2 +
          2 * trilinearConstJ * Y₀ * (Y₀ ^ 2 + Z₀ ^ 2) +
          2 * B₀ * (Y₀ + Z₀) := by
    nlinarith
  rw [C₂Abs, C₃Abs]
  norm_num only [zero_mul, add_zero]
  nlinarith

/-- Pointwise eq:Rcritical2 along a classical solution. -/
theorem rcritical2_pointwise {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hsmall : Y (C01.slice w.velocity t) ≤ thetaAbs * ν) :
    rcritical2EnergyDerivative w hf t + ν * Z (C01.slice w.velocity t) ^ 2 ≤
      C₂Abs * ν * Y (C01.slice w.velocity t) ^ 2 +
        C₃Abs * ν⁻¹ * B (C01.slice f t) ^ 2 := by
  let h := jWeightDatumPath w hf t ⟨ht.1.le, ht.2⟩
  let ha := advectionJDatumPath w hf t ht
  rw [rcritical2EnergyDerivative_eq w hf ht,
    energyAdvectionJPairing_path_eq w hf ht]
  apply young_absorption hν hsmall
  · exact advection_pairing_le h ha
  · exact force_pairing_le' h

/-! ## One locally integrable derivative function -/

/-- A continuous representative of the energy derivative on `Ico 0 T`, using
the one-sided derivative at zero. -/
def smoothRcritical2EnergyDerivative {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionR ν a f T) (t : ℝ) : ℝ :=
  2 * ⟪energyVelocity w (1 / 2) t,
    derivWithin (energyVelocity w (1 / 2)) (Ico (0 : ℝ) T) t⟫

theorem smoothRcritical2EnergyDerivative_continuousOn {ν T : ℝ}
    {a : SpatialField} {f : SpaceTimeField} (hν : 0 < ν)
    (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T) :
    ContinuousOn (smoothRcritical2EnergyDerivative w) (Ico (0 : ℝ) T) := by
  have hG := energyVelocity_smooth hν hf w (by norm_num : (1 / 2 : ℝ) ≤ 2)
  have hD := hG.continuousOn_derivWithin (uniqueDiffOn_Ico (0 : ℝ) T)
    (by simp : (1 : ℕ∞ω) ≤ ∞)
  exact continuousOn_const.mul (hG.continuousOn.inner hD)

/-- On the open lifespan, the explicit energy-identity formula equals the
continuous one-sided derivative representative. -/
theorem rcritical2EnergyDerivative_eq_smooth {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (hf : A02.MemForceR f)
    (w : ClassicalSolutionR ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    rcritical2EnergyDerivative w hf t = smoothRcritical2EnergyDerivative w t := by
  have henergy := rcritical2EnergyDerivative_hasDerivAt hν hf w ht
  have hsmooth := hasDerivAt_Y_sq hν hf w ht
  have heq := henergy.unique hsmooth
  rw [smoothRcritical2EnergyDerivative,
    derivWithin_of_mem_nhds (Ico_mem_nhds ht.1 ht.2)]
  exact heq

/-- The single explicit derivative function is integrable on every closed
presingular window. -/
theorem rcritical2EnergyDerivative_intervalIntegrable {ν T : ℝ}
    {a : SpatialField} {f : SpaceTimeField} (hν : 0 < ν)
    (hf : A02.MemForceR f) (w : ClassicalSolutionR ν a f T)
    {S : ℝ} (hS : 0 ≤ S) (hST : S < T) :
    IntervalIntegrable (rcritical2EnergyDerivative w hf) volume 0 S := by
  have hsub : Icc (0 : ℝ) S ⊆ Ico (0 : ℝ) T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans_lt hST⟩
  have hi : IntervalIntegrable (smoothRcritical2EnergyDerivative w) volume 0 S :=
    ContinuousOn.intervalIntegrable_of_Icc hS
      ((smoothRcritical2EnergyDerivative_continuousOn hν hf w).mono hsub)
  apply hi.congr_uIoo
  intro t ht
  rw [uIoo_of_le hS] at ht
  exact (rcritical2EnergyDerivative_eq_smooth hν hf w
    ⟨ht.1, ht.2.trans hST⟩).symm

/-! ## Exact S1 consumer package -/

/-- The exact S1 target, for arbitrary initial data.  In R44 it is consumed at
zero initial data through `RCritical2Differential`. -/
theorem rcritical2_differential {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (hf : A02.MemForceR f)
    (w : ClassicalSolutionR ν a f T) :
    ∃ E' : ℝ → ℝ,
      (∀ S, 0 ≤ S → S < T → IntervalIntegrable E' volume 0 S) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivAt (fun s => Y (C01.slice w.velocity s) ^ 2) (E' t) t ∧
        (Y (C01.slice w.velocity t) ≤ thetaAbs * ν →
          E' t + ν * Z (C01.slice w.velocity t) ^ 2 ≤
            C₂Abs * ν * Y (C01.slice w.velocity t) ^ 2 +
              C₃Abs * ν⁻¹ * B (C01.slice f t) ^ 2) := by
  refine ⟨rcritical2EnergyDerivative w hf, ?_, ?_⟩
  · intro S hS hST
    exact rcritical2EnergyDerivative_intervalIntegrable hν hf w hS hST
  · intro t ht
    exact ⟨rcritical2EnergyDerivative_hasDerivAt hν hf w ht,
      rcritical2_pointwise hν hf w ht⟩

/-- Lane 227's smaller threshold lies in the absorption regime. -/
theorem theta_le_thetaAbs : theta ≤ thetaAbs := by
  apply (min_le_right _ _).trans
  unfold thetaAbs trilinearConstJ
  rw [← one_div]
  apply one_div_le_one_div_of_le
  · positivity [A05.criticalL3Const_pos]
  · have h := A05.criticalL3Const_pos
    have hp : A05.criticalL3Const ^ 3 ≤ (A05.criticalL3Const + 1) ^ 3 :=
      pow_le_pow_left₀ h.le (by linarith) 3
    nlinarith [pow_nonneg h.le 3]

/-- Every classical solution supplies the fixed endpoint S1 package. -/
theorem rCritical2Differential_of_classical {ν : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f) :
    ∀ T (w : ClassicalSolutionR ν (fun _ => 0) f T), RCritical2Differential w hf := by
  intro T w
  obtain ⟨E', hi, hd⟩ := rcritical2_differential hν hf w
  refine ⟨E', hi, ?_⟩
  intro t ht
  refine ⟨(hd t ht).1, ?_⟩
  intro hsmall
  have h := (hd t ht).2 (hsmall.trans
    (mul_le_mul_of_nonneg_right theta_le_thetaAbs hν.le))
  have h₂ : C₂Abs ≤ C₂ := by rw [C₂Abs, trilinear_theta]; norm_num [C₂]
  have h₃ : C₃Abs ≤ C₃ := by norm_num [C₃Abs, C₃]
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₂ hν.le) (sq_nonneg _))
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h₃ (inv_nonneg.mpr hν.le)) (sq_nonneg _)))

/-- Compatibility spelling of lane 228's provider, now at endpoint constants. -/
theorem rcritical2Differential_of_classical {ν T : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : A02.MemForceR f)
    (w : ClassicalSolutionR ν (fun _ => 0) f T) : RCritical2Differential w hf :=
  rCritical2Differential_of_classical hν hf T w

end NSFormalization.Section4.R44
