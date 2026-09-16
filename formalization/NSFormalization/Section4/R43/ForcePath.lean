import NSFormalization.Section4.R43.CriticalMomentum
import NSFormalization.Section4.A04.ZeroSolution

/-!
# The critical force path

This module closes the time-path rows G2--G4 of the R43 split.  The
inhomogeneous order-two datum path supplied by `MemForceR` is lowered to order
one half and then sent through the contractive Bessel-to-homogeneous continuous
linear map of `CriticalMomentum`.  Homogeneous datum uniqueness identifies
that continuous path with `criticalForceHalf`.

The resulting norm path is exactly `criticalForceAt`.  It is continuous on the
future half-line, locally interval integrable, and its interval-integral
primitive has the continuity and FTC derivative expected by
`Paper1.critical_norm_bound`.  The same contractive map sends every measurable
inhomogeneous datum path to a measurable homogeneous one, proving the exact
path-infimum monotonicity required by row G2.
-/

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open scoped ENNReal ContDiff

namespace NSFormalization.Section4.R43

open NSFormalization.Section4.A02
  (SpaceTimeField SpatialField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.D01
  (IsSobolevPath forceSobolevENormL1 lowerVectorL dotHomogeneousENorm)
open NSFormalization.Section4.D01.Homogeneous
  (IsHomogeneousPath IsHomogeneousSliceDatum forceHomogeneousENorm
    forceTimeMeasure bochnerDatumENorm)
open CriticalHomogeneous

/-! ## 1. The contractive Bessel-to-homogeneous map -/

/-- The componentwise Bessel-to-homogeneous map is a contraction in the
Euclidean `PiLp 2` norm. -/
theorem ofSobolevVector_norm_le (s : ℝ) (hs : 0 ≤ s)
    (A : RealVectorSobolev s) :
    ‖ofSobolevVectorL s hs A‖ ≤ ‖A‖ := by
  have hsq : ‖ofSobolevVectorL s hs A‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    have hi := NSFormalization.Source.BesselFractionalData.datum_norm_le
      s hs (A i : RealSobolevHilbert s)
    change ‖ofSobolevScalar s hs (A i)‖ ≤ ‖A i‖ at hi
    change ‖ofSobolevScalar s hs (A i)‖ ^ 2 ≤ ‖A i‖ ^ 2
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hi
  nlinarith [norm_nonneg (ofSobolevVectorL s hs A), norm_nonneg A]

/-- Every inhomogeneous datum path of nonnegative order has a homogeneous
image path for the same physical force (the `IsHomogeneousPath` predicate only;
measurability of the canonical path is proved separately below). -/
theorem isHomogeneousPath_of_isSobolevPath {s : ℝ} (hs : 0 ≤ s)
    {f : SpaceTimeField} {G : ℝ → RealVectorSobolev s}
    (hG : IsSobolevPath s f G) :
    IsHomogeneousPath s f (fun t => ofSobolevVectorL s hs (G t)) := by
  intro t ht
  exact CriticalHomogeneous.ofSobolevVector_isHomogeneousSliceDatum hs (hG t ht)

/-- G2, in the exact path-infimum spelling used by S6: the homogeneous force
norm at order one half is bounded by the inhomogeneous one. -/
theorem forceHomogeneousENorm_le_forceSobolevENormL1
    (f : SpaceTimeField) (_hf : MemForceR f) :
    forceHomogeneousENorm 1 (1 / 2) f ≤ forceSobolevENormL1 (1 / 2) f := by
  refine le_iInf fun G => ?_
  let L := ofSobolevVectorL (1 / 2) (by norm_num)
  have hpath : IsHomogeneousPath (1 / 2) f (fun t => L (G.1 t)) :=
    isHomogeneousPath_of_isSobolevPath (by norm_num) G.2.1
  have hmeas : AEStronglyMeasurable (fun t => L (G.1 t)) forceTimeMeasure :=
    L.continuous.comp_aestronglyMeasurable G.2.2
  calc
    forceHomogeneousENorm 1 (1 / 2) f
        ≤ bochnerDatumENorm 1 (1 / 2) (fun t => L (G.1 t)) :=
      iInf_le (fun H : {H : ℝ → RealVectorSobolev (1 / 2) //
          IsHomogeneousPath (1 / 2) f H ∧
            AEStronglyMeasurable H forceTimeMeasure} =>
        bochnerDatumENorm 1 (1 / 2) H.1) ⟨_, hpath, hmeas⟩
    _ ≤ bochnerDatumENorm 1 (1 / 2) G.1 := by
      exact eLpNorm_mono (fun t => ofSobolevVector_norm_le (1 / 2) (by norm_num) (G.1 t))

/-- G3: every force in `MemForceR` has finite homogeneous
`L¹_t Hdot^(1/2)_x` norm. -/
theorem forceHomogeneousENorm_one_half_ne_top {f : SpaceTimeField}
    (hf : MemForceR f) :
    forceHomogeneousENorm 1 (1 / 2) f ≠ ⊤ :=
  ne_top_of_le_ne_top
    (NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top hf)
    (forceHomogeneousENorm_le_forceSobolevENormL1 f hf)

/-! ## 2. Continuity and identification of the canonical force path -/

/-- On future times, the chosen half-order force datum is the continuous linear
image of any order-one force datum path. -/
theorem criticalForceHalf_eq_of_orderOnePath {f : SpaceTimeField}
    {G : ℝ → RealVectorSobolev (1 : ℝ)}
    (hG : IsSobolevPath 1 f G) {t : ℝ} (ht : 0 ≤ t) :
    criticalForceHalf (f := f) t =
      ofSobolevVectorL (1 / 2) (by norm_num)
        (lowerVectorL 1 (1 / 2) (by norm_num) (G t)) := by
  exact chosenHomogeneousDatum_eq (by norm_num) (by norm_num) (hG t ht)

/-- The canonical half-order datum path of a force is continuous on the whole
closed future half-line. -/
theorem criticalForceHalf_continuousOn {f : SpaceTimeField} (hf : MemForceR f) :
    ContinuousOn (criticalForceHalf (f := f)) (Ici (0 : ℝ)) := by
  obtain ⟨G, hG, hGc, _hG1, _hG2⟩ := hf.2 2
  have heq : ∀ t ∈ Ici (0 : ℝ),
      criticalForceHalf (f := f) t = orderTwoToHalf (G t) :=
    fun t ht => chosenHomogeneousDatum_eq_orderTwoToHalf (hG t ht)
  exact (orderTwoToHalf.continuous.comp_continuousOn hGc.continuousOn).congr heq

/-- The canonical force datum is a homogeneous datum path on every future
slice. -/
theorem criticalForceHalf_isHomogeneousPath {f : SpaceTimeField} (hf : MemForceR f) :
    IsHomogeneousPath (1 / 2) f (criticalForceHalf (f := f)) :=
  criticalForceHalf_isDatum hf

/-- The canonical half-order homogeneous force path is Bochner `L¹` on the
whole positive half-line. -/
theorem criticalForceHalf_memLp_one {f : SpaceTimeField} (hf : MemForceR f) :
    MemLp (criticalForceHalf (f := f)) 1 forceTimeMeasure := by
  obtain ⟨G, hG, _hGc, hG1, _hG2⟩ := hf.2 2
  have hmap : MemLp (fun t => orderTwoToHalf (G t)) 1 forceTimeMeasure :=
    orderTwoToHalf.comp_memLp' hG1
  have hae : criticalForceHalf (f := f) =ᵐ[forceTimeMeasure]
      fun t => orderTwoToHalf (G t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact chosenHomogeneousDatum_eq_orderTwoToHalf (hG t ht.le)
  exact (memLp_congr_ae hae).mpr hmap

/-- The canonical path supplies the strong measurability clause in the
definition of `forceHomogeneousENorm`. -/
theorem criticalForceHalf_aestronglyMeasurable {f : SpaceTimeField}
    (hf : MemForceR f) :
    AEStronglyMeasurable (criticalForceHalf (f := f)) forceTimeMeasure :=
  (criticalForceHalf_memLp_one hf).aestronglyMeasurable

/-- Identification requested by G4: `criticalForceAt` is the norm of the
canonical half-order datum, not a third norm spelling. -/
theorem criticalForceAt_eq_norm_criticalForceHalf {f : SpaceTimeField}
    (hf : MemForceR f) {t : ℝ} (ht : 0 ≤ t) :
    criticalForceAt f t = ‖criticalForceHalf (f := f) t‖ :=
  criticalForceAt_eq_norm (criticalForceHalf_isDatum hf t ht)

/-- The scalar half-order force norm is continuous on the future half-line. -/
theorem criticalForceAt_continuousOn_future {f : SpaceTimeField} (hf : MemForceR f) :
    ContinuousOn (criticalForceAt f) (Ici (0 : ℝ)) := by
  refine (criticalForceHalf_continuousOn hf).norm.congr ?_
  intro t ht
  exact criticalForceAt_eq_norm_criticalForceHalf hf ht

/-- G4 on a compact interval, in the spelling consumed by the scalar
bootstrap. -/
theorem criticalForceAt_continuousOn {f : SpaceTimeField} (hf : MemForceR f)
    {S : ℝ} (_hS : 0 ≤ S) :
    ContinuousOn (criticalForceAt f) (Icc (0 : ℝ) S) :=
  (criticalForceAt_continuousOn_future hf).mono Icc_subset_Ici_self

/-- The corresponding half-open-interval form. -/
theorem criticalForceAt_continuousOn_Ico {f : SpaceTimeField} (hf : MemForceR f)
    {T : ℝ} :
    ContinuousOn (criticalForceAt f) (Ico (0 : ℝ) T) :=
  (criticalForceAt_continuousOn_future hf).mono Ico_subset_Ici_self

/-- The critical force norm is pointwise nonnegative. -/
theorem criticalForceAt_nonneg (f : SpaceTimeField) (t : ℝ) :
    0 ≤ criticalForceAt f t :=
  ENNReal.toReal_nonneg

/-- Continuity on a compact future interval gives interval integrability. -/
theorem criticalForceAt_intervalIntegrable {f : SpaceTimeField} (hf : MemForceR f)
    {S : ℝ} (hS : 0 ≤ S) :
    IntervalIntegrable (criticalForceAt f) volume 0 S := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hS]
  exact criticalForceAt_continuousOn hf hS

/-! ## 3. The forcing primitive in the scalar-bootstrap shape -/

/-- The primitive `N(t) = integral_0^t ‖f(s)‖_{Hdot^(1/2)} ds`. -/
def criticalForcePrimitive (f : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, criticalForceAt f s

/-- The force primitive is continuous on every compact future interval. -/
theorem criticalForcePrimitive_continuousOn {f : SpaceTimeField} (hf : MemForceR f)
    {S : ℝ} (hS : 0 ≤ S) :
    ContinuousOn (criticalForcePrimitive f) (Icc (0 : ℝ) S) := by
  have hi : IntegrableOn (criticalForceAt f) (Icc (0 : ℝ) S) :=
    (criticalForceAt_continuousOn hf hS).integrableOn_compact isCompact_Icc
  have hi' : IntegrableOn (criticalForceAt f) (uIcc (0 : ℝ) S) := by
    simpa only [uIcc_of_le hS] using hi
  change ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, criticalForceAt f s) (Icc 0 S)
  simpa only [uIcc_of_le hS] using intervalIntegral.continuousOn_primitive_interval hi'

/-- FTC derivative of the force primitive at every interior future time. -/
theorem criticalForcePrimitive_hasDerivAt {f : SpaceTimeField} (hf : MemForceR f)
    {S t : ℝ} (hS : 0 ≤ S) (ht : t ∈ Ioo (0 : ℝ) S) :
    HasDerivAt (criticalForcePrimitive f) (criticalForceAt f t) t := by
  have hint : IntervalIntegrable (criticalForceAt f) volume 0 t :=
    criticalForceAt_intervalIntegrable hf ht.1.le
  have hcont : ContinuousAt (criticalForceAt f) t :=
    (criticalForceAt_continuousOn hf hS).continuousAt
      (Icc_mem_nhds ht.1 ht.2)
  exact intervalIntegral.integral_hasDerivAt_right hint
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      ((criticalForceAt_continuousOn hf hS).mono Ioo_subset_Icc_self) t ht)
    hcont

/-- The force primitive vanishes at the left endpoint. -/
@[simp] theorem criticalForcePrimitive_zero (f : SpaceTimeField) :
    criticalForcePrimitive f 0 = 0 :=
  intervalIntegral.integral_same

/-- Prefix integrals of the nonnegative critical force norm increase with the
endpoint. -/
theorem criticalForcePrimitive_monotoneOn {f : SpaceTimeField} (hf : MemForceR f) :
    MonotoneOn (criticalForcePrimitive f) (Ici (0 : ℝ)) := by
  intro s hs t _ht hst
  refine intervalIntegral.integral_mono_interval le_rfl hs hst ?_
    (criticalForceAt_intervalIntegrable hf (hs.trans hst))
  exact ae_of_all _ (fun r => criticalForceAt_nonneg f r)

/-- Every finite prefix integral is bounded by the homogeneous global
`L¹_t Hdot^(1/2)_x` norm.  This is the integral form underlying the path-level
monotonicity row. -/
theorem criticalForcePrimitive_le_forceHomogeneousENorm {f : SpaceTimeField}
    (hf : MemForceR f) {S : ℝ} (hS : 0 ≤ S) :
    ENNReal.ofReal (criticalForcePrimitive f S) ≤
      forceHomogeneousENorm 1 (1 / 2) f := by
  have hint := criticalForceAt_intervalIntegrable hf hS
  have hnonneg : ∀ t, 0 ≤ criticalForceAt f t := criticalForceAt_nonneg f
  refine le_iInf ?_
  rintro ⟨G, hpath, _hmeas⟩
  show ENNReal.ofReal (criticalForcePrimitive f S) ≤
    eLpNorm G 1 forceTimeMeasure
  rw [criticalForcePrimitive, intervalIntegral.integral_of_le hS]
  have hintOn : Integrable (criticalForceAt f) (volume.restrict (Ioc 0 S)) := by
    simpa only [IntegrableOn] using hint.1
  rw [ofReal_integral_eq_lintegral_ofReal hintOn
    (ae_of_all _ (fun t => hnonneg t))]
  have hcongr :
      (∫⁻ t in Ioc 0 S, ENNReal.ofReal (criticalForceAt f t) ∂volume) =
        ∫⁻ t in Ioc 0 S, ‖G t‖ₑ ∂volume := by
    refine setLIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht
    change ENNReal.ofReal (criticalForceAt f t) = ‖G t‖ₑ
    rw [criticalForceAt_eq_norm (hpath t ht.1.le), ofReal_norm]
  rw [hcongr, eLpNorm_one_eq_lintegral_enorm]
  exact lintegral_mono' (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl) le_rfl

/-- The manuscript-facing prefix bound by the inhomogeneous `L¹_t H^(1/2)_x`
norm, obtained by composing the previous result with G2. -/
theorem criticalForcePrimitive_le_forceSobolevENormL1 {f : SpaceTimeField}
    (hf : MemForceR f) {S : ℝ} (hS : 0 ≤ S) :
    criticalForcePrimitive f S ≤ (forceSobolevENormL1 (1 / 2) f).toReal := by
  have hstep : ENNReal.ofReal (criticalForcePrimitive f S) ≤
      forceSobolevENormL1 (1 / 2) f :=
    (criticalForcePrimitive_le_forceHomogeneousENorm hf hS).trans
      (forceHomogeneousENorm_le_forceSobolevENormL1 f hf)
  have hfinite := NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top hf
  have hprim_nonneg : 0 ≤ criticalForcePrimitive f S := by
    exact intervalIntegral.integral_nonneg hS (fun t _ => criticalForceAt_nonneg f t)
  calc
    criticalForcePrimitive f S =
        (ENNReal.ofReal (criticalForcePrimitive f S)).toReal :=
      (ENNReal.toReal_ofReal hprim_nonneg).symm
    _ ≤ (forceSobolevENormL1 (1 / 2) f).toReal :=
      ENNReal.toReal_mono hfinite hstep

/-! ## 4. The two elementary S6 zero reductions -/

/-- The zero initial field has vanishing critical homogeneous norm. -/
theorem zero_dotHomogeneousENorm_half :
    dotHomogeneousENorm (1 / 2) (0 : SpatialField) = 0 := by
  exact NSFormalization.Section4.D01.dotHomogeneousENorm_zero (1 / 2)

/-- The zero initial field belongs to the manuscript initial class. -/
theorem zero_mem_initialClassR :
    (0 : SpatialField) ∈ NSFormalization.Section4.A02.initialClassR :=
  NSFormalization.Section4.A04.zero_mem_initialClassR

/-! ## 5. The zero-datum critical bootstrap wiring -/

/-- R43's `a = 0` scalar bootstrap on every compact subinterval of a classical
lifespan.  Its analytic inputs are exactly `rcritical1_of_classical'` and the
force primitive facts above. -/
theorem critical_bootstrap_zero_datum
    {ν T S c : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν (0 : SpatialField) f T)
    (hS : 0 ≤ S) (hST : S < T)
    (hc0 : 0 ≤ c) (hclt : c < 1 / (2 * trilinearConst))
    (hsmall : criticalForcePrimitive f S ≤ c * ν) :
    ∀ t ∈ Icc (0 : ℝ) S, criticalNormAt w.velocity t ≤ c * ν := by
  let hcrit := criticalDatumPath w hf (criticalDatumInputs_of_classical hν hf w)
  let y : ℝ → ℝ := criticalNormAt w.velocity
  let yExt : ℝ → ℝ := fun r => y (projIcc 0 S hS r)
  have hyIcc : ContinuousOn y (Icc (0 : ℝ) S) :=
    (criticalNormAt_continuousOn hcrit).mono
      (fun t ht => ⟨ht.1, ht.2.trans_lt hST⟩)
  have hyExt : Continuous yExt :=
    (continuousOn_iff_continuous_domRestrict.mp hyIcc).comp continuous_projIcc
  have hy0 : yExt 0 = 0 := by
    have hslice : (fun x => w.velocity (0, x)) = (0 : SpatialField) := by
      funext x
      exact w.initial x
    simp only [yExt, projIcc_left, y]
    rw [criticalNormAt, hslice, NSFormalization.Section4.D01.dotHomogeneousENorm_zero]
    simp
  have hynonneg : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ yExt t := by
    intro t ht
    simp only [yExt, projIcc_of_mem hS ht]
    exact ENNReal.toReal_nonneg
  have hNbound : ∀ t ∈ Icc (0 : ℝ) S, criticalForcePrimitive f t ≤ c * ν := by
    intro t ht
    exact ((criticalForcePrimitive_monotoneOn hf) ht.1 hS ht.2).trans hsmall
  have hrc := rcritical1_of_classical' hν hf w
  have hdE : ∀ t ∈ Ioo (0 : ℝ) S,
      HasDerivAt (fun r => yExt r ^ 2)
        (criticalEnergyDerivative hcrit t) t := by
    intro t ht
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans hST⟩
    have heq : (fun r => yExt r ^ 2) =ᶠ[nhds t] (fun r => y r ^ 2) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      simp only [yExt, projIcc_of_mem hS ⟨hr.1.le, hr.2.le⟩]
    exact (hrc.1 t htT).congr_of_eventuallyEq heq
  have henergy : ∀ t ∈ Ioo (0 : ℝ) S,
      criticalEnergyDerivative hcrit t / 2 +
          (ν - trilinearConst * yExt t) *
            criticalDissipationAt w.velocity t ^ 2
        ≤ criticalForceAt f t * yExt t := by
    intro t ht
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans hST⟩
    simpa only [yExt, projIcc_of_mem hS ⟨ht.1.le, ht.2.le⟩, y] using hrc.2 t htT
  have hb := criticalNormBound_radius trilinearConst_pos hν hc0 hclt
    hyExt hy0 hynonneg
    (criticalForcePrimitive_continuousOn hf hS)
    (criticalForcePrimitive_zero f) hNbound
    (fun t _ => criticalForceAt_nonneg f t) hdE
    (fun t ht => criticalForcePrimitive_hasDerivAt hf hS ht) henergy
  intro t ht
  simpa only [yExt, projIcc_of_mem hS ht, y] using hb t ht

end NSFormalization.Section4.R43
