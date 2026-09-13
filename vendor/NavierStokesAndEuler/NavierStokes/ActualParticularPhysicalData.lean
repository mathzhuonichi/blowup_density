import NavierStokes.ActualParticularRealization
import NavierStokes.ActualSignedPhysicalData
import NavierStokes.PhysicalStageBounds
import NavierStokes.MixedAxisPreservation
import NavierStokes.ActualWaveRegularity
import NavierStokes.CartesianCopySource
import NavierStokes.ActualReferenceRebase

/-!
# Physical copy data for the actual particular reference solve

The native forcing is an explicit input, so the inverse-cover pullback of the
current residual is retained. Every coefficient below is a genuine Volterra
copy solve with the selected reference tangent, interval and cutoff.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff BigOperators

namespace NavierStokes.ActualParticularPhysicalData

attribute [local instance] Classical.propDecidable

open HarmonicCalculus ParticularWaveAssembly ParticularWaveBounds
open PhysicalParticularWave CorrectionState

abbrev Plane := TorusInverse.Plane
abbrev Copy := TorusInverse.Frequency
abbrev Native := PhysicalParticularWave.WaveSpace
abbrev Parameter := PhysicalParticularWave.Parameter
abbrev Associated := Parameter × Plane
abbrev Source := ℤ → Associated → ComplexVector

noncomputable def copyAmplitude (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (k : Copy) (x : Native) : ComplexVector :=
  D.reference.cutoff (D.reference.geometry.coordinates k x.2) •
    complexCopyVelocity (D.reference.tangent j) (f j) D.reference.geometry
      D.reference.length_pos.le k (x.1.1, x.2)

noncomputable def copyPressure (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (k : Copy) (x : Native) : ℂ :=
  D.reference.cutoff (D.reference.geometry.coordinates k x.2) •
    complexCopyPressure (D.reference.tangent j) (f j) D.reference.geometry
      D.reference.length_pos.le k (referenceFrequency D j) (x.1.1, x.2)

noncomputable def commonAmplitude (D : AssemblyData Parameter) (f : Source) (j : ℤ) : Native → ComplexVector :=
  angleLift (ParticularWaveBounds.commonVelocity (D.reference.tangent j) (f j)
    D.reference.geometry D.reference.length_pos.le D.reference.cutoff)

noncomputable def commonPressure (D : AssemblyData Parameter) (f : Source) (j : ℤ) : Native → ℂ :=
  angleLift (ParticularWaveBounds.commonPressure (D.reference.tangent j) (f j)
    D.reference.geometry D.reference.length_pos.le D.reference.cutoff (referenceFrequency D j))

theorem commonAmplitude_eq_sum (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    commonAmplitude D f j x = ∑' k, copyAmplitude D f j k x := rfl

theorem commonPressure_eq_sum (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    commonPressure D f j x = ∑' k, copyPressure D f j k x := rfl

/-- Compact native support makes the actual copy series finite at every
point, independently of the forcing values outside the active copies. -/
theorem finite_copies (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    ∃ J : Finset Copy, ∀ k ∉ J, copyAmplitude D f j k x = 0 ∧ copyPressure D f j k x = 0 := by
  obtain ⟨J, hJ⟩ := D.reference.geometry.finite_copy_cutoffs D.reference.cutoff_compact ‖x.2‖
  refine ⟨J, fun k hk => ?_⟩
  simp only [copyAmplitude, copyPressure, hJ x.2 le_rfl k hk, zero_smul, and_self]

theorem amplitude_summable (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    Summable (fun k => copyAmplitude D f j k x) := by
  obtain ⟨J, hJ⟩ := finite_copies D f j x
  exact summable_of_ne_finset_zero (s := J) (fun k hk => (hJ k hk).1)

theorem pressure_summable (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    Summable (fun k => copyPressure D f j k x) := by
  obtain ⟨J, hJ⟩ := finite_copies D f j x
  exact summable_of_ne_finset_zero (s := J) (fun k hk => (hJ k hk).2)

theorem copyAmplitude_ne_zero_source (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (k : Copy) (x : Native) (hx : copyAmplitude D f j k x ≠ 0) :
    ∃ v ∈ Icc 0 D.reference.length,
      f j (x.1.1, D.reference.geometry.path k x.2 v) ≠ 0 := by
  by_contra! hn
  have hz := complexCopyVelocity_zero_of_path (D.reference.tangent j) (f j)
    D.reference.geometry D.reference.length_pos.le k x.1.1 x.2 hn
  exact hx (by simp only [copyAmplitude, hz, smul_zero])

theorem copyPressure_ne_zero_source (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (k : Copy) (x : Native)
    (ht : (D.reference.geometry.coordinates k x.2).2 ∈ Icc 0 D.reference.length)
    (hx : copyPressure D f j k x ≠ 0) :
    ∃ v ∈ Icc 0 D.reference.length,
      f j (x.1.1, D.reference.geometry.path k x.2 v) ≠ 0 := by
  by_contra! hn
  have hz := complexCopyPressure_zero_of_path (D.reference.tangent j) (f j)
    D.reference.geometry D.reference.length_pos.le k (referenceFrequency D j) x.1.1 x.2 hn ht
  exact hx (by simp only [copyPressure, hz, smul_zero])

noncomputable def normal (D : AssemblyData Parameter) (j : ℤ) (x : Native) : ProblemStatement.Space :=
  (rawCommon D j).normal D.strip D.directions D.reference.band x

noncomputable def potentialMap (K : ℝ) (N : ProblemStatement.Space) :
    ComplexVector →L[ℝ] ComplexVector :=
  CurlClassBounds.inverseCarrier K •
    ((‖N‖ ^ 2)⁻¹ • CurlClassBounds.complexCrossLinear (CurlClassBounds.complexify N))

theorem potentialMap_apply (K : ℝ) (N : ProblemStatement.Space) (v : ComplexVector) :
    potentialMap K N v = CurlClassBounds.inverseCarrier K • CurlClassBounds.normalCoefficient N v := rfl

noncomputable def copyPotential (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (k : Copy) (x : Native) : ComplexVector :=
  potentialMap (referenceFrequency D j) (normal D j x) (copyAmplitude D f j k x)

noncomputable def potential (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (x : Native) : ComplexVector :=
  potentialMap (referenceFrequency D j) (normal D j x) (commonAmplitude D f j x)

theorem potential_eq_sum (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    potential D f j x = ∑' k, copyPotential D f j k x := by
  unfold potential
  rw [commonAmplitude_eq_sum, ContinuousLinearMap.map_tsum _ (amplitude_summable D f j x)]
  rfl

noncomputable def copyPotentialMode (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (k : Copy) (x : Native) : ComplexVector :=
  carrier (referenceFrequency D j) (referencePhase D j) x • copyPotential D f j k x

noncomputable def potentialMode (D : AssemblyData Parameter) (f : Source)
    (j : ℤ) (x : Native) : ComplexVector :=
  carrier (referenceFrequency D j) (referencePhase D j) x • potential D f j x

theorem potentialMode_eq_sum (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    potentialMode D f j x = ∑' k, copyPotentialMode D f j k x := by
  unfold potentialMode
  rw [potential_eq_sum, ← tsum_const_smul'']
  rfl

theorem copyPotentialMode_summable (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    Summable (fun k => copyPotentialMode D f j k x) := by
  obtain ⟨J, hJ⟩ := finite_copies D f j x
  apply summable_of_ne_finset_zero (s := J)
  intro k hk
  simp only [copyPotentialMode, copyPotential, (hJ k hk).1, map_zero, smul_zero]

theorem copyPotential_summable (D : AssemblyData Parameter) (f : Source) (j : ℤ) (x : Native) :
    Summable (fun k => copyPotential D f j k x) := by
  obtain ⟨J, hJ⟩ := finite_copies D f j x
  exact summable_of_ne_finset_zero (s := J)
    (fun k hk => by simp only [copyPotential, (hJ k hk).1, map_zero])

theorem rotated_potential_sum (D : AssemblyData Parameter) (f : Source) (j : ℤ)
    (x : Native) (Y : Plane) (i : Fin 3) :
    (∑' k, (CartesianCopySource.rotationMap Y (copyPotential D f j k x)) i) =
      (CartesianCopySource.rotationMap Y (potential D f j x)) i := by
  let A : ComplexVector →L[ℝ] ℂ := (ContinuousLinearMap.proj i).comp (CartesianCopySource.rotationMap Y)
  have he := A.map_tsum (copyPotential_summable D f j x)
  rw [← potential_eq_sum] at he
  exact he.symm

theorem rotated_potentialMode (D : AssemblyData Parameter) (f : Source) (j : ℤ)
    (x : Native) (Y : Plane) (i : Fin 3) (c : ℝ) :
    (CartesianCopySource.rotationMap Y (c • potentialMode D f j x)) i =
      c • (CartesianCopySource.rotationMap Y (potential D f j x)) i *
        carrier (referenceFrequency D j) (referencePhase D j) x := by
  simp only [potentialMode, map_smul, ActualSignedPhysicalData.cartesian_rotation,
    ActualSignedPhysicalData.rotateCoefficient_complex_smul, Pi.smul_apply, smul_eq_mul,
    Complex.real_smul]
  ring

/-- Specialization to the actual residual supplied by an AssemblyData;
for the physical constructor this data is the rebased native reference. -/
theorem potentialMode_eq_actual (D : AssemblyData Parameter) (H : ReferenceIdentity D)
    (j : ℤ) (x : Native) :
    potentialMode D (referenceSource D) j x = commonPotential D j D.reference.band x := by
  have ha : commonAmplitude D (referenceSource D) j x = (rawCommon D j).amplitude D.reference.band x :=
    congrFun (referenceRaw_eq_common D H j) x
  unfold potentialMode potential
  rw [ha]
  rw [potentialMap_apply]
  change _ = vectorMode (referenceFrequency D j) (referencePhase D j)
    (fun y => CurlClassBounds.inverseCarrier (referenceFrequency D j) •
      CurlClassBounds.normalCoefficient (normal D j y) ((rawCommon D j).amplitude D.reference.band y)) x
  ext i
  simp only [vectorMode, mode, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- The explicit source and the original selected reference determine the
physical potential, with one sum over actual native copies. -/
theorem referencePotential_eq_copies (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) {j : ℤ} {α κ : ℝ}
    (C : LocalControl D.reference D.charts D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j D.background D.copy D.strip D.directions α κ)
    (hQr : 0 < Qr) {z : ProblemStatement.SpaceTime} (hz : 0 < z.2 0)
    (hx : nativeMap h Qr I z ∈ D.strip.domain) :
    referencePotential D h Qr I j z = ∑' k,
      Qr ^ (-h) • copyPotentialMode D (referenceSource D) j k (nativeMap h Qr I z) := by
  rw [referencePotential_eq_common D H C hQr hz hx,
    ← potentialMode_eq_actual D H.identity j,
    potentialMode_eq_sum, ← tsum_const_smul'']

/-- A reference-band identity only needs differentiability of the actual
reference phase at this point, not an unrelated all-band control record. -/
theorem liftPotential_eq_at (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) (j : ℤ) (x : Cylinder)
    (hp : DifferentiableAt ℝ (referencePhase D j) (waveEquiv x)) :
    CurlClassBounds.vectorPotential (referenceFrequency D j)
      PhysicalResidualBridge.ScaledGraph.radius (PhysicalResidualBridge.commonGraph Qr h I).radial
      PhysicalResidualBridge.ScaledGraph.angular (PhysicalResidualBridge.commonGraph Qr h I).axial
      (liftPhase D j) (liftRaw D j) x = commonPotential D j D.reference.band (waveEquiv x) := by
  have he := PhysicalCurlCovariance.vectorPotential_reindex waveEquiv.toContinuousLinearEquiv
    (referenceFrequency D j) (D.background.radius D.reference.band)
    (D.directions.radialField D.reference.band) (fun _ => D.directions.angular)
    (D.directions.axialField D.strip D.reference.band)
    ((rawCommon D j).amplitude D.reference.band) hp
  rw [H.radius, H.radial, H.angular, H.axial] at he
  unfold liftRaw
  rw [referenceRaw_eq_common D H.identity]
  exact he

theorem referencePotential_eq_common_at (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) (j : ℤ) (hK : referenceFrequency D j ≠ 0)
    (hQr : 0 < Qr) {z : ProblemStatement.SpaceTime} (hz : 0 < z.2 0)
    (hp : DifferentiableAt ℝ (referencePhase D j) (nativeMap h Qr I z)) :
    referencePotential D h Qr I j z =
      Qr ^ (-h) • commonPotential D j D.reference.band (nativeMap h Qr I z) := by
  have hpl : DifferentiableAt ℝ (liftPhase D j)
      ((PhysicalResidualBridge.commonGraph Qr h I).map z) := by
    have hp' : DifferentiableAt ℝ (referencePhase D j)
        (waveEquiv ((PhysicalResidualBridge.commonGraph Qr h I).map z)) := hp
    exact hp'.comp ((PhysicalResidualBridge.commonGraph Qr h I).map z) waveEquiv.differentiableAt
  have he := PhysicalCurlCovariance.commonGraph_vectorPotential_pull hQr h I hK hK hz hpl (liftRaw D j)
  simp only [div_self hK, one_mul] at he
  change referencePotential D h Qr I j z = _ at he
  rw [liftPotential_eq_at D H j _ hp] at he
  exact he

theorem referencePotential_eq_copies_at (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) (j : ℤ) (hK : referenceFrequency D j ≠ 0)
    (hQr : 0 < Qr) {z : ProblemStatement.SpaceTime} (hz : 0 < z.2 0)
    (hp : DifferentiableAt ℝ (referencePhase D j) (nativeMap h Qr I z)) :
    referencePotential D h Qr I j z = ∑' k,
      Qr ^ (-h) • copyPotentialMode D (referenceSource D) j k (nativeMap h Qr I z) := by
  rw [referencePotential_eq_common_at D H j hK hQr hz hp,
    ← potentialMode_eq_actual D H.identity j,
    potentialMode_eq_sum, ← tsum_const_smul'']

/-! ## Native coefficient bounds before the Cartesian pullback -/

/-- The inverse carrier and inverse normal are applied to the actual raw
amplitude. Their bounds do not assume a potential-coefficient estimate. -/
theorem potential_class {ι X : Type} [Countable ι] [Nonempty ι]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : WeightedClasses.StripData X} {w : ι → ℕ → X → ℝ} {α β : ℝ}
    {N : ι → ℕ → X → ProblemStatement.Space}
    {a : ι → ℕ → X → ComplexVector} {K : ι → ℕ → ℝ}
    (hN : PhaseJetBounds.PolynomialJets (UniformPrimaryWeights.jointDomain s)
      (fun q => N q.2 q.1))
    (ha : LabelSumBounds.UniformClass s w α a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n x, x ∈ s.domain → b ≤ ‖N l n x‖)
    (hupper : ∀ l n x, x ∈ s.domain → ‖N l n x‖ ≤ M)
    (hK : UniformPrimaryWeights.UniformBandBound s β (fun l n => 1 / K l n)) :
    LabelSumBounds.UniformClass s w (α + β)
      (fun l n x => potentialMap (K l n) (N l n x) (a l n x)) := by
  have hn := UniformPrimaryWeights.normalCoefficient_class hN ha hb hlower hupper
  have hp := (UniformPrimaryWeights.band_smul_class hn hK).map
    (Complex.I • ContinuousLinearMap.id ℝ ComplexVector)
  apply hp.congr
  intro l n x hx
  change _ = potentialMap (K l n) (N l n x) (a l n x)
  rw [potentialMap_apply]
  ext i
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    Pi.smul_apply, Complex.real_smul, smul_eq_mul, CurlClassBounds.inverseCarrier,
    Complex.ofReal_div, Complex.ofReal_one]
  ring

theorem all_components_bounds {ι X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {s : WeightedClasses.StripData X} {w : ι → ℕ → X → ℝ} {h α : ℝ}
    {f : ι → ℕ → X → ComplexVector}
    (hf : LocalPhysicalCopyBounds.LocalSourceBounds s h α w f) :
    LocalPhysicalCopyBounds.LocalSourceBounds s h α (fun q : Fin 3 × ι => w q.2)
      (fun q n x => f q.2 n x q.1) := by
  refine ⟨⟨fun q => hf.uniform.weight_nonneg q.2,
    fun q n => (ContinuousLinearMap.proj q.1 : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn
      (hf.uniform.smooth q.2 n), ?_⟩,
    hf.flat_geometry, ?_, hf.epsilon_eq, hf.slow_le⟩
  · intro m
    obtain ⟨C, hC, p, hb⟩ := hf.uniform.bounds m
    refine ⟨C, hC, p, ?_⟩
    intro q n x hx j hj
    have hc := ((hf.uniform.smooth q.2 n).contDiffAt (s.isOpen_domain.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)
    have hproj : ‖(ContinuousLinearMap.proj q.1 : ComplexVector →L[ℝ] ℂ)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      simp only [one_mul]
      exact norm_le_pi_norm v q.1
    exact (PhysicalWaveSum.norm_jet_linear_comp_at hc (ContinuousLinearMap.proj q.1)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hproj).trans (hb q.2 n x hx j hj))
  · obtain ⟨c, hc, hb⟩ := hf.weight_le
    exact ⟨c, hc, fun q => hb q.2⟩

abbrev LiftPoint := PhysicalWaveSum.LiftPoint
abbrev BandLabel := PhysicalWaveSum.BandLabel
abbrev Cylinder := PhysicalResidualBridge.Cylinder
abbrev NativePoint := CartesianCopySource.Native

/-- The identity chart is justified by the actual support of its
amplitude and continuity of the physical lift at supported points. -/
noncomputable def identityCommonChart {N : ℕ} {K I : Type}
    (f : PhysicalCopyBounds.CopyFamily N K) (cells : PhysicalCopyBounds.SupportCells f)
    {a b h r Z σ : ℝ} {gap : ℕ} (ha : 0 < a)
    (hs : LocalPhysicalCopyBounds.SupportData f a b h r Z gap)
    (s : WeightedClasses.StripData LiftPoint) (source : I → ℕ → LiftPoint → ℂ)
    (idx : K → PhysicalWaveSum.WaveIndex N → I)
    (he : ∀ k J x, f.amplitude k J x =
      ChartScales.Q J.1.val.1 ^ σ • source (idx k J) J.1.val.1 x)
    (hd : ∀ k J x, f.amplitude k J x ≠ 0 → x ∈ s.domain) :
    LocalPhysicalCopyBounds.CommonChart f cells a b h r σ source where
  sourceIndex := idx
  map _ _ := id
  domain _ _ := s.domain
  open_domain _ _ := s.isOpen_domain
  smooth _ _ := contDiffOn_id
  positive_jets m := by
    refine ⟨1, le_rfl, 0, ?_⟩
    intro k J x hx j hj hjm
    simp only [pow_zero, mul_one]
    exact (PhysicalGraphBounds.norm_positive_jet_linear_le
        (ContinuousLinearMap.id ℝ LiftPoint) x hj).trans (by simp)
  amplitude_eq k J x _ := he k J x
  contains k J z _ _ _ _ hz := by
    have hrad := (hs.tsupport_geometry J k hz).1
    have hm := (PhysicalWaveSum.commonLift_smoothAt h J.1.val.1 (f.gap J.1)
      (PhysicalGraphBounds.scaledRadial_ne_zero (PhysicalGraphBounds.annulus_axisFree ha hrad))).continuousAt
    exact hm.continuousWithinAt.mem_closure hz
      (fun y hy => hd k J _ (PhysicalWaveSum.globalWave_ne_zero_amp hy))

/-- Angle-zero insertion in the actual native coordinate order. -/
noncomputable def insertAngle (x : NativePoint) : Native := (((x.1, x.2.1), 0), x.2.2)

theorem insertAngle_cylindricalMap (x : LiftPoint) :
    insertAngle (PhysicalClassBounds.cylindricalMap x) =
      waveEquiv ((PolarCharts.radius (PhysicalGraphBounds.liftXY x),
        (PhysicalGraphBounds.liftZT x, x.2)), 0) := rfl

/-! ## Angular invariance of the actual reference normal -/

theorem invariant_of_reindex {E G H : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] G) (v : E) (f : G → H)
    (hf : CopyAngularInvariance.Invariant v (fun x => f (e x))) :
    CopyAngularInvariance.Invariant (e v) f := by
  intro x t
  simpa only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply] using
    hf (e.symm x) t

theorem invariant_of_reindexVector {E G : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃L[ℝ] G) (v : E) (V : G → G)
    (hV : CopyAngularInvariance.Invariant v (PhysicalCurlCovariance.reindexVector e V)) :
    CopyAngularInvariance.Invariant (e v) V := by
  intro x t
  apply e.symm.injective
  simpa only [PhysicalCurlCovariance.reindexVector, map_add, map_smul,
    ContinuousLinearEquiv.apply_symm_apply] using hV (e.symm x) t

/-- Angular invariance follows from the primitive chart operators and
the actual affine carrier, even where the phase is not differentiable. -/
theorem reference_normal_invariant (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) (j : ℤ) :
    CopyAngularInvariance.Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane)) (normal D j) := by
  apply CopyAngularInvariance.phaseNormal_invariant
    (hΦ := actualCarrier_affine D.background D.carrierBlock j D.reference.band)
  · change CopyAngularInvariance.Invariant (waveEquiv.toContinuousLinearEquiv ((0, 1) : Cylinder)) _
    apply invariant_of_reindex waveEquiv.toContinuousLinearEquiv (0, 1)
    change CopyAngularInvariance.Invariant (0, 1)
      (fun x => D.background.radius D.reference.band (waveEquiv.toContinuousLinearEquiv x))
    rw [H.radius]
    intro x t
    simp [PhysicalResidualBridge.ScaledGraph.radius]
  · change CopyAngularInvariance.Invariant (waveEquiv.toContinuousLinearEquiv ((0, 1) : Cylinder)) _
    apply invariant_of_reindexVector waveEquiv.toContinuousLinearEquiv (0, 1)
    rw [H.radial]
    intro x t
    simp [PhysicalResidualBridge.ScaledGraph.radial]
  · exact CopyAngularInvariance.Invariant.const _
  · change CopyAngularInvariance.Invariant (waveEquiv.toContinuousLinearEquiv ((0, 1) : Cylinder)) _
    apply invariant_of_reindexVector waveEquiv.toContinuousLinearEquiv (0, 1)
    rw [H.axial]
    exact CopyAngularInvariance.Invariant.const _

theorem copyAmplitude_invariant (D : AssemblyData Parameter) (f : Source) (j : ℤ) (k : Copy) :
    CopyAngularInvariance.Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      (copyAmplitude D f j k) := by
  intro x t
  simp [copyAmplitude]

theorem copyPressure_invariant (D : AssemblyData Parameter) (f : Source) (j : ℤ) (k : Copy) :
    CopyAngularInvariance.Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      (copyPressure D f j k) := by
  intro x t
  simp [copyPressure]

theorem copyPotential_invariant (D : AssemblyData Parameter) {h Qr : ℝ} {I : ℕ}
    (H : ReferenceChart D h Qr I) (f : Source) (j : ℤ) (k : Copy) :
    CopyAngularInvariance.Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane))
      (copyPotential D f j k) := by
  intro x t
  simp only [copyPotential, reference_normal_invariant D H j x t,
    copyAmplitude_invariant D f j k x t]

theorem sum_harmonic_nonzero {E : Type*} [AddCommMonoid E] (N : ℕ) (f : ℤ → E) :
    (∑ j : PhysicalWaveSum.Harmonic N, if j.val = 0 then 0 else f j.val) =
      ∑ j ∈ modes N, f j := by
  classical
  rw [Finset.sum_coe_sort (Finset.Icc (-(N : ℤ)) N)
    (fun j => if j = 0 then (0 : E) else f j)]
  rw [← Finset.sum_erase (Finset.Icc (-(N : ℤ)) N)
    (show (if (0 : ℤ) = 0 then (0 : E) else f 0) = 0 by simp)]
  apply Finset.sum_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

/-! ## The selected reference family and its actual copy cells -/

/-- The supplied assemblies retain the chosen references and current
residual sources. Only primitive slot/phase data are recorded here. -/
structure ReferenceFamily {d h : ℝ}
    (sys : PartitionedCovariance.SlotSystem d h
      ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector) where
  active : Set BandLabel
  data : {L : BandLabel // L ∈ active} → AssemblyData Parameter
  phase : PhaseJetBounds.PhaseFamily {L : BandLabel // L ∈ active}
  band : ∀ L, (data L).reference.band = L.val.val.1
  geometry : ∀ L, (data L).reference.geometry = ActualSignedPhysicalData.geometry sys L.val.val 0
  cutoff_support : ∀ L, support (data L).reference.cutoff ⊆
    (ActualSignedGeometry.clockWindow sys L.val.val.1).outer
  length : ∀ L, (data L).reference.length = ChartScales.slotLength sys.radius h L.val.val.1
  cutoff_time : ∀ L z, (data L).reference.cutoff z ≠ 0 →
    z.2 ∈ Icc 0 (data L).reference.length

namespace ReferenceFamily

variable {d h : ℝ}
  {sys : PartitionedCovariance.SlotSystem d h
    ActualSignedGeometry.radialVector ActualSignedGeometry.temporalVector}
  (F : ReferenceFamily sys)

abbrev Label := {L : BandLabel // L ∈ F.active}

noncomputable def selectedCarrier (L : F.Label) (k : Copy) : PhysicalWaveSum.CarrierData :=
  ActualSignedPhysicalData.carrier (h := h) L.val.val k
    (F.phase.p L) (F.phase.pz L) (F.phase.x0 L) (F.phase.F L) (F.phase.G L)

noncomputable def extendedCarrier (L : BandLabel) (k : Copy) : PhysicalWaveSum.CarrierData :=
  if hL : L ∈ F.active then F.selectedCarrier ⟨L, hL⟩ k else
    ActualSignedPhysicalData.carrier (h := h) L.val k 0 0 0 (fun _ => 0) (fun _ => 0)

theorem extendedCarrier_active (L : F.Label) (k : Copy) :
    F.extendedCarrier L.val k = F.selectedCarrier L k := by
  simp only [extendedCarrier, dite_eq_left L.property]

theorem extendedCarrier_center (L : BandLabel) (k : Copy) :
    (F.extendedCarrier L k).center = ActualSignedPhysicalData.center (h := h) L.val k := by
  unfold extendedCarrier
  split_ifs <;> rfl

noncomputable def amplitude (L : F.Label) (j : ℤ) (k : Copy) (x : NativePoint) : ComplexVector :=
  copyAmplitude (F.data L) (referenceSource (F.data L)) j k (insertAngle x)

noncomputable def potentialCoefficient (L : F.Label) (j : ℤ) (k : Copy) (x : NativePoint) : ComplexVector :=
  copyPotential (F.data L) (referenceSource (F.data L)) j k (insertAngle x)

noncomputable def pressureCoefficient (L : F.Label) (j : ℤ) (k : Copy) (x : NativePoint) : ℂ :=
  copyPressure (F.data L) (referenceSource (F.data L)) j k (insertAngle x)

noncomputable def potentialFamily (N : ℕ) (i : Fin 3) : PhysicalCopyBounds.CopyFamily N Copy where
  gap _ := 0
  carrier k L := F.extendedCarrier L k
  amplitude k I x := if hL : I.1 ∈ F.active then if I.2.val = 0 then 0 else
    (ChartScales.Q I.1.val.1 ^ (-h)) •
      (CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)
        (F.potentialCoefficient ⟨I.1, hL⟩ I.2.val k (PhysicalClassBounds.cylindricalMap x))) i
    else 0

noncomputable def pressureFamily (N : ℕ) : PhysicalCopyBounds.CopyFamily N Copy where
  gap _ := 0
  carrier k L := F.extendedCarrier L k
  amplitude k I x := if hL : I.1 ∈ F.active then if I.2.val = 0 then 0 else
    (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h))) •
      F.pressureCoefficient ⟨I.1, hL⟩ I.2.val k (PhysicalClassBounds.cylindricalMap x)
    else 0

theorem potential_amplitude_mem (N : ℕ) (i : Fin 3) (k : Copy)
    (I : PhysicalWaveSum.WaveIndex N) (x : LiftPoint)
    (hx : (F.potentialFamily N i).amplitude k I x ≠ 0) :
    (ActualSignedPhysicalData.geometry sys I.1.val 0).coordinates k x.2 ∈
      (ActualSignedGeometry.clockWindow sys I.1.val.1).outer := by
  by_cases hL : I.1 ∈ F.active
  · apply F.cutoff_support ⟨I.1, hL⟩
    intro hz
    apply hx
    have hy : (PhysicalClassBounds.slowFast x).2 = x.2 := rfl
    simp only [potentialFamily, dite_eq_left hL, potentialCoefficient, copyPotential, copyAmplitude,
      insertAngle, PhysicalClassBounds.cylindricalMap, hy, F.geometry, hz,
      zero_smul, map_zero, Pi.zero_apply, smul_zero, ite_self]
  · exact False.elim (hx (by simp only [potentialFamily, dite_eq_right hL]))

theorem pressure_amplitude_mem (N : ℕ) (k : Copy)
    (I : PhysicalWaveSum.WaveIndex N) (x : LiftPoint)
    (hx : (F.pressureFamily N).amplitude k I x ≠ 0) :
    (ActualSignedPhysicalData.geometry sys I.1.val 0).coordinates k x.2 ∈
      (ActualSignedGeometry.clockWindow sys I.1.val.1).outer := by
  by_cases hL : I.1 ∈ F.active
  · apply F.cutoff_support ⟨I.1, hL⟩
    intro hz
    apply hx
    have hy : (PhysicalClassBounds.slowFast x).2 = x.2 := rfl
    simp only [pressureFamily, dite_eq_left hL, pressureCoefficient, copyPressure,
      insertAngle, PhysicalClassBounds.cylindricalMap, hy, F.geometry, hz,
      zero_smul, smul_zero, ite_self]
  · exact False.elim (hx (by simp only [pressureFamily, dite_eq_right hL]))

noncomputable def potentialCells (hh : 0 ≤ h) (N : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.SupportCells (F.potentialFamily N i) :=
  PhysicalCopyBounds.nativeSupportCells
    (fun L => ActualSignedPhysicalData.geometry sys L.val 0)
    (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).outer)
    (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).outer_compact)
    (fun L => ActualSignedGeometry.clockWindow_injective sys ActualSignedGeometry.vectors_det hh L.property 0)
    (F.potential_amplitude_mem N i)

noncomputable def pressureCells (hh : 0 ≤ h) (N : ℕ) :
    PhysicalCopyBounds.SupportCells (F.pressureFamily N) :=
  PhysicalCopyBounds.nativeSupportCells
    (fun L => ActualSignedPhysicalData.geometry sys L.val 0)
    (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).outer)
    (fun L => (ActualSignedGeometry.clockWindow sys L.val.1).outer_compact)
    (fun L => ActualSignedGeometry.clockWindow_injective sys ActualSignedGeometry.vectors_det hh L.property 0)
    (F.pressure_amplitude_mem N)

theorem potential_amplitude_source {N : ℕ} (i : Fin 3) (k : Copy)
    (L : F.Label) (j : PhysicalWaveSum.Harmonic N) (x : LiftPoint)
    (hx : (F.potentialFamily N i).amplitude k (L.val, j) x ≠ 0) :
    ∃ v ∈ Icc 0 (F.data L).reference.length,
      referenceSource (F.data L) j.val
        ((insertAngle (PhysicalClassBounds.cylindricalMap x)).1.1,
          (F.data L).reference.geometry.path k x.2 v) ≠ 0 := by
  apply copyAmplitude_ne_zero_source (F.data L) (referenceSource (F.data L)) j.val k
    (insertAngle (PhysicalClassBounds.cylindricalMap x))
  intro hz
  apply hx
  simp only [potentialFamily, dite_eq_left L.property, potentialCoefficient, copyPotential,
    hz, map_zero, Pi.zero_apply, smul_zero, ite_self]

theorem potential_amplitude_cutoff {N : ℕ} (i : Fin 3) (k : Copy)
    (L : F.Label) (j : PhysicalWaveSum.Harmonic N) (x : LiftPoint)
    (hx : (F.potentialFamily N i).amplitude k (L.val, j) x ≠ 0) :
    (F.data L).reference.cutoff ((F.data L).reference.geometry.coordinates k x.2) ≠ 0 := by
  intro hz
  apply hx
  have hy : (PhysicalClassBounds.slowFast x).2 = x.2 := rfl
  simp only [potentialFamily, dite_eq_left L.property, potentialCoefficient, copyPotential,
    copyAmplitude, insertAngle, PhysicalClassBounds.cylindricalMap, hy,
    hz, zero_smul, map_zero, Pi.zero_apply, smul_zero, ite_self]

theorem pressure_amplitude_cutoff {N : ℕ} (k : Copy)
    (L : F.Label) (j : PhysicalWaveSum.Harmonic N) (x : LiftPoint)
    (hx : (F.pressureFamily N).amplitude k (L.val, j) x ≠ 0) :
    (F.data L).reference.cutoff ((F.data L).reference.geometry.coordinates k x.2) ≠ 0 := by
  intro hz
  apply hx
  have hy : (PhysicalClassBounds.slowFast x).2 = x.2 := rfl
  simp only [pressureFamily, dite_eq_left L.property, pressureCoefficient, copyPressure,
    insertAngle, PhysicalClassBounds.cylindricalMap, hy,
    hz, zero_smul, smul_zero, ite_self]

theorem pressure_amplitude_source {N : ℕ} (k : Copy)
    (L : F.Label) (j : PhysicalWaveSum.Harmonic N) (x : LiftPoint)
    (hx : (F.pressureFamily N).amplitude k (L.val, j) x ≠ 0) :
    ∃ v ∈ Icc 0 (F.data L).reference.length,
      referenceSource (F.data L) j.val
        ((insertAngle (PhysicalClassBounds.cylindricalMap x)).1.1,
          (F.data L).reference.geometry.path k x.2 v) ≠ 0 := by
  apply copyPressure_ne_zero_source (F.data L) (referenceSource (F.data L)) j.val k
    (insertAngle (PhysicalClassBounds.cylindricalMap x))
    (F.cutoff_time L _ (F.pressure_amplitude_cutoff k L j x hx))
  intro hz
  apply hx
  simp only [pressureFamily, dite_eq_left L.property, pressureCoefficient,
    hz, smul_zero, ite_self]

theorem width_of_cutoff (k : Copy) (L : F.Label) (Y : Plane)
    (hy : (F.data L).reference.cutoff ((F.data L).reference.geometry.coordinates k Y) ≠ 0) :
    |PhysicalGraphBounds.etaCoordinate
      (Y - ActualSignedPhysicalData.center (h := h) L.val.val k)| ≤ sys.radius := by
  have ht := F.cutoff_time L _ hy
  rw [F.geometry, F.length] at ht
  have hpos := ChartScales.timeCoefficient_pos h L.val.val.1
  have he : ChartScales.timeCoefficient h L.val.val.1 *
      ChartScales.slotLength sys.radius h L.val.val.1 = 2 * sys.radius := by
    unfold ChartScales.slotLength
    field_simp
  have hoff := ActualSignedPhysicalData.eta_offset sys L.val.val 0 k Y
  simp only [CommonCoverSolve.coverPower, ContinuousLinearEquiv.refl_apply] at hoff
  rw [hoff]
  have hu := mul_le_mul_of_nonneg_left ht.2 hpos.le
  have hl := mul_nonneg hpos.le ht.1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

abbrev SourceIndex (N : ℕ) := Copy × PhysicalWaveSum.WaveIndex N

instance sourceIndex_nonempty (N : ℕ) : Nonempty (SourceIndex N) :=
  ⟨(0, (⟨(4, 0, false), le_rfl⟩, ⟨0, by simp⟩))⟩

/-- Only the label's own reference band is used by the physical copy.
Zero extension in the discrete band variable keeps a uniform class honest. -/
noncomputable def nativeSource {E : Type} [Zero E] {N : ℕ}
    (f : F.Label → ℤ → Copy → NativePoint → E) (I : SourceIndex N) (n : ℕ) (x : NativePoint) : E :=
  if hL : I.2.1 ∈ F.active then
    if n = I.2.1.val.1 ∧ I.2.2.val ≠ 0 then f ⟨I.2.1, hL⟩ I.2.2.val I.1 x else 0
  else 0

noncomputable def nativeAmplitude (N : ℕ) : SourceIndex N → ℕ → NativePoint → ComplexVector :=
  F.nativeSource F.amplitude

noncomputable def nativePotential (N : ℕ) : SourceIndex N → ℕ → NativePoint → ComplexVector :=
  F.nativeSource F.potentialCoefficient

noncomputable def nativePressure (N : ℕ) : SourceIndex N → ℕ → NativePoint → ℂ :=
  F.nativeSource F.pressureCoefficient

noncomputable def nativeNormal (N : ℕ) (I : SourceIndex N) (n : ℕ) (x : NativePoint) :
    ProblemStatement.Space :=
  if hL : I.2.1 ∈ F.active then
    if n = I.2.1.val.1 ∧ I.2.2.val ≠ 0 then normal (F.data ⟨I.2.1, hL⟩) I.2.2.val (insertAngle x)
    else ProblemStatement.coordinateVector 0
  else ProblemStatement.coordinateVector 0

noncomputable def nativeHarmonic {N : ℕ} (I : SourceIndex N) : ℤ :=
  if I.2.2.val = 0 then 1 else I.2.2.val

theorem nativeHarmonic_ne {N : ℕ} (I : SourceIndex N) : nativeHarmonic I ≠ 0 := by
  unfold nativeHarmonic
  split_ifs with hj <;> simp_all

noncomputable def nativeFrequency {N : ℕ} (I : SourceIndex N) (n : ℕ) : ℝ :=
  (nativeHarmonic I : ℝ) * ChartScales.carrier h n

theorem nativeFrequency_bound (N : ℕ) (s : WeightedClasses.StripData NativePoint)
    (hepsilon : s.epsilon = ChartScales.epsilon h) (hh : 0 ≤ h) :
    UniformPrimaryWeights.UniformBandBound s (1 / 2)
      (fun I : SourceIndex N => fun n => 1 / nativeFrequency (h := h) I n) := by
  refine ⟨1, zero_le_one, 0, ?_⟩
  intro I n
  have hJ : (1 : ℝ) ≤ |(nativeHarmonic I : ℝ)| := by
    exact_mod_cast Int.one_le_abs (nativeHarmonic_ne I)
  have hK : 0 < (ChartScales.carrier h n : ℝ) := by
    have hk := (ChartScales.carrier_viscosity_bounds h hh n).1
    have hn : 0 ≤ (ChartScales.carrier h n : ℝ) := Nat.cast_nonneg _
    by_contra! hz
    have he : (ChartScales.carrier h n : ℝ) = 0 := le_antisymm hz hn
    rw [he] at hk
    norm_num at hk
  have hden : (ChartScales.carrier h n : ℝ) ≤
      |(nativeHarmonic I : ℝ)| * ChartScales.carrier h n :=
    le_mul_of_one_le_left hK.le hJ
  simp only [nativeFrequency, Real.norm_eq_abs, abs_div, abs_one, abs_mul, abs_of_pos hK,
    pow_zero, mul_one, one_mul]
  calc
    _ ≤ 1 / (ChartScales.carrier h n : ℝ) :=
      div_le_div_of_nonneg_left zero_le_one hK hden
    _ ≤ Real.sqrt (ChartScales.epsilon h n) := (ChartScales.carrier_inv_bounds h hh n).2
    _ = s.epsilon n ^ (1 / 2 : ℝ) := by rw [hepsilon, Real.sqrt_eq_rpow]

theorem nativePotential_eq {N : ℕ}
    (hf : ∀ L : F.Label, (F.data L).carrierBlock.frequency (F.data L).reference.band =
      ChartScales.carrier h L.val.val.1)
    (I : SourceIndex N) (n : ℕ) (x : NativePoint) :
    F.nativePotential N I n x =
      potentialMap (nativeFrequency (h := h) I n) (F.nativeNormal N I n x) (F.nativeAmplitude N I n x) := by
  unfold nativePotential nativeAmplitude nativeSource nativeNormal
  split_ifs with hL hn
  · have hK : referenceFrequency (F.data ⟨I.2.1, hL⟩) I.2.2.val = nativeFrequency (h := h) I n := by
      simp only [referenceFrequency, hf, nativeFrequency, nativeHarmonic, ite_eq_right hn.2, hn.1]
    change copyPotential (F.data ⟨I.2.1, hL⟩) _ _ _ _ = _
    unfold copyPotential
    rw [hK]
    rfl
  · exact (map_zero _).symm
  · exact (map_zero _).symm

theorem nativePotential_bounds (N : ℕ) {s : WeightedClasses.StripData NativePoint}
    {w : SourceIndex N → ℕ → NativePoint → ℝ} {α : ℝ}
    (ha : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativeAmplitude N))
    (hN : PhaseJetBounds.PolynomialJets (UniformPrimaryWeights.jointDomain s)
      (fun q => F.nativeNormal N q.2 q.1)) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ I n x, x ∈ s.domain → b ≤ ‖F.nativeNormal N I n x‖)
    (hupper : ∀ I n x, x ∈ s.domain → ‖F.nativeNormal N I n x‖ ≤ M)
    (hf : ∀ L : F.Label, (F.data L).carrierBlock.frequency (F.data L).reference.band =
      ChartScales.carrier h L.val.val.1) (hh : 0 ≤ h) :
    LocalPhysicalCopyBounds.LocalSourceBounds s h (α + 1 / 2) w (F.nativePotential N) := by
  have hp := potential_class hN ha.uniform hb hlower hupper
    (nativeFrequency_bound (h := h) N s (funext ha.epsilon_eq) hh)
  refine ⟨hp.congr (fun I n x _ => (F.nativePotential_eq hf I n x).symm),
    ha.flat_geometry, ha.weight_le, ha.epsilon_eq, ha.slow_le⟩

theorem cartesianPotential_bounds (N : ℕ) {s : WeightedClasses.StripData NativePoint}
    {w : SourceIndex N → ℕ → NativePoint → ℝ} {α a b : ℝ} (ha : 0 < a)
    (hp : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativePotential N)) (i : Fin 3) :
    LocalPhysicalCopyBounds.LocalSourceBounds (CartesianCopySource.pullStrip s a b ha) h α
      (fun I n x => w I n (PhysicalClassBounds.cylindricalMap x))
      (fun I n x => CartesianCopySource.rotatedSource (F.nativePotential N) I n x i) :=
  CartesianCopySource.sourceBounds_rotated_component ha hp i

theorem cartesianPressure_bounds (N : ℕ) {s : WeightedClasses.StripData NativePoint}
    {w : SourceIndex N → ℕ → NativePoint → ℝ} {α a b : ℝ} (ha : 0 < a)
    (hp : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativePressure N)) :
    LocalPhysicalCopyBounds.LocalSourceBounds (CartesianCopySource.pullStrip s a b ha) h α
      (fun I n x => w I n (PhysicalClassBounds.cylindricalMap x))
      (fun I n x => F.nativePressure N I n (PhysicalClassBounds.cylindricalMap x)) :=
  CartesianCopySource.sourceBounds_pullback ha hp

/-- Support premises concern only the literal residual forcing. The
Volterra equation fixes its slow parameter along the entire sampled path. -/
structure SourceSupport (a b Z : ℝ) (s : WeightedClasses.StripData NativePoint) : Prop where
  geometry : ∀ (L : F.Label) (j : ℤ) (p : Parameter) (Y : Plane), 0 ≤ p.1 →
    referenceSource (F.data L) j (p, Y) ≠ 0 →
      2 * a ≤ p.1 ∧ p.1 ≤ b ∧ ‖p.2‖ ≤ Z
  domain : ∀ (L : F.Label) (j : ℤ) (p : Parameter) (Y : Plane), 0 ≤ p.1 →
    referenceSource (F.data L) j (p, Y) ≠ 0 → ∀ V : Plane, (p.1, (p.2, V)) ∈ s.domain
  mask : ∀ (L : F.Label) (j : ℤ) (z : ProblemStatement.SpaceTime) (Y : Plane),
    z ∈ PhysicalWaveSum.preterminal →
    referenceSource (F.data L) j
      ((insertAngle (PhysicalClassBounds.cylindricalMap
        (PhysicalWaveSum.commonLift h L.val.val.1 0 z))).1.1, Y) ≠ 0 →
      PhysicalWaveSum.physicalMask (CoordinateAlgebra.D h) L.val.val
        (PhysicalWaveSum.physicalParams h z) ≠ 0

theorem source_geometry {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (L : F.Label) (j : ℤ) (x : LiftPoint) (Y : Plane)
    (hf : referenceSource (F.data L) j ((insertAngle (PhysicalClassBounds.cylindricalMap x)).1.1, Y) ≠ 0) :
    PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus a b ∧
      ‖PhysicalGraphBounds.liftZT x‖ ≤ Z := by
  have hb := hs.geometry L j _ Y (Real.sqrt_nonneg _) hf
  have hl : 2 * a ≤ PolarCharts.radius (PhysicalGraphBounds.liftXY x) := hb.1
  have hu : PolarCharts.radius (PhysicalGraphBounds.liftXY x) ≤ b := hb.2.1
  have hn := PolarCharts.radius_le_two_norm (PhysicalGraphBounds.liftXY x)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using
      (PolarCharts.norm_le_radius _).trans hu
  · change a ≤ ‖PhysicalGraphBounds.liftXY x‖
    linarith
  · change max ‖x.1.2.2.2‖ ‖x.1.1‖ ≤ Z
    have hz := hb.2.2
    change max ‖x.1.1‖ ‖x.1.2.2.2‖ ≤ Z at hz
    simpa only [max_comm] using hz

theorem source_domain {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (L : F.Label) (j : ℤ) (x : LiftPoint) (Y : Plane)
    (hf : referenceSource (F.data L) j ((insertAngle (PhysicalClassBounds.cylindricalMap x)).1.1, Y) ≠ 0) :
    PhysicalClassBounds.cylindricalMap x ∈ s.domain :=
  hs.domain L j _ Y (Real.sqrt_nonneg _) hf x.2

theorem potential_support {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s)
    (hi : ∀ L : F.Label, ∃ m : ℤ,
      (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (N : ℕ) (i : Fin 3) :
    LocalPhysicalCopyBounds.SupportData (F.potentialFamily N i) a b h sys.radius Z 0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ F.active
    · simpa only [potentialFamily, extendedCarrier, dite_eq_left hL,
        selectedCarrier, ActualSignedPhysicalData.carrier] using hi ⟨L, hL⟩
    · exact ⟨0, by simp [potentialFamily, extendedCarrier, hL, ActualSignedPhysicalData.carrier]⟩
  geometry_support k I z hz := by
    by_cases hL : I.1 ∈ F.active
    · let L : F.Label := ⟨I.1, hL⟩
      obtain ⟨v, hv, hsrc⟩ := F.potential_amplitude_source i k L I.2 _ hz
      have hg := F.source_geometry hs L I.2.val _ _ hsrc
      refine ⟨?_, ?_, ?_⟩
      · simpa only [PhysicalClassBounds.liftXY_commonLift] using hg.1
      · have hh := hg.2
        simp only [potentialFamily, ActualSignedPhysicalData.commonLift_zero] at hh
        exact hh
      · have hw := F.width_of_cutoff k L _ (F.potential_amplitude_cutoff i k L I.2 _ hz)
        change |PhysicalGraphBounds.etaCoordinate
          (PhysicalGraphBounds.nativeGraph h I.1.val.1 z - (F.extendedCarrier I.1 k).center)| ≤ _
        rw [F.extendedCarrier_center]
        simp only [potentialFamily, ActualSignedPhysicalData.commonLift_zero, PhysicalGraphBounds.physicalLift] at hw
        exact hw
    · exact False.elim (hz (by simp only [potentialFamily, dite_eq_right hL]))
  mask_support k I z hz hne := by
    by_cases hL : I.1 ∈ F.active
    · let L : F.Label := ⟨I.1, hL⟩
      obtain ⟨v, hv, hsrc⟩ := F.potential_amplitude_source i k L I.2 _ hne
      exact hs.mask L I.2.val z _ hz hsrc
    · exact False.elim (hne (by simp only [potentialFamily, dite_eq_right hL]))

theorem pressure_support {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s)
    (hi : ∀ L : F.Label, ∃ m : ℤ,
      (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (N : ℕ) :
    LocalPhysicalCopyBounds.SupportData (F.pressureFamily N) a b h sys.radius Z 0 where
  gap_le _ := le_rfl
  gap_native _ := Nat.zero_le _
  angular_integer k L := by
    by_cases hL : L ∈ F.active
    · simpa only [pressureFamily, extendedCarrier, dite_eq_left hL,
        selectedCarrier, ActualSignedPhysicalData.carrier] using hi ⟨L, hL⟩
    · exact ⟨0, by simp [pressureFamily, extendedCarrier, hL, ActualSignedPhysicalData.carrier]⟩
  geometry_support k I z hz := by
    by_cases hL : I.1 ∈ F.active
    · let L : F.Label := ⟨I.1, hL⟩
      obtain ⟨v, hv, hsrc⟩ := F.pressure_amplitude_source k L I.2 _ hz
      have hg := F.source_geometry hs L I.2.val _ _ hsrc
      refine ⟨?_, ?_, ?_⟩
      · simpa only [PhysicalClassBounds.liftXY_commonLift] using hg.1
      · have hh := hg.2
        simp only [pressureFamily, ActualSignedPhysicalData.commonLift_zero] at hh
        exact hh
      · have hw := F.width_of_cutoff k L _ (F.pressure_amplitude_cutoff k L I.2 _ hz)
        change |PhysicalGraphBounds.etaCoordinate
          (PhysicalGraphBounds.nativeGraph h I.1.val.1 z - (F.extendedCarrier I.1 k).center)| ≤ _
        rw [F.extendedCarrier_center]
        simp only [pressureFamily, ActualSignedPhysicalData.commonLift_zero, PhysicalGraphBounds.physicalLift] at hw
        exact hw
    · exact False.elim (hz (by simp only [pressureFamily, dite_eq_right hL]))
  mask_support k I z hz hne := by
    by_cases hL : I.1 ∈ F.active
    · let L : F.Label := ⟨I.1, hL⟩
      obtain ⟨v, hv, hsrc⟩ := F.pressure_amplitude_source k L I.2 _ hne
      exact hs.mask L I.2.val z _ hz hsrc
    · exact False.elim (hne (by simp only [pressureFamily, dite_eq_right hL]))

theorem potential_amplitude_eq_source (N : ℕ) (i : Fin 3) (k : Copy)
    (I : PhysicalWaveSum.WaveIndex N) (x : LiftPoint) :
    (F.potentialFamily N i).amplitude k I x = ChartScales.Q I.1.val.1 ^ (-h) •
      CartesianCopySource.rotatedSource (F.nativePotential N) (k, I) I.1.val.1 x i := by
  by_cases hL : I.1 ∈ F.active <;> by_cases hj : I.2.val = 0 <;>
    simp [potentialFamily, nativePotential, nativeSource, CartesianCopySource.rotatedSource, hL, hj]

theorem pressure_amplitude_eq_source (N : ℕ) (k : Copy)
    (I : PhysicalWaveSum.WaveIndex N) (x : LiftPoint) :
    (F.pressureFamily N).amplitude k I x = ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)) •
      F.nativePressure N (k, I) I.1.val.1 (PhysicalClassBounds.cylindricalMap x) := by
  by_cases hL : I.1 ∈ F.active <;> by_cases hj : I.2.val = 0 <;>
    simp [pressureFamily, nativePressure, nativeSource, hL, hj]

theorem potential_amplitude_domain {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (N : ℕ) (i : Fin 3) (k : Copy)
    (I : PhysicalWaveSum.WaveIndex N) (x : LiftPoint)
    (hx : (F.potentialFamily N i).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s a b ha).domain := by
  by_cases hL : I.1 ∈ F.active
  · let L : F.Label := ⟨I.1, hL⟩
    obtain ⟨v, hv, hsrc⟩ := F.potential_amplitude_source i k L I.2 x hx
    have hg := (F.source_geometry hs L I.2.val x _ hsrc).1
    refine ⟨?_, F.source_domain hs L I.2.val x _ hsrc⟩
    change a / 2 < ‖PhysicalGraphBounds.liftXY x‖ ∧ ‖PhysicalGraphBounds.liftXY x‖ < b + 1
    have hl : a ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.2
    have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ b := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1
    constructor <;> linarith
  · exact False.elim (hx (by simp only [potentialFamily, dite_eq_right hL]))

theorem pressure_amplitude_domain {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (N : ℕ) (k : Copy)
    (I : PhysicalWaveSum.WaveIndex N) (x : LiftPoint)
    (hx : (F.pressureFamily N).amplitude k I x ≠ 0) :
    x ∈ (CartesianCopySource.pullStrip s a b ha).domain := by
  by_cases hL : I.1 ∈ F.active
  · let L : F.Label := ⟨I.1, hL⟩
    obtain ⟨v, hv, hsrc⟩ := F.pressure_amplitude_source k L I.2 x hx
    have hg := (F.source_geometry hs L I.2.val x _ hsrc).1
    refine ⟨?_, F.source_domain hs L I.2.val x _ hsrc⟩
    change a / 2 < ‖PhysicalGraphBounds.liftXY x‖ ∧ ‖PhysicalGraphBounds.liftXY x‖ < b + 1
    have hl : a ≤ ‖PhysicalGraphBounds.liftXY x‖ := hg.2
    have hu : ‖PhysicalGraphBounds.liftXY x‖ ≤ b := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hg.1
    constructor <;> linarith
  · exact False.elim (hx (by simp only [pressureFamily, dite_eq_right hL]))

noncomputable def potentialChart {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hh : 0 ≤ h)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (N : ℕ) (i : Fin 3) :
    LocalPhysicalCopyBounds.CommonChart (F.potentialFamily N i) (F.potentialCells hh N i)
      a b h sys.radius (-h)
      (fun q : Fin 3 × SourceIndex N => fun n x =>
        CartesianCopySource.rotatedSource (F.nativePotential N) q.2 n x q.1) :=
  identityCommonChart (F.potentialFamily N i) (F.potentialCells hh N i) ha
    (F.potential_support hs hi N i) (CartesianCopySource.pullStrip s a b ha) _
    (fun k I => (i, k, I)) (F.potential_amplitude_eq_source N i)
    (F.potential_amplitude_domain hs ha N i)

noncomputable def pressureChart {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hh : 0 ≤ h)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (N : ℕ) :
    LocalPhysicalCopyBounds.CommonChart (F.pressureFamily N) (F.pressureCells hh N)
      a b h sys.radius (-(2 * CoordinateAlgebra.A h))
      (fun I n x => F.nativePressure N I n (PhysicalClassBounds.cylindricalMap x)) :=
  identityCommonChart (F.pressureFamily N) (F.pressureCells hh N) ha
    (F.pressure_support hs hi N) (CartesianCopySource.pullStrip s a b ha) _
    (fun k I => (k, I)) (F.pressure_amplitude_eq_source N)
    (F.pressure_amplitude_domain hs ha N)

noncomputable def sourceCore (L : BandLabel) : Set LiftPoint :=
  {x | ∃ hL : L ∈ F.active, ∃ j : ℤ, ∃ Y : Plane,
    referenceSource (F.data ⟨L, hL⟩) j ((insertAngle (PhysicalClassBounds.cylindricalMap x)).1.1, Y) ≠ 0}

noncomputable def restrictCells {E K : Type} [TopologicalSpace E]
    (c : PeriodizedWaveBounds.Cells E K) (U : Set E) (hU : IsClosed U) :
    PeriodizedWaveBounds.Cells E K where
  carrier n k := c.carrier n k ∩ U
  closed n k := (c.closed n k).inter hU
  locallyFinite n := (c.locallyFinite n).subset (fun _ => inter_subset_left)
  unique n i j x hi hj := c.unique n i j x hi.1 hj.1

noncomputable def localPotentialCells (hh : 0 ≤ h) (N : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.SupportCells (F.potentialFamily N i) where
  cells L := restrictCells ((F.potentialCells hh N i).cells L) (closure (F.sourceCore L)) isClosed_closure
  support I k x hx := by
    refine ⟨(F.potentialCells hh N i).support I k hx, ?_⟩
    by_cases hL : I.1 ∈ F.active
    · obtain ⟨v, hv, hsrc⟩ := F.potential_amplitude_source i k ⟨I.1, hL⟩ I.2 x hx
      exact subset_closure ⟨hL, I.2.val, _, hsrc⟩
    · exact False.elim (hx (by simp only [potentialFamily, dite_eq_right hL]))

noncomputable def localPressureCells (hh : 0 ≤ h) (N : ℕ) :
    PhysicalCopyBounds.SupportCells (F.pressureFamily N) where
  cells L := restrictCells ((F.pressureCells hh N).cells L) (closure (F.sourceCore L)) isClosed_closure
  support I k x hx := by
    refine ⟨(F.pressureCells hh N).support I k hx, ?_⟩
    by_cases hL : I.1 ∈ F.active
    · obtain ⟨v, hv, hsrc⟩ := F.pressure_amplitude_source k ⟨I.1, hL⟩ I.2 x hx
      exact subset_closure ⟨hL, I.2.val, _, hsrc⟩
    · exact False.elim (hx (by simp only [pressureFamily, dite_eq_right hL]))

noncomputable def nativeSlow (x : NativePoint) : PhysicalGraphBounds.Slow := (x.1, (x.2.1.2, x.2.1.1))

theorem slotSlow_native {a : ℝ} (ha : 0 < a) (c : PhysicalWaveSum.CarrierData)
    (n : ℕ) (r : ℝ) (j : PolarCharts.Index) (w : ProblemStatement.SpaceTime)
    (hj : PhysicalGraphBounds.scaledRadial n w ∈ PolarCharts.chartDomain a j) :
    LocalPhysicalCopyBounds.slotSlow (c.withChart j) a h n r w =
      nativeSlow (PhysicalClassBounds.cylindricalMap (PhysicalWaveSum.commonLift h n 0 w)) := by
  have hxy : PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h n w) ∈
      PolarCharts.chartDomain a j := by simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hj
  unfold LocalPhysicalCopyBounds.slotSlow
  rw [PhysicalGraphBounds.slotMap_formula]
  change ((PolarCharts.chart a j (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h n w))).1,
    PhysicalGraphBounds.liftZT (PhysicalGraphBounds.physicalLift h n w)) = _
  rw [ActualSignedPhysicalData.chart_radius ha j hxy]
  rw [ActualSignedPhysicalData.commonLift_zero]
  rfl

structure NativeProfiles where
  region : BandLabel → Set PhysicalGraphBounds.Slow
  region_open : ∀ L, IsOpen (region L)
  jets : PhaseJetBounds.PolynomialJets
    (PhysicalCopyBounds.copyBandDomain (fun (_ : Copy) L => region L) (fun _ L => region_open L))
    (fun I p => ((F.extendedCarrier I.2 I.1).F p, (F.extendedCarrier I.2 I.1).G p))
  covers : ∀ L w, w ∈ PhysicalWaveSum.preterminal →
    PhysicalWaveSum.physicalParams h w ∈ PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) L.val →
    PhysicalGraphBounds.physicalLift h L.val.1 w ∈ closure (F.sourceCore L) →
    nativeSlow (PhysicalClassBounds.cylindricalMap (PhysicalWaveSum.commonLift h L.val.1 0 w)) ∈ region L

noncomputable def potentialCarrier {a b : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hp : F.NativeProfiles) (N : ℕ) (i : Fin 3) :
    PhysicalCopyBounds.CarrierBounds (F.potentialFamily N i) (F.localPotentialCells hh N i)
      a b h sys.radius where
  region _ L := hp.region L
  open_region _ L := hp.region_open L
  jets := hp.jets
  contains _ I w hw hr _ hc j hj := by
    change LocalPhysicalCopyBounds.slotSlow ((F.extendedCarrier I.1 _).withChart j)
      a h I.1.val.1 sys.radius w ∈ hp.region I.1
    rw [slotSlow_native ha _ _ _ _ _ hj]
    apply hp.covers I.1 w hw hr
    simpa only [potentialFamily, ActualSignedPhysicalData.commonLift_zero] using hc.2

noncomputable def pressureCarrier {a b : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hp : F.NativeProfiles) (N : ℕ) :
    PhysicalCopyBounds.CarrierBounds (F.pressureFamily N) (F.localPressureCells hh N)
      a b h sys.radius where
  region _ L := hp.region L
  open_region _ L := hp.region_open L
  jets := hp.jets
  contains _ I w hw hr _ hc j hj := by
    change LocalPhysicalCopyBounds.slotSlow ((F.extendedCarrier I.1 _).withChart j)
      a h I.1.val.1 sys.radius w ∈ hp.region I.1
    rw [slotSlow_native ha _ _ _ _ _ hj]
    apply hp.covers I.1 w hw hr
    simpa only [pressureFamily, ActualSignedPhysicalData.commonLift_zero] using hc.2

noncomputable def nativePast : Set NativePoint := {x | 0 < x.2.1.1}

theorem nativePast_open : IsOpen nativePast := isOpen_lt continuous_const continuous_snd.fst.fst

/-- Qualitative regularity of the literal, discretely indexed native
coefficients. This remains a native input: smoothness on the interior of
one dyadic band alone does not establish it at the band faces. -/
structure NativeRegular (N : ℕ) : Prop where
  potential : ∀ I n, ContDiffOn ℝ ∞ (F.nativePotential N I n) nativePast
  pressure : ∀ I n, ContDiffOn ℝ ∞ (F.nativePressure N I n) nativePast

noncomputable def liftedPast (a b : ℝ) : Set LiftPoint :=
  PhysicalClassBounds.cylindricalDomain a b ∩ PhysicalClassBounds.cylindricalMap ⁻¹' nativePast

theorem liftedPast_open (a b : ℝ) : IsOpen (liftedPast a b) :=
  (PhysicalClassBounds.cylindricalDomain_open a b).inter
    (nativePast_open.preimage CartesianCopySource.cylindricalMap_continuous)

theorem potential_amplitude_smooth {a b : ℝ} (ha : 0 < a) (N : ℕ) (hr : F.NativeRegular N)
    (i : Fin 3) (k : Copy) (I : PhysicalWaveSum.WaveIndex N) :
    ContDiffOn ℝ ∞ ((F.potentialFamily N i).amplitude k I) (liftedPast a b) := by
  have hn : ContDiffOn ℝ ∞
      (fun x => F.nativePotential N (k, I) I.1.val.1 (PhysicalClassBounds.cylindricalMap x)) (liftedPast a b) :=
    (hr.potential (k, I) I.1.val.1).comp
      ((PhysicalClassBounds.cylindricalMap_smooth (b := b) ha).mono inter_subset_left) (fun _ hx => hx.2)
  have hrot : ContDiffOn ℝ ∞
      (fun x : LiftPoint => CartesianCopySource.rotationMap (PhysicalGraphBounds.liftXY x)) (liftedPast a b) :=
    CartesianCopySource.rotationMap_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
      (fun _ hx => PhysicalClassBounds.cylindricalDomain_axisFree ha hx.1)
  have hc := ((ContinuousLinearMap.proj i : ComplexVector →L[ℝ] ℂ).contDiff.comp_contDiffOn
    (hrot.clm_apply hn)).const_smul (ChartScales.Q I.1.val.1 ^ (-h))
  exact hc.congr (fun x _ => F.potential_amplitude_eq_source N i k I x)

theorem pressure_amplitude_smooth {a b : ℝ} (ha : 0 < a) (N : ℕ) (hr : F.NativeRegular N)
    (k : Copy) (I : PhysicalWaveSum.WaveIndex N) :
    ContDiffOn ℝ ∞ ((F.pressureFamily N).amplitude k I) (liftedPast a b) := by
  have hn : ContDiffOn ℝ ∞
      (fun x => F.nativePressure N (k, I) I.1.val.1 (PhysicalClassBounds.cylindricalMap x)) (liftedPast a b) :=
    (hr.pressure (k, I) I.1.val.1).comp
      ((PhysicalClassBounds.cylindricalMap_smooth (b := b) ha).mono inter_subset_left) (fun _ hx => hx.2)
  exact (hn.const_smul (ChartScales.Q I.1.val.1 ^ (-(2 * CoordinateAlgebra.A h)))).congr
    (fun x _ => F.pressure_amplitude_eq_source N k I x)

theorem commonLift_liftedPast {a b : ℝ} (ha : 0 < a) (n : ℕ) {w : ProblemStatement.SpaceTime}
    (hw : w ∈ PhysicalWaveSum.preterminal)
    (hann : PhysicalGraphBounds.scaledRadial n w ∈ PhysicalGraphBounds.annulus a b) :
    PhysicalWaveSum.commonLift h n 0 w ∈ liftedPast a b := by
  refine ⟨PhysicalClassBounds.commonLift_mem_cylindricalDomain ha h n 0 w hann, ?_⟩
  change 0 < (PhysicalClassBounds.cylindricalMap (PhysicalWaveSum.commonLift h n 0 w)).2.1.1
  rw [PhysicalClassBounds.cylindricalMap_commonLift]
  exact div_pos (sub_pos.mpr hw) (ChartScales.Q_pos n)

theorem term_labelRegion {N : ℕ} {K : Type} {f : PhysicalCopyBounds.CopyFamily N K}
    {a b r Z : ℝ} {gap : ℕ} (hs : LocalPhysicalCopyBounds.SupportData f a b h r Z gap)
    (hh : 0 < h) (hh1 : h < 1 / 2) (I : PhysicalWaveSum.WaveIndex N) (k : K)
    {w : ProblemStatement.SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal)
    (ht : w ∈ tsupport (f.term a h r I k)) :
    PhysicalWaveSum.physicalParams h w ∈ PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) I.1.val := by
  apply PhysicalWaveSum.closed_property_on_tsupport PhysicalWaveSum.preterminal_open hw
    (PhysicalWaveSum.physicalParams_continuousAt hh hh1 hw)
    (PhysicalWaveSum.labelRegion_closed _ _) ?_ ht
  intro y hy hny
  exact PhysicalWaveSum.physicalMask_support_subset _ _
    (hs.mask_support k I y hy (PhysicalWaveSum.globalWave_ne_zero_amp hny))

theorem potentialSmooth {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (hp : F.NativeProfiles) (N : ℕ) (hr : F.NativeRegular N) (i : Fin 3) :
    LocalPhysicalCopyBounds.SmoothData (F.potentialFamily N i) a h sys.radius := by
  let hsp := F.potential_support hs hi N i
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedPast_open a b)
      (F.potential_amplitude_smooth ha N hr i k I)
      (commonLift_liftedPast ha _ hw (hsp.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (F.localPotentialCells hh.le N i).term_tsupport_mem ha I k (hsp.tsupport_geometry I k ht).1 ht
    have hl := term_labelRegion hsp hh hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [potentialFamily, ActualSignedPhysicalData.commonLift_zero] using hc.2)
    change LocalPhysicalCopyBounds.SmoothNear (F.extendedCarrier I.1 k).F
        (LocalPhysicalCopyBounds.slotSlow ((F.extendedCarrier I.1 k).withChart j) _ _ _ _ _) ∧
      LocalPhysicalCopyBounds.SmoothNear (F.extendedCarrier I.1 k).G
        (LocalPhysicalCopyBounds.slotSlow ((F.extendedCarrier I.1 k).withChart j) _ _ _ _ _)
    rw [slotSlow_native ha _ _ _ _ _ hj]
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1) (hp.jets.smooth (k, I.1)).fst hp',
      LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1) (hp.jets.smooth (k, I.1)).snd hp'⟩

theorem pressureSmooth {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (hp : F.NativeProfiles) (N : ℕ) (hr : F.NativeRegular N) :
    LocalPhysicalCopyBounds.SmoothData (F.pressureFamily N) a h sys.radius := by
  let hsp := F.pressure_support hs hi N
  constructor
  · intro k I w hw ht
    exact LocalPhysicalCopyBounds.SmoothNear.of_open (liftedPast_open a b)
      (F.pressure_amplitude_smooth ha N hr k I)
      (commonLift_liftedPast ha _ hw (hsp.tsupport_geometry I k ht).1)
  · intro k I w hw ht j hj
    have hc := (F.localPressureCells hh.le N).term_tsupport_mem ha I k (hsp.tsupport_geometry I k ht).1 ht
    have hl := term_labelRegion hsp hh hh1 I k hw ht
    have hp' := hp.covers I.1 w hw hl
      (by simpa only [pressureFamily, ActualSignedPhysicalData.commonLift_zero] using hc.2)
    change LocalPhysicalCopyBounds.SmoothNear (F.extendedCarrier I.1 k).F
        (LocalPhysicalCopyBounds.slotSlow ((F.extendedCarrier I.1 k).withChart j) _ _ _ _ _) ∧
      LocalPhysicalCopyBounds.SmoothNear (F.extendedCarrier I.1 k).G
        (LocalPhysicalCopyBounds.slotSlow ((F.extendedCarrier I.1 k).withChart j) _ _ _ _ _)
    rw [slotSlow_native ha _ _ _ _ _ hj]
    exact ⟨LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1) (hp.jets.smooth (k, I.1)).fst hp',
      LocalPhysicalCopyBounds.SmoothNear.of_open (hp.region_open I.1) (hp.jets.smooth (k, I.1)).snd hp'⟩

theorem frequency_bounds {P : ℝ} (hP : 0 ≤ P)
    (hf : ∀ L : F.Label, |F.phase.p L| ≤ P ∧ |F.phase.pz L| ≤ P ∧ |F.phase.x0 L| ≤ P)
    (k : Copy) (L : BandLabel) :
    |(F.extendedCarrier L k).angular| ≤ P ∧ |(F.extendedCarrier L k).axial| ≤ P ∧
      |(F.extendedCarrier L k).radial| ≤ P := by
  by_cases hL : L ∈ F.active
  · simpa only [extendedCarrier, dite_eq_left hL, selectedCarrier, ActualSignedPhysicalData.carrier] using hf ⟨L, hL⟩
  · simp only [extendedCarrier, dite_eq_right hL, ActualSignedPhysicalData.carrier, abs_zero, and_self]
    exact hP

noncomputable def copyPotentialData {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hh : 0 ≤ h)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (N : ℕ) : MixedAxisPreservation.CopyPotential h where
  Copy := Copy
  harmonics := N
  family := F.potentialFamily N
  inner := a
  outer := b
  width := sys.radius
  axialRadius := Z
  gap := 0
  inner_pos := ha
  support := F.potential_support hs hi N
  cells := F.localPotentialCells hh N

theorem copyPotentialData_field {a b Z : ℝ} {s : WeightedClasses.StripData NativePoint}
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hh : 0 ≤ h)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (N : ℕ) :
    (F.copyPotentialData hs ha hh hi N).field =
      PhysicalCopyBounds.vectorSum (F.potentialFamily N) a h sys.radius := rfl

/-- All physical estimates of this data are supplied by `WaveData`'s
proved native-to-physical theorem. No physical jet bound is an input. -/
noncomputable def potentialWaveData {a b Z P α : ℝ} {s : WeightedClasses.StripData NativePoint}
    (N : ℕ) {w : SourceIndex N → ℕ → NativePoint → ℝ}
    (hc : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativePotential N))
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hZ : 0 ≤ Z) (hP : 1 ≤ P)
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (hp : F.NativeProfiles) (hr : F.NativeRegular N)
    (hf : ∀ L : F.Label, |F.phase.p L| ≤ P ∧ |F.phase.pz L| ≤ P ∧ |F.phase.x0 L| ≤ P) :
    PhysicalStageBounds.WaveData h LiftPoint (Fin 3 × SourceIndex N) Copy (Fin 3) where
  lowerRadius := a
  upperRadius := b
  nativeWidth := sys.radius
  slowBound := Z
  frequencyBound := P
  alpha := α
  shift := -h
  harmonics := N
  gapBound := 0
  lower_pos := ha
  width_nonneg := sys.radius_pos.le
  slow_nonneg := hZ
  frequency_one_le := hP
  strip := CartesianCopySource.pullStrip s a b ha
  weight q n x := w q.2 n (PhysicalClassBounds.cylindricalMap x)
  source q n x := CartesianCopySource.rotatedSource (F.nativePotential N) q.2 n x q.1
  source_bounds := all_components_bounds (CartesianCopySource.sourceBounds_rotated ha hc)
  copies := F.potentialFamily N
  cells := F.localPotentialCells hh.le N
  chart i := identityCommonChart (F.potentialFamily N i) (F.localPotentialCells hh.le N i) ha
    (F.potential_support hs hi N i) (CartesianCopySource.pullStrip s a b ha) _
    (fun k I => (i, k, I)) (F.potential_amplitude_eq_source N i)
    (F.potential_amplitude_domain hs ha N i)
  chart_maps _ _ _ _ hx := hx
  carrier := F.potentialCarrier ha hh.le hp N
  support := F.potential_support hs hi N
  smooth := F.potentialSmooth hs ha hh hh1 hi hp N hr
  frequencies _ := F.frequency_bounds (zero_le_one.trans hP) hf

noncomputable def pressureWaveData {a b Z P α : ℝ} {s : WeightedClasses.StripData NativePoint}
    (N : ℕ) {w : SourceIndex N → ℕ → NativePoint → ℝ}
    (hc : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativePressure N))
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hZ : 0 ≤ Z) (hP : 1 ≤ P)
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (hp : F.NativeProfiles) (hr : F.NativeRegular N)
    (hf : ∀ L : F.Label, |F.phase.p L| ≤ P ∧ |F.phase.pz L| ≤ P ∧ |F.phase.x0 L| ≤ P) :
    PhysicalStageBounds.WaveData h LiftPoint (SourceIndex N) Copy Unit where
  lowerRadius := a
  upperRadius := b
  nativeWidth := sys.radius
  slowBound := Z
  frequencyBound := P
  alpha := α
  shift := -(2 * CoordinateAlgebra.A h)
  harmonics := N
  gapBound := 0
  lower_pos := ha
  width_nonneg := sys.radius_pos.le
  slow_nonneg := hZ
  frequency_one_le := hP
  strip := CartesianCopySource.pullStrip s a b ha
  weight I n x := w I n (PhysicalClassBounds.cylindricalMap x)
  source I n x := F.nativePressure N I n (PhysicalClassBounds.cylindricalMap x)
  source_bounds := CartesianCopySource.sourceBounds_pullback ha hc
  copies _ := F.pressureFamily N
  cells _ := F.localPressureCells hh.le N
  chart _ := identityCommonChart (F.pressureFamily N) (F.localPressureCells hh.le N) ha
    (F.pressure_support hs hi N) (CartesianCopySource.pullStrip s a b ha) _
    (fun k I => (k, I)) (F.pressure_amplitude_eq_source N)
    (F.pressure_amplitude_domain hs ha N)
  chart_maps _ _ _ _ hx := hx
  carrier _ := F.pressureCarrier ha hh.le hp N
  support _ := F.pressure_support hs hi N
  smooth _ := F.pressureSmooth hs ha hh hh1 hi hp N hr
  frequencies _ := F.frequency_bounds (zero_le_one.trans hP) hf

theorem potential_physical_bound {a b Z P α : ℝ} {s : WeightedClasses.StripData NativePoint}
    (N : ℕ) {w : SourceIndex N → ℕ → NativePoint → ℝ}
    (hc : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativePotential N))
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hZ : 0 ≤ Z) (hP : 1 ≤ P)
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (hp : F.NativeProfiles) (hr : F.NativeRegular N)
    (hf : ∀ L : F.Label, |F.phase.p L| ≤ P ∧ |F.phase.pz L| ≤ P ∧ |F.phase.x0 L| ≤ P)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h z ≤ 1 →
      ‖iteratedFDeriv ℝ m (PhysicalCopyBounds.vectorSum (F.potentialFamily N) a h sys.radius) z‖ ≤
        C * PhysicalWaveSum.physicalQ h z ^
          (h * α - PhysicalClassBounds.physicalLoss h (-h) m) :=
  (F.potentialWaveData N hc hs ha hZ hP hh hh1 hi hp hr hf).vector_bound hh hh1 m

theorem pressure_physical_bound {a b Z P α : ℝ} {s : WeightedClasses.StripData NativePoint}
    (N : ℕ) {w : SourceIndex N → ℕ → NativePoint → ℝ}
    (hc : LocalPhysicalCopyBounds.LocalSourceBounds s h α w (F.nativePressure N))
    (hs : F.SourceSupport a b Z s) (ha : 0 < a) (hZ : 0 ≤ Z) (hP : 1 ≤ P)
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hi : ∀ L : F.Label, ∃ m : ℤ, (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = m)
    (hp : F.NativeProfiles) (hr : F.NativeRegular N)
    (hf : ∀ L : F.Label, |F.phase.p L| ≤ P ∧ |F.phase.pz L| ≤ P ∧ |F.phase.x0 L| ≤ P)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h z ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun y => ((F.pressureFamily N).sum a h sys.radius y).re) z‖ ≤
        C * PhysicalWaveSum.physicalQ h z ^
          (h * α - PhysicalClassBounds.physicalLoss h (-(2 * CoordinateAlgebra.A h)) m) :=
  (F.pressureWaveData N hc hs ha hZ hP hh hh1 hi hp hr hf).pressure_bound hh hh1 m

/-! ## Exact carrier and copy-sum identities on the source parameter domain -/

/-- All hypotheses concern the selected reference, its primitive phase,
or the support of its forcing. No identity of solved fields is assumed. -/
structure ReferenceGeometry (U : F.Label → Set Parameter) : Prop where
  chart : ∀ L, ReferenceChart (F.data L) h (ChartScales.Q L.val.val.1)
    (ChartScales.nativeIndex h L.val.val.1)
  frequency : ∀ L, (F.data L).carrierBlock.frequency (F.data L).reference.band =
    (ChartScales.carrier h L.val.val.1 : ℝ)
  phase : ∀ L, liftPhase (F.data L) 1 =
    ActualSignedGeometry.periodicPhase sys L.val.val 0
      (ChartScales.epsilon h L.val.val.1) (F.phase.p L) (F.phase.pz L)
      (F.phase.x0 L) (F.phase.F L) (F.phase.G L)
  source_core : ∀ L j p, p ∈ U L → ∀ Y,
    referenceSource (F.data L) j (p, Y) ≠ 0 → ∃ k : Copy,
      (F.data L).reference.geometry.coordinates k Y ∈
        (ActualSignedGeometry.clockWindow sys L.val.val.1).core

variable {U : F.Label → Set Parameter} (G : F.ReferenceGeometry U)

include G

/-- A nonzero forcing value along a contributing path puts its original
copy in the core. Uniqueness uses the actual injective padded slot. -/
theorem path_core (hh : 0 ≤ h) (L : F.Label) (j : ℤ) (k : Copy)
    {p : Parameter} (hp : p ∈ U L) {Y : Plane}
    (hc : (F.data L).reference.cutoff ((F.data L).reference.geometry.coordinates k Y) ≠ 0)
    {v : ℝ} (hv : v ∈ Icc 0 (F.data L).reference.length)
    (hf : referenceSource (F.data L) j (p, (F.data L).reference.geometry.path k Y v) ≠ 0) :
    (F.data L).reference.geometry.coordinates k Y ∈
      (ActualSignedGeometry.clockWindow sys L.val.val.1).core := by
  let g := (F.data L).reference.geometry
  let W := ActualSignedGeometry.clockWindow sys L.val.val.1
  have ho : g.coordinates k Y ∈ W.outer := F.cutoff_support L hc
  have hv' : (0, v) ∈ W.core := by
    refine ⟨⟨neg_nonpos.mpr sys.radius_pos.le, sys.radius_pos.le⟩, ?_⟩
    simp only [F.length] at hv
    exact hv
  have hpout : g.coordinates k (g.path k Y v) ∈ W.outer := by
    rw [g.coordinates_path]
    exact ⟨ho.1, (W.core_subset_outer hv').2⟩
  obtain ⟨k', hk'⟩ := G.source_core L j p hp _ hf
  have hi : InjOn TorusAverages.quotientPoint ((fun z => g.center + g.basis z) '' W.outer) := by
    change InjOn TorusAverages.quotientPoint
      ((fun z => (F.data L).reference.geometry.center + (F.data L).reference.geometry.basis z) '' W.outer)
    rw [F.geometry]
    exact ActualSignedGeometry.clockWindow_injective sys ActualSignedGeometry.vectors_det hh L.val.property 0
  have he : k = k' := native_copy_unique g hi hpout (W.core_subset_outer hk')
  subst k'
  refine ⟨?_, ?_⟩
  · simpa only [(F.data L).reference.geometry.coordinates_path] using hk'.1
  · have ht := F.cutoff_time L _ hc
    simp only [F.length] at ht
    exact ht

theorem phase_eq_native (hh : 0 ≤ h) (L : F.Label) (j : ℤ) (k : Copy)
    (a : ℝ) (chart : PolarCharts.Index) (x : LiftPoint)
    (hx : (F.data L).reference.geometry.coordinates k x.2 ∈
      (ActualSignedGeometry.clockWindow sys L.val.val.1).core) :
    referencePhase (F.data L) j (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart x)) =
      ((F.selectedCarrier L k).withChart chart).phase a h L.val.val.1 sys.radius x := by
  change liftPhase (F.data L) 1 (ActualSignedPhysicalData.cylinderAt a chart x) = _
  rw [G.phase L]
  have hx' : (ActualSignedPhysicalData.geometry sys L.val.val 0).coordinates k x.2 ∈
      (ActualSignedGeometry.clockWindow sys L.val.val.1).core := by simpa only [F.geometry] using hx
  have he := (ActualSignedGeometry.periodicPhase_germ sys hh L.val.property 0
    (ChartScales.epsilon h L.val.val.1) (F.phase.p L) (F.phase.pz L) (F.phase.x0 L)
    (F.phase.F L) (F.phase.G L) k (x := ActualSignedPhysicalData.cylinderAt a chart x) hx').eq_of_nhds
  exact he.trans (ActualSignedPhysicalData.carrier_phase_eq_native sys L.val.val 0 k
    (F.phase.p L) (F.phase.pz L) (F.phase.x0 L) (F.phase.F L) (F.phase.G L) a chart x).symm

omit F G in
theorem invariant_cylinderAt {E : Type} (f : Native → E)
    (hf : CopyAngularInvariance.Invariant (((0 : Parameter), (1 : ℝ)), (0 : Plane)) f)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a chart) :
    f (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart x)) =
      f (insertAngle (PhysicalClassBounds.cylindricalMap x)) := by
  have hi : CopyAngularInvariance.Invariant ((0, 1) : Cylinder) (fun y => f (waveEquiv y)) := by
    intro y t
    simp only [map_add, map_smul]
    exact hf (waveEquiv y) t
  have he := ActualSignedPhysicalData.invariant_angle_zero _ hi
    (ActualSignedPhysicalData.cylinderAt a chart x)
  rw [ActualSignedPhysicalData.cylinderAt_fst ha chart hx] at he
  exact he

theorem potential_cylinderAt (L : F.Label) (j : ℤ) (k : Copy)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a chart) :
    copyPotential (F.data L) (referenceSource (F.data L)) j k
        (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart x)) =
      F.potentialCoefficient L j k (PhysicalClassBounds.cylindricalMap x) :=
  invariant_cylinderAt _ (copyPotential_invariant (F.data L) (G.chart L) _ j k) ha chart hx

omit G in
theorem pressure_cylinderAt (L : F.Label) (j : ℤ) (k : Copy)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) {x : LiftPoint}
    (hx : PhysicalGraphBounds.liftXY x ∈ PolarCharts.chartDomain a chart) :
    copyPressure (F.data L) (referenceSource (F.data L)) j k
        (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart x)) =
      F.pressureCoefficient L j k (PhysicalClassBounds.cylindricalMap x) :=
  invariant_cylinderAt _ (copyPressure_invariant (F.data L) _ j k) ha chart hx

theorem character_eq_carrier (hh : 0 ≤ h) (L : F.Label) (j : ℤ) (k : Copy)
    (a : ℝ) (chart : PolarCharts.Index) (x : LiftPoint)
    (hx : (F.data L).reference.geometry.coordinates k x.2 ∈
      (ActualSignedGeometry.clockWindow sys L.val.val.1).core) :
    PhysicalGraphBounds.character ((ChartScales.carrier h L.val.val.1 : ℝ) * (j : ℝ))
        (((F.selectedCarrier L k).withChart chart).phase a h L.val.val.1 sys.radius x) =
      HarmonicCalculus.carrier (referenceFrequency (F.data L) j) (referencePhase (F.data L) j)
        (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart x)) := by
  rw [← F.phase_eq_native G hh L j k a chart x hx]
  simp only [PhysicalGraphBounds.character, PhysicalGraphBounds.phaseFactor,
    HarmonicCalculus.carrier, HarmonicCalculus.phaseFactor, referenceFrequency, G.frequency]
  congr 1
  push_cast
  ring

/-- The physical pressure carrier is the actual periodic carrier on every
nonzero copy. The support argument uses the forcing before integration. -/
theorem pressure_commonWave (hh : 0 ≤ h) {N : ℕ} (L : F.Label)
    (j : PhysicalWaveSum.Harmonic N) (hj : j.val ≠ 0) (k : Copy)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) (w : ProblemStatement.SpaceTime)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 w ∈ PolarCharts.chartDomain a chart)
    (hp : (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
      (PhysicalGraphBounds.physicalLift h L.val.val.1 w))).1.1 ∈ U L) :
    PhysicalWaveSum.commonWave a h L.val.val.1 0 sys.radius
      ((F.selectedCarrier L k).withChart chart)
      ((F.pressureFamily N).amplitude k (L.val, j)) j.val w =
      (ChartScales.Q L.val.val.1 ^ (-(2 * CoordinateAlgebra.A h))) •
        copyPressure (F.data L) (referenceSource (F.data L)) j.val k
          (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
            (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) *
        HarmonicCalculus.carrier (referenceFrequency (F.data L) j.val) (referencePhase (F.data L) j.val)
          (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
            (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) := by
  have hx : PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.val.1 w) ∈
      PolarCharts.chartDomain a chart := by
    simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hchart
  simp only [PhysicalWaveSum.commonWave, ActualSignedPhysicalData.commonLift_zero,
    pressureFamily, dite_eq_left L.property, ite_eq_right hj]
  rw [← F.pressure_cylinderAt L j.val k ha chart hx]
  by_cases hz : copyPressure (F.data L) (referenceSource (F.data L)) j.val k
      (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
        (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) = 0
  · simp only [hz, smul_zero, zero_mul]
  · have hc : (F.data L).reference.cutoff ((F.data L).reference.geometry.coordinates k
        (PhysicalGraphBounds.physicalLift h L.val.val.1 w).2) ≠ 0 := by
      intro he
      apply hz
      simp only [copyPressure, waveEquiv_apply, ActualSignedPhysicalData.cylinderAt, he, zero_smul]
    obtain ⟨v, hv, hf⟩ := copyPressure_ne_zero_source (F.data L) (referenceSource (F.data L))
      j.val k (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
        (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) (F.cutoff_time L _ hc) hz
    have hcore := F.path_core G hh L j.val k hp hc hv hf
    rw [F.character_eq_carrier G hh L j.val k a chart _ hcore]

theorem potential_commonWave (hh : 0 ≤ h) {N : ℕ} (L : F.Label)
    (j : PhysicalWaveSum.Harmonic N) (hj : j.val ≠ 0) (k : Copy) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) (w : ProblemStatement.SpaceTime)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 w ∈ PolarCharts.chartDomain a chart)
    (hp : (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
      (PhysicalGraphBounds.physicalLift h L.val.val.1 w))).1.1 ∈ U L) :
    PhysicalWaveSum.commonWave a h L.val.val.1 0 sys.radius
      ((F.selectedCarrier L k).withChart chart)
      ((F.potentialFamily N i).amplitude k (L.val, j)) j.val w =
      (ChartScales.Q L.val.val.1 ^ (-h)) •
        (CartesianCopySource.rotationMap
          (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.val.1 w))
          (copyPotential (F.data L) (referenceSource (F.data L)) j.val k
            (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
              (PhysicalGraphBounds.physicalLift h L.val.val.1 w))))) i *
        HarmonicCalculus.carrier (referenceFrequency (F.data L) j.val) (referencePhase (F.data L) j.val)
          (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
            (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) := by
  have hx : PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.val.1 w) ∈
      PolarCharts.chartDomain a chart := by
    simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hchart
  simp only [PhysicalWaveSum.commonWave, ActualSignedPhysicalData.commonLift_zero,
    potentialFamily, dite_eq_left L.property, ite_eq_right hj]
  rw [← F.potential_cylinderAt G L j.val k ha chart hx]
  by_cases hz : copyPotential (F.data L) (referenceSource (F.data L)) j.val k
      (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
        (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) = 0
  · simp only [hz, map_zero, Pi.zero_apply, smul_zero, zero_mul]
  · have hr : copyAmplitude (F.data L) (referenceSource (F.data L)) j.val k
        (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
          (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) ≠ 0 := by
      intro he
      exact hz (by simp only [copyPotential, he, map_zero])
    have hc : (F.data L).reference.cutoff ((F.data L).reference.geometry.coordinates k
        (PhysicalGraphBounds.physicalLift h L.val.val.1 w).2) ≠ 0 := by
      intro he
      apply hr
      simp only [copyAmplitude, waveEquiv_apply, ActualSignedPhysicalData.cylinderAt, he, zero_smul]
    obtain ⟨v, hv, hf⟩ := copyAmplitude_ne_zero_source (F.data L) (referenceSource (F.data L)) j.val k _ hr
    have hcore := F.path_core G hh L j.val k hp hc hv hf
    rw [F.character_eq_carrier G hh L j.val k a chart _ hcore]

theorem pressure_periodized_of_chart (hh : 0 ≤ h) {N : ℕ} (L : F.Label)
    (j : PhysicalWaveSum.Harmonic N) (hj : j.val ≠ 0)
    {a b : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) (w : ProblemStatement.SpaceTime)
    (hw : PhysicalGraphBounds.scaledRadial L.val.val.1 w ∈ PhysicalGraphBounds.annulus a b)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 w ∈ PolarCharts.chartDomain a chart)
    (m : ℤ) (hm : (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = (m : ℝ))
    (hp : (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
      (PhysicalGraphBounds.physicalLift h L.val.val.1 w))).1.1 ∈ U L) :
    (F.pressureFamily N).periodized a h sys.radius (L.val, j) w =
      (ChartScales.Q L.val.val.1 ^ (-(2 * CoordinateAlgebra.A h))) •
        ActualParticularPhysicalData.commonPressure (F.data L) (referenceSource (F.data L)) j.val
          (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
            (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) *
        HarmonicCalculus.carrier (referenceFrequency (F.data L) j.val) (referencePhase (F.data L) j.val)
          (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
            (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) := by
  have hc := PhysicalWaveSum.chooseChart_valid ha hw
  change (∑' k, PhysicalWaveSum.commonWave a h L.val.val.1 0 sys.radius
    ((F.extendedCarrier L.val k).withChart
      (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.val.1 w)))
    ((F.pressureFamily N).amplitude k (L.val, j)) j.val w) = _
  simp_rw [F.extendedCarrier_active L]
  have he (k : Copy) := PhysicalWaveSum.commonWave_charts_agree ha h L.val.val.1 0 sys.radius
    (F.selectedCarrier L k) ((F.pressureFamily N).amplitude k (L.val, j)) j.val w m hm _ chart hc hchart
  simp_rw [he, F.pressure_commonWave G hh L j hj _ ha chart w hchart hp]
  rw [tsum_mul_right, tsum_const_smul'', ← commonPressure_eq_sum]

theorem potential_periodized_of_chart (hh : 0 ≤ h) {N : ℕ} (L : F.Label)
    (j : PhysicalWaveSum.Harmonic N) (hj : j.val ≠ 0) (i : Fin 3)
    {a b : ℝ} (ha : 0 < a) (chart : PolarCharts.Index) (w : ProblemStatement.SpaceTime)
    (hw : PhysicalGraphBounds.scaledRadial L.val.val.1 w ∈ PhysicalGraphBounds.annulus a b)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 w ∈ PolarCharts.chartDomain a chart)
    (m : ℤ) (hm : (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = (m : ℝ))
    (hp : (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
      (PhysicalGraphBounds.physicalLift h L.val.val.1 w))).1.1 ∈ U L) :
    (F.potentialFamily N i).periodized a h sys.radius (L.val, j) w =
      (ChartScales.Q L.val.val.1 ^ (-h)) •
        (CartesianCopySource.rotationMap
          (PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h L.val.val.1 w))
          (potential (F.data L) (referenceSource (F.data L)) j.val
            (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
              (PhysicalGraphBounds.physicalLift h L.val.val.1 w))))) i *
        HarmonicCalculus.carrier (referenceFrequency (F.data L) j.val) (referencePhase (F.data L) j.val)
          (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
            (PhysicalGraphBounds.physicalLift h L.val.val.1 w))) := by
  have hc := PhysicalWaveSum.chooseChart_valid ha hw
  change (∑' k, PhysicalWaveSum.commonWave a h L.val.val.1 0 sys.radius
    ((F.extendedCarrier L.val k).withChart
      (PhysicalWaveSum.chooseChart a (PhysicalGraphBounds.scaledRadial L.val.val.1 w)))
    ((F.potentialFamily N i).amplitude k (L.val, j)) j.val w) = _
  simp_rw [F.extendedCarrier_active L]
  have he (k : Copy) := PhysicalWaveSum.commonWave_charts_agree ha h L.val.val.1 0 sys.radius
    (F.selectedCarrier L k) ((F.potentialFamily N i).amplitude k (L.val, j)) j.val w m hm _ chart hc hchart
  simp_rw [he, F.potential_commonWave G hh L j hj _ i ha chart w hchart hp]
  rw [tsum_mul_right, tsum_const_smul'', rotated_potential_sum]

theorem pressure_periodized_physical (hh : 0 ≤ h) {N : ℕ} (L : F.Label)
    (j : PhysicalWaveSum.Harmonic N) (hj : j.val ≠ 0)
    {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (chart : PolarCharts.Index) (z : ProblemStatement.SpaceTime)
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical δ chart)
    (hw : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a chart)
    (m : ℤ) (hm : (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = (m : ℝ))
    (hp : (nativeMap h (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) z).1.1 ∈ U L) :
    ((F.pressureFamily N).periodized a h sys.radius (L.val, j)
      (z.1, CylindricalResidual.chart z.2)).re =
      PhysicalParticularWave.physicalPressure (F.data L) h (ChartScales.Q L.val.val.1)
        (ChartScales.nativeIndex h L.val.val.1) δ j.val (z.1, CylindricalResidual.chart z.2) := by
  have hmap := ActualSignedPhysicalData.cylinderAt_physical_forward h L.val.val.1 ha chart z hz.1 hz.2.1 hchart
  have hp' : (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
      (PhysicalGraphBounds.physicalLift h L.val.val.1 (z.1, CylindricalResidual.chart z.2)))).1.1 ∈ U L := by
    rw [hmap]
    exact hp
  have hK : (F.data L).carrierBlock.frequency (F.data L).reference.band ≠ 0 := by
    rw [G.frequency L]
    exact PartitionedCovariance.actual_carrier_ne_zero _ _
  rw [F.pressure_periodized_of_chart G hh L j hj ha chart _ hw hchart m hm hp', hmap,
    PhysicalParticularWave.physicalPressure_forward (F.data L) h _ _ j.val hK hδ chart hz]
  rfl

theorem potential_periodized_physical (hh : 0 ≤ h) {N : ℕ} (L : F.Label)
    (j : PhysicalWaveSum.Harmonic N) (hj : j.val ≠ 0) (i : Fin 3)
    {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (chart : PolarCharts.Index) (z : ProblemStatement.SpaceTime)
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical δ chart)
    (hw : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a chart)
    (m : ℤ) (hm : (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = (m : ℝ))
    (hp : (nativeMap h (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) z).1.1 ∈ U L)
    (hΦ : DifferentiableAt ℝ (referencePhase (F.data L) j.val)
      (nativeMap h (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) z)) :
    ((F.potentialFamily N i).periodized a h sys.radius (L.val, j)
      (z.1, CylindricalResidual.chart z.2)).re =
      PhysicalParticularWave.physicalPotential (F.data L) h (ChartScales.Q L.val.val.1)
        (ChartScales.nativeIndex h L.val.val.1) δ j.val (z.1, CylindricalResidual.chart z.2) i := by
  have hmap := ActualSignedPhysicalData.cylinderAt_physical_forward h L.val.val.1 ha chart z hz.1 hz.2.1 hchart
  have hp' : (waveEquiv (ActualSignedPhysicalData.cylinderAt a chart
      (PhysicalGraphBounds.physicalLift h L.val.val.1 (z.1, CylindricalResidual.chart z.2)))).1.1 ∈ U L := by
    rw [hmap]
    exact hp
  have hK : (F.data L).carrierBlock.frequency (F.data L).reference.band ≠ 0 := by
    rw [G.frequency L]
    exact PartitionedCovariance.actual_carrier_ne_zero _ _
  have hj' : (j.val : ℝ) ≠ 0 := by exact_mod_cast hj
  have hfreq : referenceFrequency (F.data L) j.val ≠ 0 := mul_ne_zero hj' hK
  have hpot := referencePotential_eq_common_at (F.data L) (G.chart L) j.val hfreq
    (ChartScales.Q_pos _) hz.1 hΦ
  rw [← potentialMode_eq_actual (F.data L) (G.chart L).identity j.val] at hpot
  simp only [nativeMap] at hpot
  have hc : PhysicalGraphBounds.liftXY
      (PhysicalGraphBounds.physicalLift h L.val.val.1 (z.1, CylindricalResidual.chart z.2)) ∈
      PolarCharts.chartDomain a chart := by
    simpa only [PhysicalGraphBounds.liftXY_physicalLift] using hchart
  have hangle : (PolarCharts.chart a chart (PhysicalGraphBounds.liftXY
      (PhysicalGraphBounds.physicalLift h L.val.val.1 (z.1, CylindricalResidual.chart z.2)))).2 = z.2 1 :=
    congrArg Prod.snd hmap
  rw [F.potential_periodized_of_chart G hh L j hj i ha chart _ hw hchart m hm hp',
    ← rotated_potentialMode, hmap, ← hpot, ActualSignedPhysicalData.cartesian_rotation,
    ActualSignedPhysicalData.rotateCoefficient_chart_re ha chart hc, hangle]
  have he := (PhysicalCurlCovariance.globalCartesianPotential_forward_germ hδ chart
    (referencePotential (F.data L) h (ChartScales.Q L.val.val.1)
      (ChartScales.nativeIndex h L.val.val.1) j.val)
    (referencePotential_periodic (F.data L) h (ChartScales.Q L.val.val.1)
      (ChartScales.nativeIndex h L.val.val.1) j.val hK) hz).eq_of_nhds
  exact congrArg (fun v : ProblemStatement.Space => v i) he.symm

omit G in
theorem pressure_periodized_zero {N : ℕ} (L : F.Label) (j : PhysicalWaveSum.Harmonic N)
    (hj : j.val = 0) (a : ℝ) (w : ProblemStatement.SpaceTime) :
    (F.pressureFamily N).periodized a h sys.radius (L.val, j) w = 0 := by
  simp only [PhysicalCopyBounds.CopyFamily.periodized, PhysicalCopyBounds.CopyFamily.term,
    PhysicalCopyBounds.CopyFamily.copy, PhysicalWaveSum.WaveFamily.term,
    PhysicalWaveSum.globalWave, PhysicalWaveSum.commonWave, pressureFamily,
    dite_eq_left L.property, hj, ite_true, zero_mul, tsum_zero]

omit G in
theorem potential_periodized_zero {N : ℕ} (L : F.Label) (j : PhysicalWaveSum.Harmonic N)
    (hj : j.val = 0) (i : Fin 3) (a : ℝ) (w : ProblemStatement.SpaceTime) :
    (F.potentialFamily N i).periodized a h sys.radius (L.val, j) w = 0 := by
  simp only [PhysicalCopyBounds.CopyFamily.periodized, PhysicalCopyBounds.CopyFamily.term,
    PhysicalCopyBounds.CopyFamily.copy, PhysicalWaveSum.WaveFamily.term,
    PhysicalWaveSum.globalWave, PhysicalWaveSum.commonWave, potentialFamily,
    dite_eq_left L.property, hj, ite_true, zero_mul, tsum_zero]

/-- The complete finite harmonic sum is the same original label pressure. -/
theorem labelPressure_eq_copy_sum (hh : 0 ≤ h) (N : ℕ) (L : F.Label)
    {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (chart : PolarCharts.Index) (z : ProblemStatement.SpaceTime)
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical δ chart)
    (hw : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a chart)
    (m : ℤ) (hm : (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = (m : ℝ))
    (hp : (nativeMap h (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) z).1.1 ∈ U L) :
    (∑ j : PhysicalWaveSum.Harmonic N,
      ((F.pressureFamily N).periodized a h sys.radius (L.val, j)
        (z.1, CylindricalResidual.chart z.2)).re) =
      labelPressure (F.data L) h (ChartScales.Q L.val.val.1)
        (ChartScales.nativeIndex h L.val.val.1) δ N (z.1, CylindricalResidual.chart z.2) := by
  trans ∑ j : PhysicalWaveSum.Harmonic N, if j.val = 0 then 0 else
    PhysicalParticularWave.physicalPressure (F.data L) h (ChartScales.Q L.val.val.1)
      (ChartScales.nativeIndex h L.val.val.1) δ j.val (z.1, CylindricalResidual.chart z.2)
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val = 0
    · rw [ite_eq_left hj, F.pressure_periodized_zero L j hj, Complex.zero_re]
    · rw [ite_eq_right hj]
      exact F.pressure_periodized_physical G hh L j hj ha hδ chart z hz hw hchart m hm hp
  · exact sum_harmonic_nonzero N (fun j => PhysicalParticularWave.physicalPressure (F.data L) h
      (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) δ j
        (z.1, CylindricalResidual.chart z.2))

/-- Every Cartesian component of the complete label potential is exactly
the finite harmonic sum of the actual physical copy family. -/
theorem labelPotential_eq_copy_sum (hh : 0 ≤ h) (N : ℕ) (L : F.Label) (i : Fin 3)
    {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (chart : PolarCharts.Index) (z : ProblemStatement.SpaceTime)
    (hz : z ∈ PhysicalCurlCovariance.validCylindrical δ chart)
    (hw : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PhysicalGraphBounds.annulus a b)
    (hchart : PhysicalGraphBounds.scaledRadial L.val.val.1 (z.1, CylindricalResidual.chart z.2) ∈
      PolarCharts.chartDomain a chart)
    (m : ℤ) (hm : (ChartScales.carrier h L.val.val.1 : ℝ) * F.phase.p L = (m : ℝ))
    (hp : (nativeMap h (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) z).1.1 ∈ U L)
    (hΦ : DifferentiableAt ℝ (referencePhase (F.data L) 1)
      (nativeMap h (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) z)) :
    (∑ j : PhysicalWaveSum.Harmonic N,
      ((F.potentialFamily N i).periodized a h sys.radius (L.val, j)
        (z.1, CylindricalResidual.chart z.2)).re) =
      labelPotential (F.data L) h (ChartScales.Q L.val.val.1)
        (ChartScales.nativeIndex h L.val.val.1) δ N (z.1, CylindricalResidual.chart z.2) i := by
  trans ∑ j : PhysicalWaveSum.Harmonic N, if j.val = 0 then 0 else
    PhysicalParticularWave.physicalPotential (F.data L) h (ChartScales.Q L.val.val.1)
      (ChartScales.nativeIndex h L.val.val.1) δ j.val (z.1, CylindricalResidual.chart z.2) i
  · apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val = 0
    · rw [ite_eq_left hj, F.potential_periodized_zero L j hj, Complex.zero_re]
    · rw [ite_eq_right hj]
      exact F.potential_periodized_physical G hh L j hj i ha hδ chart z hz hw hchart m hm hp hΦ
  · rw [labelPotential, WithLp.ofLp_sum, Finset.sum_apply]
    exact sum_harmonic_nonzero N (fun j => PhysicalParticularWave.physicalPotential (F.data L) h
      (ChartScales.Q L.val.val.1) (ChartScales.nativeIndex h L.val.val.1) δ j
        (z.1, CylindricalResidual.chart z.2) i)

end ReferenceFamily

/-! ## The actual fixed choice and current residual -/

section Actual

open CorrectionInitialization CorrectionInitialization.ActualPrimary

variable {B N0 : ℕ}

noncomputable def actualBandLabel (l : ActualParticularStageControls.Label B N0) : BandLabel :=
  ⟨ActualParticularStageControls.spatialLabel l,
    ((choice B N0).prepared.large (BaseChartJets.cellBand l.2) l.2.property).four_le⟩

theorem actualBandLabel_injective : Function.Injective (actualBandLabel (B := B) (N0 := N0)) := by
  rintro ⟨j, L⟩ ⟨k, M⟩ he
  have hs := congrArg Subtype.val he
  change PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal L) j =
    PartitionedCovariance.signedLabel (PrimaryGeometryAssembly.label nominal M) k at hs
  have hfirst : (PrimaryGeometryAssembly.label nominal L).1 =
      (PrimaryGeometryAssembly.label nominal M).1 :=
    congrArg (fun q : SlotColoring.Label => q.1) hs
  have hsecond : (PrimaryGeometryAssembly.label nominal L).2 =
      (PrimaryGeometryAssembly.label nominal M).2 :=
    congrArg (fun q : SlotColoring.Label => q.2.1) hs
  have hl : PrimaryGeometryAssembly.label nominal L = PrimaryGeometryAssembly.label nominal M :=
    Prod.ext hfirst hsecond
  have hLM := PrimaryGeometryAssembly.label_injective nominal hl
  subst M
  have hj := PartitionedCovariance.signedLabel_injective _ hs
  subst k
  rfl

noncomputable def actualIndex
    (L : {L : BandLabel // L ∈ Set.range (actualBandLabel (B := B) (N0 := N0))}) :
    ActualParticularStageControls.Label B N0 := Classical.choose L.property

theorem actualIndex_label
    (L : {L : BandLabel // L ∈ Set.range (actualBandLabel (B := B) (N0 := N0))}) :
    actualBandLabel (actualIndex L) = L.val := Classical.choose_spec L.property

theorem actualIndex_of_label (l : ActualParticularStageControls.Label B N0) :
    actualIndex ⟨actualBandLabel l, ⟨l, rfl⟩⟩ = l :=
  actualBandLabel_injective (actualIndex_label _)

/-- The construction selects no replacement reference: the index inverse
recovers the same original signed label, and the forcing is the current
residual pulled back to that reference's native cover. -/
noncomputable def actualFamily (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0)) :
    ReferenceFamily slots where
  active := Set.range (actualBandLabel (B := B) (N0 := N0))
  data L := ActualReferenceRebase.nativeAssembly x (actualIndex L)
  phase := {
    epsilon L := ((phases B N0 (actualIndex L).1).phase).epsilon (actualIndex L).2
    p L := ((phases B N0 (actualIndex L).1).phase).p (actualIndex L).2
    pz L := ((phases B N0 (actualIndex L).1).phase).pz (actualIndex L).2
    x0 L := ((phases B N0 (actualIndex L).1).phase).x0 (actualIndex L).2
    theta L := ((phases B N0 (actualIndex L).1).phase).theta (actualIndex L).2
    F L := ((phases B N0 (actualIndex L).1).phase).F (actualIndex L).2
    G L := ((phases B N0 (actualIndex L).1).phase).G (actualIndex L).2 }
  band L := by
    rw [← actualIndex_label L]
    rfl
  geometry L := by
    rw [← actualIndex_label L]
    rfl
  cutoff_support L := by
    rw [← actualIndex_label L]
    intro z hz
    change (ActualParticularStageControls.referenceCutoff (actualIndex L)) z ≠ 0 at hz
    have hc := (mul_ne_zero_iff.mp hz).1
    change z ∈ (clockWindow (actualIndex L).2).outer
    exact (clockWindow (actualIndex L).2).cutoff_support hc
  length L := by
    rw [← actualIndex_label L]
    rfl
  cutoff_time L z hz := by
    change ActualParticularStageControls.referenceCutoff (actualIndex L) z ≠ 0 at hz
    have ht := (mul_ne_zero_iff.mp hz).2
    have hlen := (phases B N0 (actualIndex L).1).L_pos (actualIndex L).2
    have hd : |z.2 - (phases B N0 (actualIndex L).1).L (actualIndex L).2 / 2| <
        (phases B N0 (actualIndex L).1).L (actualIndex L).2 / 3 := by
      by_contra! hn
      exact ht (GaussianTailFlat.slotCutoff_zero hlen hn)
    have hv := abs_lt.mp hd
    change z.2 ∈ Icc 0 ((phases B N0 (actualIndex L).1).L (actualIndex L).2)
    exact ⟨by linarith, by linarith⟩

theorem actualFamily_data (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) :
    (actualFamily x).data ⟨actualBandLabel l, ⟨l, rfl⟩⟩ =
      ActualReferenceRebase.nativeAssembly x l := by
  change ActualReferenceRebase.nativeAssembly x (actualIndex _) = _
  erw [actualIndex_of_label]

theorem actualFamily_source (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) :
    referenceSource ((actualFamily x).data ⟨actualBandLabel l, ⟨l, rfl⟩⟩) j =
      ActualReferenceRebase.referenceResidualSource x l j := by
  rw [actualFamily_data]
  exact ActualReferenceRebase.nativeAssembly_source x l j

noncomputable def actualLabelPotential
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (δ : ℝ) (N : ℕ) : ProblemStatement.VelocityField :=
  labelPotential (ActualReferenceRebase.nativeAssembly x l) h
    (ChartScales.Q (BaseChartJets.cellBand l.2))
    (ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) δ N

noncomputable def actualLabelPressure
    (x : CorrectionStep.CycleState (ActualParticularStageControls.Label B N0))
    (l : ActualParticularStageControls.Label B N0) (δ : ℝ) (N : ℕ) : ProblemStatement.PressureField :=
  labelPressure (ActualReferenceRebase.nativeAssembly x l) h
    (ChartScales.Q (BaseChartJets.cellBand l.2))
    (ChartScales.nativeIndex h (BaseChartJets.cellBand l.2)) δ N

end Actual

end NavierStokes.ActualParticularPhysicalData
