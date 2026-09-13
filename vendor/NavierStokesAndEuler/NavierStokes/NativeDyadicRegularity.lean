import NavierStokes.ActualCoreSupport
import NavierStokes.ActualReferenceRebase

/-!
# Literal dyadic-face values and regularity

The native dyadic faces are not contained in the open common-band domain.
The results below start from the actual cutoff factors and the actual copy
formulas.  No value at a face is assigned by choosing an unrelated extension.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff BigOperators

namespace NavierStokes.NativeDyadicRegularity

open CorrectionInitialization

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

section FlatCalculus

variable {D E F G : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Smoothness and vanishing of every actual Fréchet tensor at the point. -/
structure FlatAt (f : D → E) (x : D) : Prop where
  smooth : ContDiffAt ℝ ∞ f x
  jets : ∀ n : ℕ, iteratedFDeriv ℝ n f x = 0

theorem FlatAt.value {f : D → E} {x : D} (hf : FlatAt f x) : f x = 0 := by
  apply norm_eq_zero.mp
  simpa only [norm_iteratedFDeriv_zero, norm_zero] using congrArg norm (hf.jets 0)

theorem FlatAt.of_germ {f : D → E} {x : D} (hf : f =ᶠ[𝓝 x] fun _ => 0) :
    FlatAt f x := by
  refine ⟨contDiffAt_const.congr_of_eventuallyEq hf, fun n => ?_⟩
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hf n, iteratedFDeriv_fun_zero]
  simp only [Pi.zero_apply]

theorem FlatAt.congr {f g : D → E} {x : D} (hf : FlatAt f x)
    (hg : g =ᶠ[𝓝 x] f) : FlatAt g x := by
  refine ⟨hf.smooth.congr_of_eventuallyEq hg, fun n => ?_⟩
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hg n, hf.jets n]

private theorem finite_neighborhood {f : D → E} {x : D}
    (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ∃ s : Set D, IsOpen s ∧ x ∈ s ∧ ContDiffOn ℝ n f s := by
  obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (nat_le_infty n) (by simp)
  obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨u, hu, hxu, hfs.mono hus⟩

/-- Flatness survives the literal smooth coordinate pullback. -/
theorem FlatAt.comp {f : E → F} {g : D → E} {x : D}
    (hf : FlatAt f (g x)) (hg : ContDiff ℝ ∞ g) : FlatAt (f ∘ g) x := by
  refine ⟨hf.smooth.comp x hg.contDiffAt, fun n => ?_⟩
  obtain ⟨s, hs, hxs, hfs⟩ := finite_neighborhood hf.smooth n
  let K : ℝ := 1 + ∑ j ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ j g x‖
  have hK : 1 ≤ K := by
    dsimp only [K]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hbound (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j g x‖ ≤ K := by
    have hsum := Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j g x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact hsum.trans (le_add_of_nonneg_left (by norm_num))
  have hpre := hs.preimage hg.continuous
  have hb := norm_iteratedFDerivWithin_comp_le hfs
    ((hg.of_le (nat_le_infty n)).contDiffOn : ContDiffOn ℝ n g (g ⁻¹' s))
    (n := n) (by rfl) hs.uniqueDiffOn hpre.uniqueDiffOn (fun _ hx => hx) hxs
    (C := 0) (D := K)
    (by intro j hj; rw [iteratedFDerivWithin_of_isOpen j hs hxs, hf.jets j]; simp)
    (by
      intro j hj hjn
      rw [iteratedFDerivWithin_of_isOpen j hpre hxs]
      exact (hbound j hjn).trans (by simpa only [pow_one] using pow_le_pow_right₀ hK hj))
  rw [iteratedFDerivWithin_of_isOpen n hpre hxs] at hb
  exact norm_eq_zero.mp (le_antisymm (by simpa only [mul_zero, zero_mul] using hb) (norm_nonneg _))

theorem FlatAt.map {f : D → E} {x : D} (hf : FlatAt f x) (L : E →L[ℝ] F) :
    FlatAt (L ∘ f) x := by
  refine ⟨L.contDiff.contDiffAt.comp x hf.smooth, fun n => ?_⟩
  have hb := PhysicalWaveSum.norm_jet_linear_comp_at (hf.smooth.of_le (nat_le_infty n)) L
  rw [hf.jets n, norm_zero, mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

theorem FlatAt.fderiv {f : D → E} {x : D} (hf : FlatAt f x) :
    FlatAt (fderiv ℝ f) x := by
  refine ⟨hf.smooth.fderiv_right (by simp), fun n => ?_⟩
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_fderiv, hf.jets (n + 1), norm_zero]

/-- A smooth bilinear product remains flat when its second factor is flat. -/
theorem FlatAt.bilinear_right {a : D → E} {b : D → F} {x : D}
    (B : E →L[ℝ] F →L[ℝ] G) (ha : ContDiffAt ℝ ∞ a x) (hb : FlatAt b x) :
    FlatAt (fun y => B (a y) (b y)) x := by
  refine ⟨(B.contDiff.contDiffAt.comp x ha).clm_apply hb.smooth, fun n => ?_⟩
  obtain ⟨s, hs, hxs, has⟩ := finite_neighborhood ha n
  obtain ⟨t, ht, hxt, hbt⟩ := finite_neighborhood hb.smooth n
  have he := B.norm_iteratedFDerivWithin_le_of_bilinear
    (has.mono (inter_subset_left (t := t))) (hbt.mono (inter_subset_right (s := s)))
    (hs.inter ht).uniqueDiffOn (show x ∈ s ∩ t from ⟨hxs, hxt⟩) (n := n) (by rfl)
  simp only [iteratedFDerivWithin_of_isOpen _ (hs.inter ht) ⟨hxs, hxt⟩,
    hb.jets, norm_zero, mul_zero, Finset.sum_const_zero] at he
  exact norm_eq_zero.mp (le_antisymm he (norm_nonneg _))

theorem FlatAt.bilinear_left {a : D → E} {b : D → F} {x : D}
    (B : E →L[ℝ] F →L[ℝ] G) (ha : FlatAt a x) (hb : ContDiffAt ℝ ∞ b x) :
    FlatAt (fun y => B (a y) (b y)) x :=
  FlatAt.bilinear_right B.flip hb ha

theorem FlatAt.const_smul {f : D → E} {x : D} (hf : FlatAt f x) (c : ℝ) :
    FlatAt (fun y => c • f y) x := by
  simpa only [Function.comp_def, _root_.smul_apply,
    ContinuousLinearMap.id_apply] using hf.map (c • ContinuousLinearMap.id ℝ E)

theorem FlatAt.smul {a : D → ℝ} {b : D → E} {x : D}
    (ha : ContDiffAt ℝ ∞ a x) (hb : FlatAt b x) :
    FlatAt (fun y => a y • b y) x :=
  FlatAt.bilinear_right (ContinuousLinearMap.lsmul ℝ ℝ) ha hb

end FlatCalculus

abbrev Point := LocalSignedRequest.Point
abbrev FullPoint := ActualPrimary.FullPoint
abbrev Index (B N0 : ℕ) := ActualInitialization.Index B N0

section InitialNative

variable {B N0 : ℕ}

/-- The literal attached seed fields are smooth and flat at both native
dyadic faces, including intersections with radial attachment boundaries. -/
theorem initial_native_flat (l : Index B N0) {x : ActualSignedGeometry.Native}
    (hT : 0 < x.1.2.2)
    (he : SimilarityHomogeneity.chartQ ActualPrimary.h x.1 = 1 / 2 ∨
      SimilarityHomogeneity.chartQ ActualPrimary.h x.1 = 2) :
    FlatAt (ActualPrimary.attachedRawVelocity l.2 l.1) x ∧
      FlatAt (ActualPrimary.attachedRawPressure l.2 l.1) x := by
  have hv := (ActualPrimary.attachedRawVelocity_smooth B N0 l.2 l.1).contDiffAt
    (WaveEdgeExtension.nativeSlowDomain_open.mem_nhds hT)
  have hp := (ActualPrimary.attachedRawPressure_smooth B N0 l.2 l.1).contDiffAt
    (WaveEdgeExtension.nativeSlowDomain_open.mem_nhds hT)
  exact ⟨⟨hv, fun n => (ActualPrimary.attachedPair_band_edge_jets l.2 l.1 hT he n).1⟩,
    ⟨hp, fun n => (ActualPrimary.attachedPair_band_edge_jets l.2 l.1 hT he n).2⟩⟩

theorem copyPoint_smooth (l : Index B N0) (n : ℕ) (k : TorusInverse.Frequency) :
    ContDiff ℝ ∞ (ActualPrimaryDynamics.copyPoint l.2 l.1 n k) := by
  have he : ActualPrimaryDynamics.copyPoint l.2 l.1 n k = fun x =>
      ActualPrimaryDynamics.copyLinear l.2 l.1 n x +
        (0, (ActualPrimary.geometry l.2 l.1).coordinates k 0) :=
    funext (ActualPrimaryDynamics.copyPoint_affine l.2 l.1 n k)
  rw [he]
  exact (ActualPrimaryDynamics.copyLinear l.2 l.1 n).contDiff.add contDiff_const

/-- Copying uses the same slow point on the whole fast fiber. -/
theorem initial_copy_flat (l : Index B N0) (n : ℕ) (k : TorusInverse.Frequency)
    {x : FullPoint} (hT : 0 < x.1.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x.1 = 1 / 2 ∨
      ActualCoreSupport.nativeQ l n x.1 = 2) :
    FlatAt (fun y => ActualPrimary.attachedRawVelocity l.2 l.1
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k y)) x ∧
    FlatAt (fun y => ActualPrimary.attachedRawPressure l.2 l.1
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k y)) x := by
  obtain ⟨hv, hp⟩ := initial_native_flat l
    (ActualPrimaryDynamics.copyPoint_time_pos l.2 l.1 n k hT) he
  exact ⟨hv.comp (copyPoint_smooth l n k), hp.comp (copyPoint_smooth l n k)⟩

/-- Periodization retains the literal flat jets, using the unique active
copy germ, or the zero germ when there is no active copy. -/
theorem initial_chart_flat (l : Index B N0) (n : ℕ) {x : FullPoint}
    (hT : 0 < x.1.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x.1 = 1 / 2 ∨
      ActualCoreSupport.nativeQ l n x.1 = 2) :
    FlatAt ((ActualPrimary.chartCoefficients l.2 l.1).amplitude n) x ∧
      FlatAt ((ActualPrimary.chartCoefficients l.2 l.1).pressure n) x := by
  classical
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x).2 ∈ (ActualPrimary.clockWindow l.1).core
  · obtain ⟨k, hk⟩ := hc
    obtain ⟨hv, hp⟩ := initial_copy_flat l n k hT he
    have hv' := (hv.map CurlClassBounds.complexify).const_smul
      (ActualPrimaryDynamics.velocityScale l.1 n)
    have hp' := hp.const_smul (ActualPrimaryDynamics.velocityScale l.1 n ^ 2)
    exact ⟨hv'.congr (ActualPrimaryDynamics.amplitude_germ l.2 l.1 n k hk),
      hp'.congr (ActualPrimaryDynamics.pressure_germ l.2 l.1 n k hk)⟩
  · obtain ⟨hv, hp⟩ := ActualPrimaryDynamics.coefficient_zero_germs l.2 l.1 n (not_exists.mp hc)
    exact ⟨FlatAt.of_germ hv, FlatAt.of_germ hp⟩

/-- The Gaussian cutoff multiplies the actual chart coefficients and thus
preserves all dyadic-face jets. -/
theorem initial_cut_flat (l : Index B N0) (n : ℕ) {x : FullPoint}
    (hT : 0 < x.1.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x.1 = 1 / 2 ∨
      ActualCoreSupport.nativeQ l n x.1 = 2) :
    FlatAt (((ActualPrimary.chartCoefficients l.2 l.1).withCutoff
      (ActualPrimary.chartCutoff l.2 l.1)).amplitude n) x ∧
    FlatAt (((ActualPrimary.chartCoefficients l.2 l.1).withCutoff
      (ActualPrimary.chartCutoff l.2 l.1)).pressure n) x := by
  obtain ⟨hv, hp⟩ := initial_chart_flat l n hT he
  have hc := (ActualInitialization.cutoff_smooth l n).contDiffAt (x := x)
  exact ⟨FlatAt.smul hc hv, FlatAt.smul hc hp⟩

theorem initial_native_gaussian_flat (l : Index B N0) {x : ActualSignedGeometry.Native}
    (hT : 0 < x.1.2.2)
    (he : SimilarityHomogeneity.chartQ ActualPrimary.h x.1 = 1 / 2 ∨
      SimilarityHomogeneity.chartQ ActualPrimary.h x.1 = 2) :
    FlatAt (ActualInitialExcluded.nativeGaussian (l.2,l.1)) x := by
  have hv := (initial_native_flat l hT he).1.map CurlClassBounds.complexify
  have hg := ((ActualInitialExcluded.nativeGaussian_smooth l.1).contDiffAt (x := x)).fderiv_right
    (show (∞ : WithTop ℕ∞) + 1 ≤ ∞ by simp)
  exact FlatAt.smul (hg.clm_apply contDiffAt_const) hv

/-- This is the genuine excluded-slot error, including the derivative of
the Gaussian cutoff; its face values and all mixed jets vanish. -/
theorem initial_chart_gaussian_flat (l : Index B N0) (n : ℕ) {x : FullPoint}
    (hT : 0 < x.1.2.1.1)
    (he : ActualCoreSupport.nativeQ l n x.1 = 1 / 2 ∨
      ActualCoreSupport.nativeQ l n x.1 = 2) :
    FlatAt (ActualInitialExcluded.chartGaussian (l.2,l.1) n) x := by
  classical
  by_cases hc : ∃ k : TorusInverse.Frequency,
      (ActualPrimaryDynamics.copyPoint l.2 l.1 n k x).2 ∈ (ActualPrimary.clockWindow l.1).core
  · obtain ⟨k, hk⟩ := hc
    have hg := initial_native_gaussian_flat l
      (ActualPrimaryDynamics.copyPoint_time_pos l.2 l.1 n k hT) he
    have hgc := (hg.comp (copyPoint_smooth l n k)).const_smul
      (ActualPrimaryBounds.coefficientScale (2 * CoordinateAlgebra.A ActualPrimary.h + 1 / 2)
        (l.2,l.1) n)
    exact hgc.congr (ActualInitialExcluded.chartGaussian_germ (l.2,l.1) n k hk)
  · exact FlatAt.of_germ
      (ActualInitialExcluded.chartGaussian_zero_no_copy (l.2,l.1) n (not_exists.mp hc))

end InitialNative

section ActualFastSolve

open ParticularWaveBounds CommonCoverSolve TorusInverse HarmonicCalculus

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Zero on the complete fast fiber implies literal zero velocity in every
copy, without any continuity assumption or restriction on the current clock. -/
theorem complexCopyVelocity_zero_fiber (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (p : P) (Y : Plane) (hf : ∀ Z, f (p,Z) = 0) :
    complexCopyVelocity t f g hab k (p,Y) = 0 :=
  complexCopyVelocity_zero_of_path t f g hab k p Y (fun v _ => hf (g.path k Y v))

/-- The pressure also sees the source at the current point. Full-fiber zero
supplies that value even when the current clock is outside the path interval. -/
theorem complexCopyPressure_zero_fiber (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (K : ℝ) (p : P) (Y : Plane) (hf : ∀ Z, f (p,Z) = 0) :
    complexCopyPressure t f g hab k K (p,Y) = 0 := by
  have hr := copyPressure_zero_of_path (realData t f) g hab k K p Y
    (fun v _ => by change ParticularWaveBounds.realPart (f (p,g.path k Y v)) = 0; rw [hf, map_zero])
    (by change ParticularWaveBounds.realPart (f (p,Y)) = 0; rw [hf, map_zero])
  have hi := copyPressure_zero_of_path (imagData t f) g hab k K p Y
    (fun v _ => by change imagPart (f (p,g.path k Y v)) = 0; rw [hf, map_zero])
    (by change imagPart (f (p,Y)) = 0; rw [hf, map_zero])
  simp only [complexCopyPressure, hr, hi, mul_zero, add_zero]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem realData_const_smul (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (c : ℝ) :
    realData t (fun z => c • f z) = scaleTangentSource (realData t f) c := by
  simp only [realData, scaleTangentSource, map_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem imagData_const_smul (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (c : ℝ) :
    imagData t (fun z => c • f z) = scaleTangentSource (imagData t f) c := by
  simp only [imagData, scaleTangentSource, map_smul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyVelocity_const_smul (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (c : ℝ) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (z : P × Plane) :
    complexCopyVelocity t (fun z => c • f z) g hab k z =
      c • complexCopyVelocity t f g hab k z := by
  simp only [complexCopyVelocity, realData_const_smul, imagData_const_smul,
    copyVelocity_scaleSource, smul_add, smul_comm Complex.I c]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyPressure_const_smul (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (c : ℝ) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (K : ℝ) (z : P × Plane) :
    complexCopyPressure t (fun z => c • f z) g hab k K z =
      c • complexCopyPressure t f g hab k K z := by
  simp only [complexCopyPressure, realData_const_smul, imagData_const_smul,
    copyPressure_scaleSource, smul_add, Complex.real_smul]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- A slow parameter factor is constant on every actual integration path.
This is a literal identity for the finite-path solver, with no smoothness or
integrability assumption on either factor. -/
theorem complexCopyVelocity_slow_factor (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (c : P → ℝ) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (p : P) (Y : Plane) :
    complexCopyVelocity t (fun z => c z.1 • f z) g hab k (p,Y) =
      c p • complexCopyVelocity t f g hab k (p,Y) := by
  calc
    _ = complexCopyVelocity t (fun z => c p • f z) g hab k (p,Y) :=
      ActualReferenceRebase.copyVelocity_source_congr t _ _ g hab p (fun _ => rfl) k Y
    _ = _ := complexCopyVelocity_const_smul t f (c p) g hab k (p,Y)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem complexCopyPressure_slow_factor (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (c : P → ℝ) (g : Geometry) {a b : ℝ} (hab : a ≤ b)
    (k : Frequency) (K : ℝ) (p : P) (Y : Plane) :
    complexCopyPressure t (fun z => c z.1 • f z) g hab k K (p,Y) =
      c p • complexCopyPressure t f g hab k K (p,Y) := by
  calc
    _ = complexCopyPressure t (fun z => c p • f z) g hab k K (p,Y) :=
      ActualReferenceRebase.copyPressure_source_congr t _ _ g hab p (fun _ => rfl) k K Y
    _ = _ := complexCopyPressure_const_smul t f (c p) g hab k K (p,Y)

/-- Only primitive inputs occur in this regularity package.  In particular,
neither the solved velocity nor the solved pressure is assumed smooth. -/
structure CopySmoothInputs (t : TangentData P ProblemStatement.Space)
    (f : P × Plane → ComplexVector) (U : Set P) : Prop where
  coefficient : ContDiffOn ℝ ∞ t.linearData.coefficient (U ×ˢ univ)
  forcingMap : ContDiffOn ℝ ∞ t.linearData.forcingMap (U ×ˢ univ)
  source : ContDiffOn ℝ ∞ f (U ×ˢ univ)
  normal : ContDiffOn ℝ ∞ t.normal (U ×ˢ univ)
  normalDot : ContDiffOn ℝ ∞ t.normalDot (U ×ˢ univ)
  action : ContDiffOn ℝ ∞ t.action (U ×ˢ univ)

/-- Smooth primitive inputs on a neighborhood of the entire fast fiber
give smoothness of the literal velocity and pressure at every interior
clock point. This also applies at a slow dyadic face. -/
theorem CopySmoothInputs.copy_smooth {t : TangentData P ProblemStatement.Space}
    {f : P × Plane → ComplexVector} {U : Set P} (H : CopySmoothInputs t f U)
    (hU : IsOpen U) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency)
    (K : ℝ) {z : P × Plane} (hz : z.1 ∈ U)
    (hc : (g.coordinates k z.2).2 ∈ Ioo a b)
    (hn : t.normal (nativePoint g k z) ≠ 0) :
    ContDiffAt ℝ ∞ (complexCopyVelocity t f g hab k) z ∧
      ContDiffAt ℝ ∞ (complexCopyPressure t f g hab k K) z := by
  have hfr : ContDiffOn ℝ ∞ (realData t f).source (U ×ˢ univ) :=
    ParticularWaveBounds.realPart.contDiff.comp_contDiffOn H.source
  have hfi : ContDiffOn ℝ ∞ (imagData t f).source (U ×ˢ univ) :=
    ParticularWaveBounds.imagPart.contDiff.comp_contDiffOn H.source
  have hr := (realData t f).linearData.copySolve_contDiffAt g hab hU k
    H.coefficient H.forcingMap hfr hz hc
  have hi := (imagData t f).linearData.copySolve_contDiffAt g hab hU k
    H.coefficient H.forcingMap hfi hz hc
  have hg : ContDiff ℝ ∞ (nativePoint (P := P) g k) :=
    contDiff_fst.prodMk ((g.coordinates_contDiff k).comp contDiff_snd)
  have hdom := (hU.prod isOpen_univ).mem_nhds (show z ∈ U ×ˢ univ from ⟨hz, trivial⟩)
  have hnative := (hU.prod isOpen_univ).mem_nhds
    (show nativePoint g k z ∈ U ×ˢ univ from ⟨hz, trivial⟩)
  have hN := (H.normal.contDiffAt hnative).comp z hg.contDiffAt
  have hNd := (H.normalDot.contDiffAt hnative).comp z hg.contDiffAt
  have hA := (H.action.contDiffAt hnative).comp z hg.contDiffAt
  have hpr := NativeBandExtension.projectedPressure_contDiffAt K hN hNd hr
    (hA.clm_apply hr) (hfr.contDiffAt hdom) hn
  have hpi := NativeBandExtension.projectedPressure_contDiffAt K hN hNd hi
    (hA.clm_apply hi) (hfi.contDiffAt hdom) hn
  constructor
  · exact (CurlClassBounds.complexify.contDiff.contDiffAt.comp z hr).add
      ((CurlClassBounds.complexify.contDiff.contDiffAt.comp z hi).const_smul Complex.I)
  · exact hpr.add (contDiffAt_const.mul hpi)

/-- A genuine dyadic factor produces a smooth flat extension through both
faces for the actual solves.  The quotient source and primitive ODE inputs
must be smooth on the stated neighborhood; no output regularity is assumed. -/
theorem CopySmoothInputs.dyadic_flat {t : TangentData P ProblemStatement.Space}
    {f : P × Plane → ComplexVector} {U : Set P} (H : CopySmoothInputs t f U)
    (hU : IsOpen U) (g : Geometry) {a b : ℝ} (hab : a ≤ b) (k : Frequency)
    (K : ℝ) {z : P × Plane} (hz : z.1 ∈ U)
    (hc : (g.coordinates k z.2).2 ∈ Ioo a b)
    (hn : t.normal (nativePoint g k z) ≠ 0)
    (q : P → ℝ) (hq : ContDiffAt ℝ ∞ (fun z : P × Plane => q z.1) z)
    (he : q z.1 = 1 / 2 ∨ q z.1 = 2) :
    FlatAt (complexCopyVelocity t
      (fun z => SquaredPartition.dyadicProfile (q z.1) • f z) g hab k) z ∧
    FlatAt (complexCopyPressure t
      (fun z => SquaredPartition.dyadicProfile (q z.1) • f z) g hab k K) z := by
  obtain ⟨hv, hp⟩ := H.copy_smooth hU g hab k K hz hc hn
  have hfv := NativeBandExtension.dyadic_product_endpoint hq hv he
  have hfp := NativeBandExtension.dyadic_product_endpoint hq hp he
  have hev : complexCopyVelocity t
      (fun z => SquaredPartition.dyadicProfile (q z.1) • f z) g hab k =
      fun z => SquaredPartition.dyadicProfile (q z.1) • complexCopyVelocity t f g hab k z := by
    funext z
    exact complexCopyVelocity_slow_factor t f (fun p => SquaredPartition.dyadicProfile (q p))
      g hab k z.1 z.2
  have hep : complexCopyPressure t
      (fun z => SquaredPartition.dyadicProfile (q z.1) • f z) g hab k K =
      fun z => SquaredPartition.dyadicProfile (q z.1) • complexCopyPressure t f g hab k K z := by
    funext z
    exact complexCopyPressure_slow_factor t f (fun p => SquaredPartition.dyadicProfile (q p))
      g hab k K z.1 z.2
  rw [hev, hep]
  exact ⟨⟨hfv.1, hfv.2⟩, ⟨hfp.1, hfp.2⟩⟩

end ActualFastSolve

end NavierStokes.NativeDyadicRegularity
