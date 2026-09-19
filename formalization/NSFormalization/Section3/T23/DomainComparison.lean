import NSFormalization.Section3.T23.DomainNorms
import NSFormalization.Section3.T22.ZeroExtensionComparison

/-!
# T23 domain/zero-extension comparison

The fixed-compact-support T22 comparison is integrated in time here.  Smooth
slice and fixed-support facts are explicit parameters so parallel T23 lanes can
supply them during final assembly.
-/

noncomputable section

namespace NSFormalization.Section3.T23

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section4.D01 (sobolevENorm)
open NSFormalization.Section3.T22
open scoped ContDiff ENNReal Topology

/-- Pointwise support in a closed set implies the corresponding support of the
literal zero extension is contained in that same set.  This is the bridge from
U4's all-time nonvanishing statement to T22's `tsupport` hypothesis. -/
theorem tsupport_zeroExtension_subset_of_pointwise_support
    {Ω K : Set Space} {z : SpatialField} (hK : IsClosed K)
    (hz : ∀ x : Space, z x ≠ 0 → x ∈ K) :
    tsupport (zeroExtension Ω z) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  apply hz x
  intro hzx
  apply hx
  simp [zeroExtension, hzx]

/-- A bounded-domain force is smooth on every positive-time spatial slice.
This extracts precisely the slice regularity consumed by T22 from U3's
`forceDifference_mem` field. -/
theorem contDiffOn_slice_of_memForceOmega {Ω : Set Space} {f : SpaceTimeField}
    (hf : f ∈ forceClassOmega Ω) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    ContDiffOn ℝ ∞ (fun x ↦ f (t, x)) Ω := by
  intro x hx
  exact ((hf.1 t).contDiffAt_slice ⟨ht.le, le_rfl⟩ (subset_closure hx)).contDiffWithinAt

/-- The order-zero domain norm of a smooth force-difference slice is its
physical restricted `L²(Ω)` norm. -/
theorem domainForceDifference_orderZero
    {Ω : Set Space} (norms : BoundedDomainNormAPI)
    {ε₀ : ℝ} {force : ℝ → SpaceTimeField} {g : SpaceTimeField}
    (hΩ : IsOpen Ω)
    (hforce : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (fun z ↦ force ε z - g z) ∈ forceClassOmega Ω) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioi (0 : ℝ),
      domainSobolevENorm Ω 0
          (restrictField Ω (fun x ↦ force ε (t, x) - g (t, x))) =
        eLpNorm (fun x ↦ force ε (t, x) - g (t, x)) 2
          (volume.restrict Ω) := by
  intro ε hε t ht
  exact norms.orderZero Ω hΩ _
    (contDiffOn_slice_of_memForceOmega (hforce ε hε) ht)

/-- **T23 U5.** Integrate the registered T22 comparison for the actual force
difference.  The compact set is the fixed closure of the prescribed ball, so
the constant is selected once for `s`, before both time and `ε`.  No finiteness
of either extended norm is assumed. -/
theorem domain_zeroExt_comparison
    {Ω : Set Space} (norms : BoundedDomainNormAPI)
    {ε₀ : ℝ} {force : ℝ → SpaceTimeField} {g : SpaceTimeField}
    {c : Space} {R : ℝ}
    (hΩ : IsOpen Ω) (hR : 0 < R)
    (hball : closure (Metric.ball c R) ⊆ Ω)
    (hforce : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (fun z ↦ force ε z - g z) ∈ forceClassOmega Ω)
    (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ∀ t : ℝ, ∀ x : Space, force ε (t, x) - g (t, x) ≠ 0 →
        x ∈ closure (Metric.ball c R)) :
    ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
          zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ∧
      zeroExtForceSobolevENorm Ω s (fun z ↦ force ε z - g z) ≤
          ENNReal.ofReal C *
            domainForceSobolevENorm Ω s (fun z ↦ force ε z - g z) := by
  intro s
  have hcompact : IsCompact (closure (Metric.ball c R)) := by
    rw [closure_ball c hR.ne']
    exact prescribed_closedBall_compact c R
  obtain ⟨C, hC, hcomparison⟩ :=
    norms.zeroExtensionComparison Ω (closure (Metric.ball c R))
      hΩ hcompact hball s
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have hslice (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :=
    hcomparison (fun x ↦ force ε (t, x) - g (t, x))
      (contDiffOn_slice_of_memForceOmega (hforce ε hε) ht)
      (tsupport_zeroExtension_subset_of_pointwise_support isClosed_closure
        (hsupport ε hε t))
  constructor
  · rw [domainForceSobolevENorm_eq, zeroExtForceSobolevENorm_eq]
    exact setLIntegral_mono' measurableSet_Ioi (fun t ht ↦ (hslice t ht).1)
  · rw [domainForceSobolevENorm_eq, zeroExtForceSobolevENorm_eq]
    calc
      (∫⁻ t in Ioi (0 : ℝ),
          sobolevENorm s
            (zeroExtension Ω (fun x ↦ force ε (t, x) - g (t, x)))) ≤
          ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C *
            domainSobolevENorm Ω s
              (restrictField Ω (fun x ↦ force ε (t, x) - g (t, x))) :=
        setLIntegral_mono' measurableSet_Ioi (fun t ht ↦ (hslice t ht).2)
      _ = ENNReal.ofReal C *
          ∫⁻ t in Ioi (0 : ℝ),
            domainSobolevENorm Ω s
              (restrictField Ω (fun x ↦ force ε (t, x) - g (t, x))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end NSFormalization.Section3.T23
