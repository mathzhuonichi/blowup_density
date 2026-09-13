import Contracts.V1.Correction
import NSFormalization.Section4.I02.Reference
import NSFormalization.Section4.I02.Support
import NSFormalization.Section4.I02.Energy
import NSFormalization.Section4.I02.Mixed
import NSFormalization.Paper1.InsertionEnergy
import NSFormalization.Paper1.CorrectionEnergy
import NSFormalization.Paper1.CorrectionVectorNorms
import NSFormalization.Source.PhysicalRemoval
import NSFormalization.Source.InsertionFamily

/-! The only layer that knows the current implementation's names and paths for
the correction contract.

`Contracts.V1.Correction` writes out every notion it needs that is neither in
`Contracts.V1.Data` nor in `Contracts.V1.Packet`, so this adapter has two jobs:
record by `rfl` that each locally written notion really is the upstream one, and
assemble the correction, the correction force and their bounds into the
contract.
-/

noncomputable section
namespace BlowupDensity.Bindings

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1 NSFormalization.Paper1.CorrectionProfile
open NSFormalization.Source NSFormalization.Source.PhysicalRemoval
open NSFormalization.Source.PacketScaling
open NSFormalization.Section4.I02
open scoped ContDiff ENNReal Topology

section Correspondence

variable (i j : Fin 3) (A : Contracts.V1.Space → Contracts.V1.Space)
  (a b x x₀ : Contracts.V1.Space) (θ : Contracts.V1.Space → ℝ) (η : ℝ → ℝ)
  (T ε k t₀ c d : ℝ) (u : Contracts.V1.VelocityField) (t : ℝ)

/-- The contract's Jacobian entry is the upstream one. -/
theorem derivativeEntry_eq :
    Contracts.V1.derivativeEntry i j = NavierStokes.SpatialCurl.derivativeEntry i j := rfl

/-- The contract's antisymmetrized Jacobian is the upstream one. -/
theorem curlLinear_eq : Contracts.V1.curlLinear = NavierStokes.SpatialCurl.curlLinear := rfl

/-- The contract's curl is the upstream Euclidean curl. -/
theorem curl_eq : Contracts.V1.curl A x = NavierStokes.SpatialCurl.curl A x := rfl

/-- The contract's cross product is the one in the radial potential. -/
theorem cross_eq : Contracts.V1.cross a b = RadialPotential.cross a b := rfl

/-- The contract's `θ_ε` is the implementation's rescaled spatial cutoff. -/
theorem scaledSpatialCutoff_eq :
    Contracts.V1.scaledSpatialCutoff θ x₀ ε = spatialCutoff θ x₀ ε := rfl

/-- The contract's `η_ε` is the implementation's rescaled temporal cutoff. -/
theorem scaledTemporalCutoff_eq :
    Contracts.V1.scaledTemporalCutoff η T ε = temporalCutoff η T ε := rfl

/-- The contract's dilation is the upstream one. -/
theorem dilateField_eq (α : ℝ) :
    Contracts.V1.dilateField α c d t₀ x₀ u = NSFormalization.Source.dilateField α c d t₀ x₀ u :=
  rfl

/-- The contract's parabolic velocity rescaling is the upstream one. -/
theorem parabolicVelocity_eq :
    Contracts.V1.parabolicVelocity k t₀ x₀ u = NSFormalization.Source.parabolicVelocity k t₀ x₀ u :=
  rfl

/-- The contract's `U_ε` is the implementation's parabolic rescaling of the
past-zero extension of the packet velocity. -/
theorem scaledPacket_eq :
    Contracts.V1.scaledPacket u x₀ T ε =
      NSFormalization.Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField u) := rfl

/-- The contract's `U_ε` really is the third summand of the implementation's
insertion family `NSFormalization.Source.InsertionFamily.velocity`
(`formalization/NSFormalization/Source/InsertionFamily.lean:32-35`), which is
what the `scaledPacket` docstring claims.  `scaledPacket_eq` alone cannot see
that: it only restates the contract's own right-hand side.  This theorem names
`InsertionFamily.velocity` and so stops compiling the moment the insertion
family changes shape. -/
theorem insertionFamily_velocity_eq (U W : Contracts.V1.VelocityField)
    (z : Contracts.V1.SpaceTime) :
    NSFormalization.Source.InsertionFamily.velocity U W x₀ T θ η ε z =
      W z + physicalCorrection W x₀ T θ η ε z + Contracts.V1.scaledPacket U x₀ T ε z := rfl

/-- The contract's `E_T` gradient vector is the one the transport lemmas use. -/
theorem spatialGradient_eq (z : Contracts.V1.VelocityField) :
    Contracts.V1.Data.spatialGradient z t x = NSFormalization.Section4.I02.spatialGradient z t x :=
  rfl

/-- The contract's packet-force exponent, shifted by the one power the
correction force gains, is the exponent the implementation's mixed bound
carries.  This is the drift guard for `Contracts.V1.alpha`, the one re-defined
notion with no single upstream counterpart. -/
theorem alpha_add_one (p q : ℝ≥0∞) :
    Contracts.V1.alpha p q + 1 = -2 + 3 / p.toReal + 2 / q.toReal := by
  simp only [Contracts.V1.alpha]; ring

/-- The canonical Section 4 energy norm, spelled out as the two quantities the
transport lemmas of `NSFormalization.Section4.I02.Energy` bound.  Stating this
`rfl` once keeps the assembly from re-checking the unfolding. -/
theorem energyENorm_eq (T : ℝ) (z : Contracts.V1.VelocityField) :
    Contracts.V1.Data.energyENorm T z =
      essSup (fun s => eLpNorm (fun y : Contracts.V1.Space => z (s, y)) 2 volume)
          (volume.restrict (Set.Ioo (0 : ℝ) T)) +
        (∫⁻ s in Set.Ioo (0 : ℝ) T,
            (eLpNorm (fun y : Contracts.V1.Space =>
              NSFormalization.Section4.I02.spatialGradient z s y) 2 volume) ^ (2 : ℝ)) ^
          ((2 : ℝ)⁻¹) := rfl

/-- The canonical Section 4 mixed Lebesgue norm is at most the time norm of any
admissible Bochner slice path, because it is defined as an infimum over them. -/
theorem mixedLebesgueENorm_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] (F : Contracts.V1.VelocityField)
    (G : ℝ → MeasureTheory.Lp Contracts.V1.Space p (volume : Measure Contracts.V1.Space))
    (hslice : ∀ t : ℝ,
      (G t : Contracts.V1.Space → Contracts.V1.Space) =ᵐ[volume] fun x => F (t, x))
    (hmeas : AEStronglyMeasurable G NSFormalization.Paper3.positiveTimeMeasure) :
    Contracts.V1.Data.mixedLebesgueENorm q p F ≤
      eLpNorm G q NSFormalization.Paper3.positiveTimeMeasure :=
  iInf_le (fun Gs : {H : ℝ → MeasureTheory.Lp Contracts.V1.Space p
        (volume : Measure Contracts.V1.Space) //
      Contracts.V1.Data.IsLebesgueSlicePath p F H ∧
        AEStronglyMeasurable H Contracts.V1.Data.forceTimeMeasure} =>
    eLpNorm Gs.1 q Contracts.V1.Data.forceTimeMeasure) ⟨G, fun t _ => hslice t, hmeas⟩

end Correspondence

set_option maxHeartbeats 2000000 in
/-- Bind the local vector potential, the solenoidal correction and the
correction force of Lemmas 3.4 and 3.5 to the stable version-one contract.

The reference is only assumed smooth on the open slab `(0,T+δ) × R³`, while the
whole `Paper1`/`Source` chain assumes global smoothness.  The bridge is the
globally smooth window extension `V` of `NSFormalization.Paper1.TimeExtension`
together with the slicewise congruence lemmas of
`NSFormalization.Section4.I02.Reference`: the correction and its force are
defined from the *given* `v`, and every estimate is transported from `V` through
the function equalities `hcorr` and `hforce`, which hold because both sides
vanish off the cutoff window. -/
def correction {ν : ℝ} (P : Contracts.V1.PacketAPI ν) {T δ r : ℝ}
    {v : Contracts.V1.VelocityField} {π : Contracts.V1.PressureField}
    {g : Contracts.V1.VelocityField} (x₀ : Contracts.V1.Space)
    (hT : 0 < T) (hδ : 0 < δ) (hr : 0 < r)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Contracts.V1.Space)))
    (hπ : ContDiffOn ℝ ∞ π (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Contracts.V1.Space)))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Contracts.V1.Space,
      Contracts.V1.spatialDivergence v t x = 0)
    (heq : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Contracts.V1.Space,
      Contracts.V1.navierStokesResidual ν v π t x = g (t, x)) :
    Contracts.V1.CorrectionAPI ν P := by
  classical
  -- ### The window extension of the reference
  have hmin : 0 < min T δ := lt_min hT hδ
  set δ₁ : ℝ := min T δ / 4 with hδ₁def
  have hδ₁ : 0 < δ₁ := by rw [hδ₁def]; linarith
  have hminT : min T δ ≤ T := min_le_left _ _
  have hminδ : min T δ ≤ δ := min_le_right _ _
  have hslabt : Ioo (T - 2 * δ₁) (T + 2 * δ₁) ⊆ Ioo (0 : ℝ) (T + δ) := by
    intro s hs
    rw [hδ₁def] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hslab : Ioo (T - 2 * δ₁) (T + 2 * δ₁) ×ˢ (univ : Set Contracts.V1.Space) ⊆
      Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Contracts.V1.Space) :=
    Set.prod_mono_left hslabt
  choose V hVs hVdiv hVeq _hVzero using
    exists_global_reference_extension T δ₁ hδ₁ (hv.mono hslab)
      (fun s hs x => hdiv s (hslabt hs) x)
  have hVslice : ∀ s : ℝ, |s - T| ≤ δ₁ → ∀ y : Contracts.V1.Space, V (s, y) = v (s, y) := by
    intro s hs y
    rw [abs_le] at hs
    exact hVeq ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, mem_univ y⟩
  -- ### The cutoffs and the scale threshold
  choose Rb hRb hRle using P.carrier_compact.isBounded.exists_pos_norm_le
  set R : ℝ := Rb + 1 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hKR : P.carrier ⊆ Metric.ball (0 : Contracts.V1.Space) R := by
    intro y hy
    have hyb := hRle y hy
    rw [Metric.mem_ball, dist_zero_right, hRdef]
    linarith
  choose θ O hθ hθc hθR hO hKO hθone using
    exists_spatial_cutoff P.carrier_compact hR hKR
  choose η hη hηc hηone0 hηI0 using exists_temporal_cutoff (0 : ℝ) 1 one_pos
  have hηone : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1) := by simpa using hηone0
  have hηI : tsupport η ⊆ Ioo (-2 : ℝ) 2 := by simpa using hηI0
  set ε₀ : ℝ := min 1 (min (r / (R + 1)) (Real.sqrt (δ₁ / 2))) with hε₀def
  have hε₀ : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min one_pos (lt_min (div_pos hr (by linarith))
      (Real.sqrt_pos.mpr (by linarith)))
  have hεle1 : ε₀ ≤ 1 := by rw [hε₀def]; exact min_le_left _ _
  have hspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * R < r := by
    intro ε hε
    have h1 : ε ≤ r / (R + 1) := by
      refine hε.2.trans ?_
      rw [hε₀def]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have h2 : ε * R ≤ (r / (R + 1)) * R :=
      mul_le_mul_of_nonneg_right h1 hR.le
    have h3 : (r / (R + 1)) * R < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hwindow : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 ≤ δ₁ := by
    intro ε hε
    have h1 : ε ≤ Real.sqrt (δ₁ / 2) := by
      refine hε.2.trans ?_
      rw [hε₀def]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have h2 : ε ^ 2 ≤ δ₁ / 2 := by
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ δ₁ / 2 by linarith)
      nlinarith [hε.1.le, Real.sqrt_nonneg (δ₁ / 2)]
    linarith
  have htime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ := by
    intro ε hε
    have h := hwindow ε hε
    rw [hδ₁def] at h
    linarith
  have hεIoc : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε ∈ Ioc (0 : ℝ) 1 :=
    fun ε hε => ⟨hε.1, hε.2.trans hεle1⟩
  -- ### The correction and its force are built from the *given* reference
  have hsupp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      tsupport (physicalCorrection v x₀ T θ η ε) ⊆
        Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * R) :=
    fun ε hε => physical_support hε.1 v x₀ T hθc hηc hθR hηI
  have hcut0 : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ s : ℝ, δ₁ < |s - T| → temporalCutoff η T ε s = 0 := by
    intro ε hε s hs
    show η ((ε ^ 2)⁻¹ * (s - T)) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε.1 2
    have hI := hηI hmem
    have hb1 : s - T < 2 * ε ^ 2 := by
      have h := mul_lt_mul_of_pos_left hI.2 hε2
      rw [← mul_assoc, mul_inv_cancel₀ hε2.ne', one_mul] at h
      linarith
    have hb2 : -(2 * ε ^ 2) < s - T := by
      have h := mul_lt_mul_of_pos_left hI.1 hε2
      rw [← mul_assoc, mul_inv_cancel₀ hε2.ne', one_mul] at h
      linarith
    have habs : |s - T| < 2 * ε ^ 2 := abs_lt.mpr ⟨hb2, hb1⟩
    linarith [hwindow ε hε]
  have hcorr : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      physicalCorrection v x₀ T θ η ε = physicalCorrection V x₀ T θ η ε := by
    intro ε hε
    funext z
    obtain ⟨s, y⟩ := z
    by_cases hz : |s - T| ≤ δ₁
    · exact physicalCorrection_congr_slice v V x₀ T θ η ε (s, y)
        (fun w => (hVslice s hz w).symm)
    · rw [not_le] at hz
      rw [physicalCorrection, physicalCorrection,
        localCorrection_zero_of_time v x₀ _ _ s y (hcut0 ε hε s hz),
        localCorrection_zero_of_time V x₀ _ _ s y (hcut0 ε hε s hz)]
  have hforce : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      correctionForce ν v (physicalCorrection v x₀ T θ η ε) =
        correctionForce ν V (physicalCorrection V x₀ T θ η ε) := by
    intro ε hε
    rw [hcorr ε hε]
    funext z
    by_cases hz : |z.1 - T| ≤ δ₁
    · exact correctionForce_congr_slice ν v V _ z (fun w => (hVslice z.1 hz w).symm)
    · rw [not_le] at hz
      have hout : z ∉ tsupport (physicalCorrection V x₀ T θ η ε) := by
        intro hmem
        rw [← hcorr ε hε] at hmem
        obtain ⟨ha, hb⟩ := (hsupp ε hε hmem).1
        have : |z.1 - T| < 2 * ε ^ 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
        linarith [hwindow ε hε]
      rw [LocalizedInsertion.correctionForce_eq_zero_outside ν v _ hout,
        LocalizedInsertion.correctionForce_eq_zero_outside ν V _ hout]
  have hsmooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (physicalCorrection v x₀ T θ η ε) := by
    intro ε hε
    rw [hcorr ε hε]
    exact physical_smooth hVs x₀ T ε hθ hη
  have hcompact : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      HasCompactSupport (physicalCorrection v x₀ T θ η ε) :=
    fun ε hε => physical_compact hε.1.ne' v x₀ T hθc hηc
  have hFsmooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      ContDiff ℝ ∞ (correctionForce ν v (physicalCorrection v x₀ T θ η ε)) := by
    intro ε hε
    rw [hforce ε hε]
    exact CorrectionForceNorms.physicalForce_smooth ν hVs x₀ T ε hθ hη
  have hFcompact : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      HasCompactSupport (correctionForce ν v (physicalCorrection v x₀ T θ η ε)) :=
    fun ε hε => LocalizedInsertion.correctionForce_compact ν v (hcompact ε hε)
  have hFsupp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      tsupport (correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ⊆
        Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * R) :=
    fun ε hε => (LocalizedInsertion.correctionForce_support ν v _).trans (hsupp ε hε)
  -- ### The uniform constants
  choose Cw hCw hCwb using fun j m : ℕ =>
    physical_mixed_derivative_bound hVs x₀ T hθ hη hθc hηc j m
  choose Cf hCf hCfb using fun m : ℕ =>
    CorrectionForceProfile.physicalForce_spatial_derivative_bound ν hVs x₀ T hθ hη hθc hηc m
  choose Cm hCmlt hCmb using fun p q : ℝ≥0∞ =>
    CorrectionMixedNorms.physical_force_mixed_bound ν hVs x₀ T hθ hη hθc hηc p q
  choose Ae hAe hAeb using
    CorrectionEnergy.physicalCorrection_uniform_energy hVs x₀ T hθ hη hθc hηc
  choose De hDe hDeb using
    InsertionEnergy.correction_gradientSquare_bound hVs x₀ T hθ hη hθc hηc
  have hballtop : volume (Metric.ball (0 : Contracts.V1.Space) 1) ≠ ⊤ :=
    (measure_ball_lt_top).ne
  refine
    { T := T, time_pos := hT, δ := δ, margin_pos := hδ
      v := v, π := π, g := g
      reference_smooth := hv, reference_pressure_smooth := hπ
      reference_divergence_free := hdiv, reference_equation := heq
      x₀ := x₀, r := r, radius_pos := hr
      θ := θ, theta_smooth := hθ, theta_compactSupport := hθc
      plateau := O, plateau_open := hO, carrier_subset_plateau := hKO, theta_one := hθone
      θRadius := R, theta_radius_pos := hR, theta_support := hθR
      η := η, eta_smooth := hη, eta_compactSupport := hηc
      eta_one := hηone, eta_support := hηI
      ε₀ := ε₀, eps_pos := hε₀, eps_le_one := hεle1
      eps_time := htime, eps_space := hspace
      potential := RadialPotential.timePotential v x₀
      potential_smooth := timePotential_contDiffOn isOpen_Ioo hv x₀
      potential_formula := fun _ _ => rfl
      potential_curl := fun t ht x => spatialCurl_timePotential_on hv hdiv x₀ ht x
      correction := fun ε => physicalCorrection v x₀ T θ η ε
      correction_formula := fun _ _ => rfl
      correction_smooth := hsmooth
      correction_divergence_free := ?_
      correction_compactSupport := hcompact
      correction_support := hsupp
      correction_support_ball := ?_
      correction_vanishes_before := ?_
      correction_cancels := ?_
      correction_cancels_germ := ?_
      correctionDerivConst := Cw
      correctionDerivConst_nonneg := hCw
      correction_derivative_bound := ?_
      forceCorrection := fun ε => correctionForce ν v (physicalCorrection v x₀ T θ η ε)
      force_formula := fun _ _ _ => rfl
      force_smooth := hFsmooth
      force_compactSupport := hFcompact
      force_support := hFsupp
      force_positive_time := ?_
      force_support_ball := ?_
      spatialVolumeConst := R ^ 3 * (volume (Metric.ball (0 : Contracts.V1.Space) 1)).toReal
      force_spatial_volume := ?_
      force_time_length := ?_
      forceDerivConst := Cf
      forceDerivConst_nonneg := hCf
      force_derivative_bound := ?_
      energyConst := Real.sqrt Ae + Real.sqrt De
      correction_slice_memLp := ?_
      correction_gradient_memLp := ?_
      correction_energy_bound := ?_
      mixedConst := fun p q => (Cm p q).toReal
      force_spatial_memLp := ?_
      force_mixed_bound := ?_
      corrected_background := ?_
      perturbation_divergence_free := ?_ }
  -- `correction_divergence_free`
  · intro ε hε t x
    rw [hcorr ε hε]
    exact physical_divergence hVs x₀ T ε η hθ t x
  -- `correction_support_ball`
  · intro ε hε t
    refine (LocalizedInsertion.slice_support_projection (hcompact ε hε) t).trans ?_
    rintro x ⟨z, hz, rfl⟩
    exact Metric.ball_subset_ball (hspace ε hε).le (hsupp ε hε hz).2
  -- `correction_vanishes_before`
  · intro ε hε t ht x
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact absurd (hsupp ε hε hmem).1.1 (not_lt.mpr ht)
  -- `correction_cancels`, `eq:bgzero` in its open-neighbourhood form
  · intro ε hε t ht
    have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε.1
    have hkk : ((ε⁻¹ : ℝ) ^ 2)⁻¹ = ε ^ 2 := inv_sq_inv ε
    by_cases hb : t ≤ T - ε ^ 2
    · refine ⟨∅, isOpen_empty, ?_, by simp⟩
      exact (scaledPacket_slice_empty (k := ε⁻¹) P.velocity x₀ hb).le
    · rw [not_le] at hb
      refine ⟨spaceMap ε x₀ '' O, isOpen_spaceMap_image hε.1.ne' x₀ hO, ?_, ?_⟩
      · refine (delayed_full_support P.carrier_compact hk x₀ P.velocity_support
          (t₀ := T - ε ^ 2) t ⟨ht.1.le, by rw [hkk]; linarith [ht.2]⟩).trans ?_
        rw [scaledSupport_eq_spaceMap]
        exact Set.image_mono hKO
      · intro x hx
        have hIcc : t ∈ Icc (T - ε ^ 2) (T + ε ^ 2) :=
          ⟨hb.le, by linarith [ht.2, sq_nonneg ε]⟩
        have habs : |t - T| ≤ δ₁ := by
          rw [abs_le]
          exact ⟨by linarith [hIcc.1, hwindow ε hε, sq_nonneg ε],
            by linarith [hIcc.2, hwindow ε hε, sq_nonneg ε]⟩
        have h0 := (physical_removes hVs hVdiv x₀ T hε.1 θ η hO hθone hηone t hIcc x hx).self_of_nhds
        rw [congrFun (hcorr ε hε) (t, x), ← hVslice t habs x]
        exact h0
  -- `correction_cancels_germ`
  · intro ε hε t ht x hx
    have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε.1
    have hkk : ((ε⁻¹ : ℝ) ^ 2)⁻¹ = ε ^ 2 := inv_sq_inv ε
    have hremove : ∀ s ∈ Icc (T - ((ε⁻¹ : ℝ) ^ 2)⁻¹) (T + ((ε⁻¹ : ℝ) ^ 2)⁻¹),
        ∀ y ∈ spaceMap ε x₀ '' O,
        ∀ᶠ z in 𝓝 y, v (s, z) + physicalCorrection v x₀ T θ η ε (s, z) = 0 := by
      rw [hkk]
      intro s hs y hy
      have habs : |s - T| ≤ δ₁ := by
        rw [abs_le]
        exact ⟨by linarith [hs.1, hwindow ε hε, sq_nonneg ε],
          by linarith [hs.2, hwindow ε hε, sq_nonneg ε]⟩
      filter_upwards [physical_removes hVs hVdiv x₀ T hε.1 θ η hO hθone hηone s hs y hy]
        with z hz
      rw [congrFun (hcorr ε hε) (s, z), ← hVslice s habs z]
      exact hz
    have hKO' : scaledSupport ε⁻¹ x₀ P.carrier ⊆ spaceMap ε x₀ '' O := by
      rw [scaledSupport_eq_spaceMap]
      exact Set.image_mono hKO
    have hmain := LocalizedInsertion.background_removed_on_packet hk x₀ P.velocity_support
      P.carrier_compact hKO' hremove
    rw [hkk] at hmain
    exact hmain t ht x hx
  -- `correction_derivative_bound`
  · intro j m ε hε z u hu
    rw [hcorr ε hε]
    exact hCwb j m ε (hεIoc ε hε) z u hu
  -- `force_positive_time`
  · intro ε hε z hz
    have h1 := (hFsupp ε hε hz).1.1
    have h2 : 2 * ε ^ 2 < T := lt_of_lt_of_le (htime ε hε) hminT
    linarith
  -- `force_support_ball`
  · intro ε hε z hz
    exact Metric.ball_subset_ball (hspace ε hε).le (hFsupp ε hε hz).2
  -- `force_spatial_volume`
  · intro ε hε
    have hcube : (0 : ℝ) ≤ (ε * R) ^ 3 := pow_nonneg (mul_nonneg hε.1.le hR.le) 3
    refine (spatial_support_volume (hFsupp ε hε) (mul_nonneg hε.1.le hR.le)).trans ?_
    have hEq : ENNReal.ofReal ((ε * R) ^ 3) * volume (Metric.ball (0 : Contracts.V1.Space) 1)
        = ENNReal.ofReal ((ε * R) ^ 3 *
            (volume (Metric.ball (0 : Contracts.V1.Space) 1)).toReal) := by
      rw [ENNReal.ofReal_mul hcube, ENNReal.ofReal_toReal hballtop]
    rw [hEq]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  -- `force_time_length`
  · intro ε hε
    refine (temporal_support_length (hFsupp ε hε)).trans ?_
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- `force_derivative_bound`
  · intro m ε hε z u hu
    rw [hforce ε hε]
    exact hCfb m ε (hεIoc ε hε) z u hu
  -- `correction_slice_memLp`
  · intro ε hε t
    exact slice_memLp (hsmooth ε hε).continuous (hcompact ε hε) 2 t
  -- `correction_gradient_memLp`
  · intro ε hε t
    exact spatialGradient_memLp (hsmooth ε hε) (hcompact ε hε) 2 t
  -- `correction_energy_bound`, `eq:wE`
  · intro ε hε
    rw [energyENorm_eq]
    have h1 := energyEssSup_le (T := T) (A := Ae * ε ^ 3) (hsmooth ε hε) (hcompact ε hε)
      (fun t => by rw [hcorr ε hε]; exact hAeb ε (hεIoc ε hε) t)
    have h2 := energyGradient_le (T := T) (D := De * ε ^ 3) (hsmooth ε hε) (hcompact ε hε)
      (by rw [hcorr ε hε]; exact (hDeb ε (hεIoc ε hε)).1)
      (by rw [hcorr ε hε]; exact (hDeb ε (hεIoc ε hε)).2)
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    congr 1
    rw [sqrt_mul_cube hAe hε.1.le, sqrt_mul_cube hDe hε.1.le]
    ring
  -- `force_spatial_memLp`
  · intro p ε hε t
    exact slice_memLp (hFsmooth ε hε).continuous (hFcompact ε hε) p t
  -- `force_mixed_bound`, `eq:Hmixed`
  · intro p q _inst ε hε
    obtain ⟨G, hGslice, hGmeas, hGbound⟩ :=
      exists_slicePath (p := p) (hFsmooth ε hε).continuous (hFcompact ε hε) q
    refine (mixedLebesgueENorm_le (q := q) _ G hGslice hGmeas).trans (hGbound.trans ?_)
    rw [hforce ε hε]
    refine (hCmb p q ε (hεIoc ε hε)).trans (le_of_eq ?_)
    rw [alpha_add_one p q, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hCmlt p q).ne, mul_comm]
  -- `corrected_background`
  · intro ε hε t ht x
    have hsm := hsmooth ε hε
    have hopen : Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Contracts.V1.Space) ∈ 𝓝 ((t, x) : SpaceTime) :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩
    have hvt : DifferentiableAt ℝ (fun s : ℝ => v (s, x)) t :=
      (((hv.contDiffAt hopen).comp t
        (contDiffAt_id.prodMk contDiffAt_const))).differentiableAt (by simp)
    have hwt : DifferentiableAt ℝ (fun s : ℝ => physicalCorrection v x₀ T θ η ε (s, x)) t :=
      ((hsm.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)) t
    have hvs : ContDiff ℝ 2 (fun y : Contracts.V1.Space => v (t, y)) :=
      (SpatialCurl.contDiff_spatialSlice hv ht).of_le (by simp)
    have hws : ContDiff ℝ 2
        (fun y : Contracts.V1.Space => physicalCorrection v x₀ T θ η ε (t, y)) :=
      (hsm.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
    have hπs : ContDiff ℝ ∞ (fun y : Contracts.V1.Space => π (t, y)) :=
      hπ.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun y => ⟨ht, mem_univ y⟩)
    have hps : DifferentiableAt ℝ (fun y : Contracts.V1.Space => π (t, y)) x :=
      (hπs.differentiable (by simp)) x
    have heq' : NSFormalization.Source.residual ν v π t x = g (t, x) := heq t ht x
    show NSFormalization.Source.residual ν
        (fun z => v z + physicalCorrection v x₀ T θ η ε z) π t x =
      g (t, x) + correctionForce ν v (physicalCorrection v x₀ T θ η ε) (t, x)
    rw [NSFormalization.Source.corrected_background ν v _ π t x hvt hwt hvs hws hps, heq']
  -- `perturbation_divergence_free`
  · intro ε hε t ht x
    have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε.1
    have hkk : ((ε⁻¹ : ℝ) ^ 2)⁻¹ = ε ^ 2 := inv_sq_inv ε
    have hTend : T - ε ^ 2 + ((ε⁻¹ : ℝ) ^ 2)⁻¹ = T := by rw [hkk]; ring
    have hUs : ContDiffOn ℝ ∞
        (NSFormalization.Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField P.velocity))
        (Ico (0 : ℝ) T ×ˢ (univ : Set Contracts.V1.Space)) := by
      have h := dilate_smoothOn (f := zeroPastField P.velocity) ε⁻¹ hk (T - ε ^ 2) x₀
        P.velocity_extension_smooth
      rw [hTend] at h
      exact h.mono (Set.prod_mono_left Ico_subset_Iio_self)
    have hUdiv : ∀ s ∈ Ico (0 : ℝ) T, ∀ y : Contracts.V1.Space, spatialDivergence
        (NSFormalization.Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀
          (zeroPastField P.velocity)) s y = 0 := by
      intro s hs y
      refine delayed_parabolic_divergence hk (T - ε ^ 2) x₀
        (fun σ hσ z => P.divergence_free σ ⟨hσ.1.le, hσ.2⟩ z) (t := s) ?_ y
      rw [hkk]; linarith [hs.2]
    have hwdiv : ∀ s : ℝ, ∀ y : Contracts.V1.Space,
        spatialDivergence (physicalCorrection v x₀ T θ η ε) s y = 0 := by
      intro s y
      rw [hcorr ε hε]
      exact physical_divergence hVs x₀ T ε η hθ s y
    have hmain := LocalizedInsertion.inserted_divergence
      (v := fun _ : SpaceTime => (0 : Contracts.V1.Space)) contDiff_const (hsmooth ε hε) hUs
      (fun s y => by simp [spatialDivergence, spatialDerivative]) hwdiv hUdiv
    show NavierStokes.ProblemStatement.spatialDivergence
        (fun z : SpaceTime => physicalCorrection v x₀ T θ η ε z +
          NSFormalization.Source.parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀
            (zeroPastField P.velocity) z) t x = 0
    simpa only [zero_add] using hmain t ht x

end BlowupDensity.Bindings
