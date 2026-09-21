import Contracts.V2.Correction
import Bindings.Correction
import NSFormalization.Section4.I02.Prescribed
import NSFormalization.Section4.I02.Reference
import NSFormalization.Section4.I02.Support
import NSFormalization.Section4.I02.Energy
import NSFormalization.Section4.I02.Mixed
import NSFormalization.Paper1.InsertionEnergy
import NSFormalization.Paper1.CorrectionEnergy
import NSFormalization.Paper1.CorrectionVectorNorms
import NSFormalization.Source.PhysicalRemoval
import NSFormalization.Source.InsertionFamily

/-! The implementation layer for the version-two correction contract, and the
compatibility bridge back to version one.

`Contracts.V2.CorrectionAPI ν P K` extends `Contracts.V1.CorrectionAPI ν P` by
the single field `prescribed_subset_plateau : K ⊆ plateau`
(`paper/sections/03-torus.tex:101-102`), so this file has three jobs.

* `correctionV2` inhabits the version-two record.  It is the argument of
  `Bindings.correction` with **one** step changed: the Urysohn cutoff is built
  around `P.carrier ∪ K` instead of around `P.carrier`, through the new
  `NSFormalization.Section4.I02.exists_prescribed_cutoff`, which also produces
  the enclosing radius `R_*`.  Nothing else in the argument sees `K`: the
  radius `R_*`, the threshold `ε₀ = min 1 (min (r/(R_*+1)) √(δ₁/2))`, the
  correction, the force and all their bounds are written in `R_*`, `θ`, `η`
  exactly as before, which is why the `Paper1`/`Source` chain is reused
  unchanged.  The duplication of the version-one argument is deliberate:
  `verification/Bindings/Correction.lean` is the frozen witness of the
  registered version-one contract and is not edited by this lane.  The copy is
  exact: `diff -u` of the two *files* is seven hunks, and only **three** of them
  fall inside the shared proof body -- the signature and target type, the cutoff
  block, and the record literal gaining one field.  The other four are the
  imports, this docstring, the deletion of the `Correspondence` section (which
  is imported from `Bindings.Correction`, not recopied), and the five new
  trailing declarations.  At `--unified=0` the proof-body count is five, the
  signature region splitting into three; the mathematical delta is one `choose`
  against `exists_prescribed_cutoff` either way.
* `correctionV1_of_v2` and `correctionStatement_of_v2` record that version one
  is recoverable from version two.  The first is the inherited projection
  `toCorrectionAPI`, so the recovery is definitional, not a re-proof; the second
  instantiates `K := P.carrier` (any compact set would do) and is what makes
  "V2 is strictly stronger than V1" a checked statement rather than a comment.
  `Tests.checkedCorrection` keeps using `Bindings.correction` and is untouched.
* `prescribed_subset_ball` is the three-line consequence every consumer wants:
  the prescribed set sits inside `ball 0 θRadius`, so the inherited
  `eps_space : ε * θRadius < r` alone puts `x₀ + ε K` inside `B`
  (`03-torus.tex:104-105`).  Stating it here keeps the contract itself
  assertion-free.

The `rfl` bridges that guard the contract's re-defined notions against upstream
drift live in `Bindings.Correction` and are imported, not repeated: version two
reuses version one's `curl`, `scaledPacket`, `alpha`, ... verbatim, so version
one's bridges guard version two as well.
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

/-- Bind the local vector potential, the solenoidal correction and the
correction force of Lemmas 3.4 and 3.5 to the stable version-two contract, with
the cutoff plateau covering the caller's prescribed compact set `K`.

The reference is only assumed smooth on the open slab `(0,T+δ) × R³`, while the
whole `Paper1`/`Source` chain assumes global smoothness.  The bridge is the
globally smooth window extension `V` of `NSFormalization.Paper1.TimeExtension`
together with the slicewise congruence lemmas of
`NSFormalization.Section4.I02.Reference`: the correction and its force are
defined from the *given* `v`, and every estimate is transported from `V` through
the function equalities `hcorr` and `hforce`, which hold because both sides
vanish off the cutoff window.

`K` enters at exactly one place, marked in the proof: the cutoff is built around
`P.carrier ∪ K`, which is compact because both summands are
(`03-torus.tex:101`, "choose a compact set `K_*`").  Every later step is the
version-one step, so `hK` costs the caller one compactness proof and buys the
whole `K_*` clause. -/
def correctionV2 {ν : ℝ} (P : Contracts.V1.PacketAPI ν)
    {K : Set Contracts.V1.Space} {T δ r : ℝ}
    {v : Contracts.V1.VelocityField} {π : Contracts.V1.PressureField}
    {g : Contracts.V1.VelocityField} (x₀ : Contracts.V1.Space)
    (hK : IsCompact K) (hT : 0 < T) (hδ : 0 < δ) (hr : 0 < r)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Contracts.V1.Space)))
    (hπ : ContDiffOn ℝ ∞ π (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Contracts.V1.Space)))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Contracts.V1.Space,
      Contracts.V1.spatialDivergence v t x = 0)
    (heq : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Contracts.V1.Space,
      Contracts.V1.navierStokesResidual ν v π t x = g (t, x)) :
    Contracts.V2.CorrectionAPI ν P K := by
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
  -- The whole version-two delta is here.  `Bindings.correction` builds the
  -- plateau around `P.carrier` alone and derives `R = Rb + 1` from it; this
  -- builds one cutoff whose plateau covers `P.carrier ∪ K`, so the very same
  -- `R` dominates the prescribed set.  `exists_prescribed_cutoff` produces the
  -- radius, so no `hKR`/`hRdef` bookkeeping survives.
  choose R θ O hR hθ hθc hθR hO hKO hKplateau hθone using
    exists_prescribed_cutoff P.carrier_compact hK
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
      plateau := O, plateau_open := hO, carrier_subset_plateau := hKO
      prescribed_subset_plateau := hKplateau, theta_one := hθone
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

/-- Version one is recoverable from version two by the inherited projection: a
version-two record *is* a version-one record together with one extra clause.
This is the compatibility binding `CONTRIBUTING.md` asks for when a
specification changes -- and it is definitional, so it cannot drift.

`Tests.checkedCorrection` does not go through this function: the registered
version-one test keeps using the untouched `Bindings.correction`.  What this
declaration rules out is a version two that quietly drops or weakens a
version-one field, which would make the projection fail to typecheck. -/
def correctionV1_of_v2 {ν : ℝ} {P : Contracts.V1.PacketAPI ν}
    {K : Set Contracts.V1.Space} (A : Contracts.V2.CorrectionAPI ν P K) :
    Contracts.V1.CorrectionAPI ν P :=
  A.toCorrectionAPI

/-- The prescribed compact set lies inside the cutoff radius.

`prescribed_subset_plateau` states the manuscript's plateau form
(`03-torus.tex:101-102, 181`); this is the ball form that the smallness clause
`eps_space : ε * θRadius < r` consumes.  Together they give
`x₀ + ε K ⊆ ball x₀ r = B` for every `ε ∈ (0, ε₀]`, which is
`03-torus.tex:104-105` for `K_*` rather than for the packet carrier alone.

The derivation is the one `Bindings.Scaling.carrier_subset_ball` runs for
`P.carrier`: on the plateau `θ = 1 ≠ 0`, so the plateau is inside `tsupport θ`,
which `theta_support` puts inside `ball 0 θRadius`. -/
theorem prescribed_subset_ball {ν : ℝ} {P : Contracts.V1.PacketAPI ν}
    {K : Set Contracts.V1.Space} (A : Contracts.V2.CorrectionAPI ν P K) :
    K ⊆ Metric.ball (0 : Contracts.V1.Space) A.θRadius := by
  intro x hx
  refine A.theta_support (subset_tsupport _ ?_)
  rw [Function.mem_support, A.theta_one (A.prescribed_subset_plateau hx)]
  exact one_ne_zero

/-- The version-two statement implies the version-one statement.

Take `K := P.carrier`, which is compact by `PacketAPI.carrier_compact`, and
forget the extra clause.  So version two is strictly stronger: it is the
version-one contract plus the `K_*` enlargement of `03-torus.tex:101-102`, and
registering it cannot lose anything that `I02.correction` version one already
guarantees. -/
theorem correctionStatement_of_v2 (h : Contracts.V2.correctionStatement) :
    Contracts.V1.correctionStatement := by
  intro ν P T δ r v π g x₀ hT hδ hr hv hπ hdiv heq
  obtain ⟨A, hT', hδ', hv', hπ', hg', hx', hr'⟩ :=
    h ν P P.carrier T δ r v π g x₀ P.carrier_compact hT hδ hr hv hπ hdiv heq
  exact ⟨correctionV1_of_v2 A, hT', hδ', hv', hπ', hg', hx', hr'⟩

/-- The manuscript's `K_*` is compact.

`paper/sections/03-torus.tex:101-102`: "choose a compact set `K_*` containing
`K` and the spatial projection of `supp F`".  The canonical such choice is the
union itself, and it is compact because `PacketAPI.force_support` carries
`HasCompactSupport P.force` and `Prod.snd` is continuous.  This is the datum
`correctionV2` asks for, so the manuscript's own enlargement is always an
admissible argument.  `Source/InsertionFamily.lean:218-221` forms the same set
inline. -/
theorem isCompact_carrierStar {ν : ℝ} (P : Contracts.V1.PacketAPI ν) :
    IsCompact (P.carrier ∪ Prod.snd '' tsupport P.force) :=
  P.carrier_compact.union (P.force_support.1.isCompact.image continuous_snd)

/-- The premise that no consumer of version one could discharge.

`research/I03/REVIEW_CONTRACT.md` 5.1 item 4 dropped `force_carrier_subset` from
`ScalingAPI` and `research/R42/ATTEMPTS.md` 3 rejected it as an
`InsertionFamilyAPI` field, both for the same reason: with `θRadius` fixed from
`P.carrier` alone, `∀ z ∈ tsupport P.force, z.2 ∈ ball 0 θRadius` is true of the
concrete construction but unprovable from the registered interface.  Taking the
manuscript's own `K_*` as the prescribed set makes it a one-line consequence of
`prescribed_subset_plateau`.

With this, `eps_space : ε * θRadius < r` places the rescaled packet force `F_ε`
inside `B` on the *whole* version-two range, so a consumer no longer has to
shrink its threshold to `min S.ε₀ (r / (R_F + 1))`. -/
theorem force_carrier_subset_ball {ν : ℝ} {P : Contracts.V1.PacketAPI ν}
    (A : Contracts.V2.CorrectionAPI ν P (P.carrier ∪ Prod.snd '' tsupport P.force))
    {z : Contracts.V1.SpaceTime} (hz : z ∈ tsupport P.force) :
    z.2 ∈ Metric.ball (0 : Contracts.V1.Space) A.θRadius :=
  prescribed_subset_ball A (Or.inr ⟨z, hz, rfl⟩)

end BlowupDensity.Bindings
