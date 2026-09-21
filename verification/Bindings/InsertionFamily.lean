import Contracts.V1.InsertionFamily
import Bindings.Scaling
import NSFormalization.Section4.R42.Assembly

/-! The only layer that knows the current implementation's names and paths for
the inserted family of Theorem 4.2.

`Contracts.V1.InsertionFamily` copies no notion of its own -- every object it
mentions already lives in `Contracts.V1.{Data, Packet, Correction, Scaling}` and
is bridged by `Bindings/Correction.lean` and `Bindings/Scaling.lean` -- so this
adapter carries no new `rfl` bridge.  What it does is the composition:
`04-whole-space.tex:44-55`, from the registered `I01`, `I02` and `I03` records
and a `D01` reference solution.

## The one place where the registered records are not enough

`supp F_eps subset B` (`04-whole-space.tex:38`) needs the compact enlargement
`K_*` of `03-torus.tex:101-102`, which contains the spatial projection of
`supp F` as well as the packet carrier `K`.  `CorrectionAPI.thetaRadius` is tied
to `K` alone (`carrier_subset_plateau`), and `ScalingAPI.eps_space` therefore
calibrates `eps` against `K` alone.  `R42` recovers the enlargement itself:
`forceRadius` is a radius bounding the spatial projection of `supp F`, obtained
from `PacketAPI.force_support` by compactness, and `threshold` shrinks `I03`'s
`eps0` until `eps * forceRadius < r`.  That is why `InsertionFamilyAPI.ε₀` is
below `ScalingAPI.ε₀` rather than equal to it.  See `research/R42/COMPARISON.md`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.PacketScaling
open NSFormalization.Source.LocalizedInsertion
open NSFormalization.Section4.R42
open scoped ContDiff ENNReal Topology

section Family

variable {ν : ℝ} {P : Contracts.V1.PacketAPI ν}

/-! ## 1. The force radius: the `K -> K_*` enlargement, recovered in `R42` -/

/-- A radius bounding the spatial projection of `supp F`.  `PacketAPI` states
only `CompactPositiveTimeSupport force`, so this is where the enlargement
`K -> K_*` of `paper/sections/03-torus.tex:101-102` enters the assembly. -/
def forceRadius (P : Contracts.V1.PacketAPI ν) : ℝ :=
  (exists_spatial_radius P.force_support.1).choose

theorem forceRadius_pos (P : Contracts.V1.PacketAPI ν) : 0 < forceRadius P :=
  (exists_spatial_radius P.force_support.1).choose_spec.1

theorem forceRadius_spec (P : Contracts.V1.PacketAPI ν) :
    ∀ z ∈ tsupport P.force, z.2 ∈ Metric.ball (0 : Contracts.V1.Space) (forceRadius P) :=
  (exists_spatial_radius P.force_support.1).choose_spec.2

/-! ## 2. The `R42` scale threshold -/

variable (S : Contracts.V1.ScalingAPI ν P)

/-- `I03`'s threshold, shrunk so that the rescaled packet force also fits inside
the ball: `eps * R_F < r`. -/
def threshold : ℝ := min S.ε₀ (S.correction.r / (forceRadius P + 1))

theorem threshold_pos : 0 < threshold S :=
  lt_min S.eps_pos (div_pos S.correction.radius_pos (by linarith [forceRadius_pos P]))

theorem threshold_le : threshold S ≤ S.ε₀ := min_le_left _ _

theorem mem_scaling_range {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    ε ∈ Ioc (0 : ℝ) S.ε₀ :=
  ⟨hε.1, hε.2.trans (threshold_le S)⟩

theorem mem_correction_range' {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    ε ∈ Ioc (0 : ℝ) S.correction.ε₀ :=
  ⟨hε.1, (hε.2.trans (threshold_le S)).trans S.eps_le_correction⟩

theorem force_space_bound {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    ε * forceRadius P < S.correction.r := by
  have hR : (0 : ℝ) < forceRadius P + 1 := by linarith [forceRadius_pos P]
  have hle : ε ≤ S.correction.r / (forceRadius P + 1) := hε.2.trans (min_le_right _ _)
  have h1 : ε * forceRadius P ≤ S.correction.r / (forceRadius P + 1) * forceRadius P :=
    mul_le_mul_of_nonneg_right hle (forceRadius_pos P).le
  have h2 : S.correction.r / (forceRadius P + 1) * forceRadius P < S.correction.r := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hR]
    nlinarith [S.correction.radius_pos, forceRadius_pos P]
  exact h1.trans_lt h2

/-! ## 3. Elementary consequences of the smallness clauses -/

theorem time_bound {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    2 * ε ^ 2 < min S.correction.T S.correction.δ :=
  S.eps_time ε (mem_scaling_range S hε)

theorem sq_lt_time {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    ε ^ 2 < S.correction.T := by
  have h := (time_bound S hε).trans_le (min_le_left _ _)
  nlinarith [sq_nonneg ε]

theorem delay_nonneg {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    0 ≤ S.correction.T - ε ^ 2 := by
  linarith [sq_lt_time S hε]

theorem delay_end (T ε : ℝ) : T - ε ^ 2 + (((ε⁻¹ : ℝ)) ^ 2)⁻¹ = T := by
  rw [NSFormalization.Section4.I02.inv_sq_inv]; ring

/-! ## 4. The three displays -/

/-- `u_eps = v + w_eps + U_eps`, `paper/sections/04-whole-space.tex:47`. -/
def insertedVelocity (ε : ℝ) : Contracts.V1.VelocityField := fun z =>
  S.correction.v z + S.correction.correction ε z + S.U ε z

/-- `p_eps = pi + P_eps`, `paper/sections/04-whole-space.tex:47`. -/
def insertedPressure (ε : ℝ) : Contracts.V1.PressureField := fun z =>
  S.correction.π z + S.P ε z

/-- `g_eps = g + H_eps + F_eps`, `paper/sections/04-whole-space.tex:48`. -/
def insertedForce (ε : ℝ) : Contracts.V1.VelocityField := fun z =>
  S.correction.g z + S.correction.forceCorrection ε z + S.F ε z

theorem velocityDifference_eq (ε : ℝ) :
    (fun z => insertedVelocity S ε z - S.correction.v z) =
      fun z => S.correction.correction ε z + S.U ε z := by
  funext z; simp only [insertedVelocity]; abel

theorem forceDifference_eq' (ε : ℝ) :
    (fun z => insertedForce S ε z - S.correction.g z) =
      fun z => S.correction.forceCorrection ε z + S.F ε z := by
  funext z; simp only [insertedForce]; abel

/-! ## 5. Smoothness of the rescaled fields -/

theorem scaledPacket_smoothOn {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (S.U ε)
      (Iio S.correction.T ×ˢ (univ : Set Contracts.V1.Space)) :=
  dilate_smoothOn_target (ε⁻¹) hε S.correction.T S.correction.x₀
    P.velocity_extension_smooth

theorem scaledPressure_smoothOn {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (S.P ε)
      (Iio S.correction.T ×ˢ (univ : Set Contracts.V1.Space)) :=
  dilate_smoothOn_target (((ε⁻¹ : ℝ)) ^ 2) hε S.correction.T S.correction.x₀
    P.pressure_extension_smooth

/-! ## 6. Localization of the rescaled packet velocity and pressure -/

theorem scaledPacket_slice_ball {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S.correction.T) :
    tsupport (fun x : Contracts.V1.Space => S.U ε (t, x)) ⊆
      Metric.ball S.correction.x₀ S.correction.r := by
  have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε.1
  have hs := delayed_full_support P.carrier_compact hk S.correction.x₀
    P.velocity_support (t₀ := S.correction.T - ε ^ 2) t
    (by rw [delay_end]; exact ht)
  exact hs.trans (scaledSupport_subset_ball hε.1 S.carrier_subset
    (S.eps_space ε (mem_scaling_range S hε)) S.correction.x₀)

theorem scaledPressure_slice_ball {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) S.correction.T) :
    tsupport (fun x : Contracts.V1.Space => S.P ε (t, x)) ⊆
      Metric.ball S.correction.x₀ S.correction.r := by
  have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε.1
  have hs := delayed_pressure_support P.carrier_compact hk S.correction.x₀
    P.pressure_support (t₀ := S.correction.T - ε ^ 2) t
    (by rw [delay_end]; exact ht)
  exact hs.trans (scaledSupport_subset_ball hε.1 S.carrier_subset
    (S.eps_space ε (mem_scaling_range S hε)) S.correction.x₀)

/-! ## 7. The rescaled packet force is a compact force supported in the ball -/

theorem scaledForce_positive_support {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport (S.F ε) :=
  parabolicForce_positive_support P.force_support (inv_pos.mpr hε.1)
    (delay_nonneg S hε) S.correction.x₀

theorem scaledForce_ball {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (threshold S)) :
    ∀ z ∈ tsupport (S.F ε), z.2 ∈ Metric.ball S.correction.x₀ S.correction.r :=
  parabolicForce_ball P.force_support.1 hε.1 (forceRadius_spec P)
    (force_space_bound S hε) (S.correction.T - ε ^ 2) S.correction.x₀

/-! ## 8. The inserted family -/

/-- Theorem 4.2 (`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-43`) for
the registered `I03` family and a `D01` reference solution, minus the two
lifespan clauses.  Every field is proved from the fields of `PacketAPI`,
`CorrectionAPI`, `ScalingAPI` and `Data.ClassicalSolutionR`; nothing is
reconstructed. -/
def insertionFamily {a : Contracts.V1.Data.SpatialField}
    (R : Contracts.V1.Data.ClassicalSolutionR ν a S.correction.g
      (S.correction.T + S.correction.δ))
    (hv : R.velocity = S.correction.v) (hp : R.pressure = S.correction.π) :
    Contracts.V1.InsertionFamilyAPI ν P where
  scaling := S
  a := a
  reference := R
  reference_velocity := hv
  reference_pressure := hp
  ε₀ := threshold S
  eps_pos := threshold_pos S
  eps_le_scaling := threshold_le S
  velocity := insertedVelocity S
  pressure := insertedPressure S
  force := insertedForce S
  velocity_formula := fun _ _ => rfl
  pressure_formula := fun _ _ => rfl
  force_formula := fun _ _ => rfl
  velocity_smooth := by
    intro ε hε
    have hsub : Ico (0 : ℝ) S.correction.T ×ˢ (univ : Set Contracts.V1.Space) ⊆
        Ico (0 : ℝ) (S.correction.T + S.correction.δ) ×ˢ (univ : Set Contracts.V1.Space) :=
      prod_mono (Ico_subset_Ico_right (by linarith [S.correction.margin_pos])) subset_rfl
    have hvs : ContDiffOn ℝ ∞ S.correction.v
        (Ico (0 : ℝ) S.correction.T ×ˢ (univ : Set Contracts.V1.Space)) :=
      hv ▸ R.velocity_smooth.mono hsub
    have hws : ContDiffOn ℝ ∞ (S.correction.correction ε)
        (Ico (0 : ℝ) S.correction.T ×ˢ (univ : Set Contracts.V1.Space)) :=
      (S.correction.correction_smooth ε (mem_correction_range' S hε)).contDiffOn
    have hUs : ContDiffOn ℝ ∞ (S.U ε)
        (Ico (0 : ℝ) S.correction.T ×ˢ (univ : Set Contracts.V1.Space)) :=
      (scaledPacket_smoothOn S hε.1).mono
        (prod_mono Ico_subset_Iio_self subset_rfl)
    exact (hvs.add hws).add hUs
  pressure_smooth := by
    intro ε hε
    have hsub : Ico (0 : ℝ) S.correction.T ×ˢ (univ : Set Contracts.V1.Space) ⊆
        Ico (0 : ℝ) (S.correction.T + S.correction.δ) ×ˢ (univ : Set Contracts.V1.Space) :=
      prod_mono (Ico_subset_Ico_right (by linarith [S.correction.margin_pos])) subset_rfl
    have hπs : ContDiffOn ℝ ∞ S.correction.π
        (Ico (0 : ℝ) S.correction.T ×ˢ (univ : Set Contracts.V1.Space)) :=
      hp ▸ R.pressure_smooth.mono hsub
    exact hπs.add ((scaledPressure_smoothOn S hε.1).mono
      (prod_mono Ico_subset_Iio_self subset_rfl))
  initial := by
    intro ε hε x
    have hzero : (0 : ℝ) ≤ S.correction.T - 2 * ε ^ 2 := by
      linarith [(time_bound S hε).trans_le (min_le_left S.correction.T S.correction.δ)]
    have hw : S.correction.correction ε (0, x) = 0 :=
      S.correction.correction_vanishes_before ε (mem_correction_range' S hε) 0 hzero x
    have hU : S.U ε (0, x) = 0 :=
      zeroPast_dilate_early P.velocity (ε⁻¹) (((ε⁻¹ : ℝ)) ^ 2) (ε⁻¹)
        (S.correction.T - ε ^ 2) (sq_nonneg _) S.correction.x₀
        (by linarith [sq_nonneg ε, sq_lt_time S hε]) x
    have : S.correction.v (0, x) = a x := by rw [← hv]; exact R.initial x

    simp only [insertedVelocity, hw, hU, add_zero, this]
  incompressible := by
    intro ε hε
    have hvs : ContDiffOn ℝ ∞ S.correction.v
        (Ico (0 : ℝ) (S.correction.T + S.correction.δ) ×ˢ
          (univ : Set Contracts.V1.Space)) := hv ▸ R.velocity_smooth
    have hdv : ∀ t ∈ Ico (0 : ℝ) (S.correction.T + S.correction.δ), ∀ x,
        spatialDivergence S.correction.v t x = 0 := hv ▸ R.divergence
    exact inserted_divergence_slab (Tref := S.correction.T + S.correction.δ)
      (by linarith [S.correction.margin_pos]) hvs
      (S.correction.correction_smooth ε (mem_correction_range' S hε))
      ((scaledPacket_smoothOn S hε.1).mono (prod_mono Ico_subset_Iio_self subset_rfl))
      hdv (S.correction.perturbation_divergence_free ε (mem_correction_range' S hε))
  momentum := by
    intro ε hε
    have hvs : ContDiffOn ℝ ∞ S.correction.v
        (Ico (0 : ℝ) (S.correction.T + S.correction.δ) ×ˢ
          (univ : Set Contracts.V1.Space)) := hv ▸ R.velocity_smooth
    have hps : ContDiffOn ℝ ∞ S.correction.π
        (Ico (0 : ℝ) (S.correction.T + S.correction.δ) ×ˢ
          (univ : Set Contracts.V1.Space)) := hp ▸ R.pressure_smooth
    exact inserted_equation_slab (ν := ν) (T := S.correction.T)
      (Tref := S.correction.T + S.correction.δ)
      (v := S.correction.v) (w := S.correction.correction ε) (U := S.U ε)
      (g := fun z => S.correction.g z + S.correction.forceCorrection ε z)
      (F := S.F ε) (p := S.correction.π) (P := S.P ε)
      (by linarith [S.correction.margin_pos]) hvs hps
      (S.correction.correction_smooth ε (mem_correction_range' S hε))
      ((scaledPacket_smoothOn S hε.1).mono (prod_mono Ico_subset_Iio_self subset_rfl))
      ((scaledPressure_smoothOn S hε.1).mono (prod_mono Ico_subset_Iio_self subset_rfl))
      (fun t ht x => S.correction.corrected_background ε (mem_correction_range' S hε) t
        ⟨ht.1, by linarith [ht.2, S.correction.margin_pos]⟩ x)
      (fun t ht x => S.scaledEquation ε (mem_scaling_range S hε) t ht.2 x)
      (S.correction.correction_cancels_germ ε (mem_correction_range' S hε))
  history := by
    intro ε hε t _ hle x
    have hw : S.correction.correction ε (t, x) = 0 :=
      S.correction.correction_vanishes_before ε (mem_correction_range' S hε) t hle x
    have hU : S.U ε (t, x) = 0 :=
      zeroPast_dilate_early P.velocity (ε⁻¹) (((ε⁻¹ : ℝ)) ^ 2) (ε⁻¹)
        (S.correction.T - ε ^ 2) (sq_nonneg _) S.correction.x₀
        (by nlinarith [sq_nonneg ε]) x
    simp only [insertedVelocity, hw, hU, add_zero]
  velocityDifference_support := by
    intro ε hε t ht
    have hsplit := tsupport_binop_subset (fun p q : Contracts.V1.Space => p + q) (by simp)
      (fun x : Contracts.V1.Space => S.correction.correction ε (t, x))
      (fun x : Contracts.V1.Space => S.U ε (t, x))
    have heq : (fun x : Contracts.V1.Space =>
        insertedVelocity S ε (t, x) - S.correction.v (t, x)) =
        fun x : Contracts.V1.Space =>
          S.correction.correction ε (t, x) + S.U ε (t, x) := by
      funext x; simp only [insertedVelocity]; abel
    rw [heq]
    intro x hx
    rcases hsplit hx with h | h
    · exact S.correction.correction_support_ball ε (mem_correction_range' S hε) t h
    · exact scaledPacket_slice_ball S hε ht h
  velocityDifference_divFree := by
    intro ε hε t ht x
    rw [velocityDifference_eq]
    exact S.correction.perturbation_divergence_free ε (mem_correction_range' S hε) t ht x
  pressureDifference_formula := by
    intro ε z; simp only [insertedPressure]; abel
  pressureDifference_support := by
    intro ε hε t ht
    have heq : (fun x : Contracts.V1.Space =>
        insertedPressure S ε (t, x) - S.correction.π (t, x)) =
        fun x : Contracts.V1.Space => S.P ε (t, x) := by
      funext x; simp only [insertedPressure]; abel
    rw [heq]
    exact scaledPressure_slice_ball S hε ht
  forceDifference_compact := by
    intro ε hε
    rw [forceDifference_eq']
    refine ⟨(S.correction.force_smooth ε (mem_correction_range' S hε)).add
        (parabolicForce_smooth P.force_smooth (ε⁻¹) (S.correction.T - ε ^ 2)
          S.correction.x₀), ?_, ?_⟩
    · exact (S.correction.force_compactSupport ε (mem_correction_range' S hε)).add
        (scaledForce_positive_support S hε).1
    · intro z hz
      rcases tsupport_binop_subset (fun p q : Contracts.V1.Space => p + q) (by simp)
          (S.correction.forceCorrection ε) (S.F ε) hz with h | h
      · exact ⟨S.correction.force_positive_time ε (mem_correction_range' S hε) z h, mem_univ _⟩
      · exact (scaledForce_positive_support S hε).2 h
  forceDifference_ball := by
    intro ε hε z hz
    rw [forceDifference_eq'] at hz
    rcases tsupport_binop_subset (fun p q : Contracts.V1.Space => p + q) (by simp)
        (S.correction.forceCorrection ε) (S.F ε) hz with h | h
    · exact S.correction.force_support_ball ε (mem_correction_range' S hε) z h
    · exact scaledForce_ball S hε z h
  blowup := by
    intro ε hε
    have h : Contracts.V1.SpeedUnboundedAt S.correction.T
        (fun z => (S.correction.v z + S.correction.correction ε z) + S.U ε z) :=
      inserted_speed (T := S.correction.T)
        (b := fun z => S.correction.v z + S.correction.correction ε z) (U := S.U ε)
        (S.scaledBlowup ε (mem_scaling_range S hε))
        (fun t ht x hx =>
          (S.correction.correction_cancels_germ ε (mem_correction_range' S hε) t ht x
            hx).self_of_nhds)
    exact h
  energyRate := by
    intro ε hε
    rw [velocityDifference_eq]
    exact S.perturbationEnergyBound ε (mem_scaling_range S hε)
  forceConvergence := by
    intro q hq s hs
    have heq : (fun ε : ℝ => Contracts.V1.Data.forceSobolevENorm q s
          (fun z => insertedForce S ε z - S.correction.g z)) =
        fun ε : ℝ => Contracts.V1.Data.forceSobolevENorm q s
          (fun z => S.correction.forceCorrection ε z + S.F ε z) := by
      funext ε; rw [forceDifference_eq']
    rw [heq]
    exact S.forceConvergence q hq s hs

end Family

end BlowupDensity.Bindings
