import NSFormalization.Section3.T23.NormBridge
import NSFormalization.Section3.T24.AffineEnergy
import NSFormalization.Paper1.ScalingLimits

/-! Domain restriction and closeness rates for T23. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.I02 (spatialGradient)
open scoped ENNReal Topology

/-- Restricting the spatial measure contracts both summands of the energy. -/
theorem domainEnergyENorm_le (Ω : Set Space) (T : ℝ) (z : VelocityField) :
    domainEnergyENorm Ω T z ≤ NSFormalization.Section3.T24.energyENorm T z := by
  apply add_le_add
  · exact essSup_mono_ae (Filter.Eventually.of_forall fun t =>
      eLpNorm_mono_measure (fun x => z (t, x)) Measure.restrict_le_self)
  · apply ENNReal.rpow_le_rpow _ (by norm_num)
    apply lintegral_mono
    intro t
    exact ENNReal.rpow_le_rpow
      (eLpNorm_mono_measure (fun x => spatialGradient z t x) Measure.restrict_le_self)
      (by norm_num)

/-- The whole-space correction constant is made nonnegative once, before ε. -/
def energyConst (C : ℝ) : ℝ := max C 0

theorem energyConst_nonneg (C : ℝ) : 0 ≤ energyConst C := le_max_right _ _

/-- Transport the canonical I03 perturbation energy estimate, with its two
separate exponents, through restriction and the insertion formula. -/
theorem energyRate {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K Ω : Set Space} {a : Space → Space} {g : VelocityField}
    (place : DomainPlacementData u p f K) {δ : ℝ} (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (velocity : ℝ → VelocityField) (M E C ε₀ : ℝ)
    (hformula : ∀ ε z, velocity ε z = reference.velocity z + D.correction ε z +
      NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z)
    (hwhole : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section3.T24.energyENorm place.T
        (fun z => D.correction ε z +
          NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z) ≤
        ENNReal.ofReal ((M + E) * ε ^ ((1 : ℝ) / 2) + C * ε ^ ((3 : ℝ) / 2))) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainEnergyENorm Ω place.T (fun z => velocity ε z - reference.velocity z) ≤
        ENNReal.ofReal ((M + E) * ε ^ ((1 : ℝ) / 2) +
          energyConst C * ε ^ ((3 : ℝ) / 2)) := by
  intro ε hε
  have heq : (fun z => velocity ε z - reference.velocity z) =
      (fun z => D.correction ε z +
        NSFormalization.Section3.T15.scaledVelocity u place.x₀ place.T ε z) := by
    funext z
    rw [hformula]
    abel
  rw [heq]
  exact (domainEnergyENorm_le Ω place.T _).trans ((hwhole ε hε).trans
    (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hε.1.le _)))))

/-- One positive constant absorbs both suppliers, chosen before ε. -/
def forceDiffSobolevConst (A B : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * (|A s| + |B s|) + 1

theorem forceDiffSobolevConst_pos (A B : ℝ → ℝ) (s : ℝ) :
    0 < forceDiffSobolevConst A B s := by
  unfold forceDiffSobolevConst
  positivity

/-- The two inhomogeneous order-zero terms are absorbed for ε ≤ 1 and s ≥ 0. -/
theorem positive_rates_absorb (A B s ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 0 ≤ s) :
    max A 0 * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)) +
      max B 0 * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)) ≤
      (2 * (|A| + |B|) + 1) *
        (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)) := by
  have h1 := Real.rpow_le_rpow_of_exponent_ge hε hε1
    (show (1 : ℝ) / 2 - s ≤ 1 / 2 by linarith)
  have h3 := Real.rpow_le_rpow_of_exponent_ge hε hε1
    (show (3 : ℝ) / 2 - s ≤ 3 / 2 by linarith)
  have ha : max A 0 ≤ |A| := max_le (le_abs_self _) (abs_nonneg _)
  have hb : max B 0 ≤ |B| := max_le (le_abs_self _) (abs_nonneg _)
  have hx := Real.rpow_nonneg hε.le ((1 : ℝ) / 2 - s)
  have hy := Real.rpow_nonneg hε.le ((3 : ℝ) / 2 - s)
  have hA := mul_le_mul ha (add_le_add h1 le_rfl)
    (add_nonneg (Real.rpow_nonneg hε.le _) hx) (abs_nonneg A)
  have hB := mul_le_mul hb (add_le_add h3 le_rfl)
    (add_nonneg (Real.rpow_nonneg hε.le _) hy) (abs_nonneg B)
  nlinarith [mul_nonneg (abs_nonneg A) hy, mul_nonneg (abs_nonneg B) hx]

/-- Combine the q = 1 packet and correction path estimates before restricting
to the domain. The hypotheses are precisely the separate supplier rates. -/
theorem force_sum_rate {s ε A B : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (F H : VelocityField)
    (hF : ∀ t, 0 ≤ t → Continuous (fun x => F (t, x)))
    (hH : ∀ t, 0 ≤ t → Continuous (fun x => H (t, x)))
    (hpacket : NSFormalization.Section4.D01.forceSobolevENorm 1 s F ≤
      ENNReal.ofReal (A * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))))
    (hcorr : NSFormalization.Section4.D01.forceSobolevENorm 1 s H ≤
      ENNReal.ofReal (B * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))) :
    (∫⁻ t in Ioi (0 : ℝ), NSFormalization.Section4.D01.sobolevENorm s
      (fun x => H (t, x) + F (t, x))) ≤
      ENNReal.ofReal ((2 * (|A| + |B|) + 1) *
        (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  have hA : 0 ≤ max A 0 * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s)) :=
    mul_nonneg (le_max_right _ _) (add_nonneg (Real.rpow_nonneg hε.le _)
      (Real.rpow_nonneg hε.le _))
  have hB : 0 ≤ max B 0 * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)) :=
    mul_nonneg (le_max_right _ _) (add_nonneg (Real.rpow_nonneg hε.le _)
      (Real.rpow_nonneg hε.le _))
  have hp := hpacket.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left A 0)
      (add_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hε.le _))))
  have hc := hcorr.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left B 0)
      (add_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hε.le _))))
  apply (lintegral_sobolevENorm_le_forceSobolevENorm s (fun z => H z + F z)).trans
  apply (forceSobolevENorm_add_le_of_continuous hs H F hH hF).trans
  apply (add_le_add hc hp).trans
  rw [add_comm, ← ENNReal.ofReal_add hA hB]
  exact ENNReal.ofReal_le_ofReal (positive_rates_absorb A B s ε hε hε1 hs)

/-- The exact domain force-rate field, with U2b's separate whole-space
estimates and U5's left comparison explicitly threaded. -/
theorem forceDifference_sobolev_bound {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K Ω : Set Space} {a : Space → Space} {g : VelocityField}
    (place : DomainPlacementData u p f K) {δ : ℝ} (D : CutoffData)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (force : ℝ → VelocityField) (ε₀ : ℝ) (A B : ℝ → ℝ)
    (he1 : ε₀ ≤ 1)
    (hformula : ∀ ε z, force ε z = g z + correctionForce ν reference.velocity D ε z +
      NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε z)
    (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t,
      Function.support (fun x => force ε (t, x) - g (t, x)) ⊆ Ω)
    (hleft : ∀ s, ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        zeroExtForceSobolevENorm Ω s (fun z => force ε z - g z))
    (hF : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, 0 ≤ t → Continuous
      (fun x => NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε (t, x)))
    (hH : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t, 0 ≤ t → Continuous
      (fun x => correctionForce ν reference.velocity D ε (t, x)))
    (hpacket : ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section4.D01.forceSobolevENorm 1 s
        (NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε) ≤
      ENNReal.ofReal (A s * (ε ^ ((1 : ℝ) / 2) + ε ^ ((1 : ℝ) / 2 - s))))
    (hcorr : ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      NSFormalization.Section4.D01.forceSobolevENorm 1 s
        (correctionForce ν reference.velocity D ε) ≤
      ENNReal.ofReal (B s * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))) :
    ∀ s, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      domainForceSobolevENorm Ω s (fun z => force ε z - g z) ≤
        ENNReal.ofReal (forceDiffSobolevConst A B s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  intro s hs hs' ε hε
  apply (hleft s ε hε).trans
  have heq : ∀ t, NSFormalization.Section3.T22.zeroExtension Ω
      (fun x => force ε (t, x) - g (t, x)) =
      (fun x => correctionForce ν reference.velocity D ε (t, x) +
        NSFormalization.Section3.T15.scaledForce f place.x₀ place.T ε (t, x)) := by
    intro t
    have hzero : NSFormalization.Section3.T22.zeroExtension Ω
        (fun x => force ε (t, x) - g (t, x)) =
        (fun x => force ε (t, x) - g (t, x)) := by
      funext x
      by_cases hx : x ∈ Ω
      · simp [NSFormalization.Section3.T22.zeroExtension, hx]
      · have hz : force ε (t, x) - g (t, x) = 0 := by
          by_contra hn
          exact hx (hsupport ε hε t hn)
        simp [NSFormalization.Section3.T22.zeroExtension, hx, hz]
    rw [hzero]
    funext x
    rw [hformula]
    abel
  unfold zeroExtForceSobolevENorm
  simp_rw [heq]
  exact force_sum_rate hs hε.1 (hε.2.trans he1) _ _ (hF ε hε) (hH ε hε)
    (hpacket s hs hs' ε hε) (hcorr s hs hs' ε hε)

end NSFormalization.Section3.T23
