import NavierStokes.R3CompactEnergy
import NavierStokes.R3CompactParametricIntegral
import NavierStokes.R3LocalizedEnergyLimit

/-!
# Time evolution of the actual localized kinetic energy
-/

noncomputable section
namespace NavierStokes.R3LocalEnergyEvolution

open Set MeasureTheory ProblemStatement InnerProductSpace
open R3LocalizedEnergyLimit R3CompactParametricIntegral
open scoped ContDiff RealInnerProductSpace

def energyRate (χ : Space → ℝ) (w : VelocityField) (t : ℝ) : ℝ :=
  2 * ∫ x : Space, χ x * ⟪w (t, x), temporalDerivative w t x⟫_ℝ

theorem energy_continuousOn {I : Set ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hI : IsCompact I) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (I ×ˢ (univ : Set Space))) :
    ContinuousOn (fun t => localizedEnergy χ (fun x => w (t, x))) I := by
  apply integral_continuousOn hI hc
    ((hχ.comp continuous_snd).continuousOn.mul (hw.norm_sq ℝ).continuousOn)
  intro t ht x hx
  simp [image_eq_zero_of_notMem_tsupport hx]

theorem energy_hasDerivAt {I : Set ℝ} {χ : Space → ℝ} {w : VelocityField}
    (hI : IsOpen I) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hw : ContDiffOn ℝ ∞ w (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => localizedEnergy χ (fun x => w (s, x))) (energyRate χ w t) t := by
  have hF : ContDiffOn ℝ 1 (fun z : ℝ × Space => χ z.2 * ‖w z‖ ^ 2)
      (I ×ˢ (univ : Set Space)) :=
    (((hχ.comp contDiff_snd).contDiffOn).mul (hw.norm_sq ℝ)).of_le (by simp)
  have h := integral_hasDerivAt_of_contDiffOn hI hc hF
    (fun s hs x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) ht
  have he (x : Space) : deriv (fun s : ℝ => χ x * ‖w (s, x)‖ ^ 2) t =
      2 * (χ x * ⟪w (t, x), temporalDerivative w t x⟫_ℝ) := by
    have hd : DifferentiableAt ℝ (fun s : ℝ => w (s, x)) t :=
      ((hw.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)).comp t
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    rw [((PeriodicUniqueness.energy_density_derivative hd).const_mul (χ x)).deriv]
    ring
  simpa only [he, integral_const_mul, localizedEnergy, energyRate] using h

/-- Smooth solutions of the same forced equation satisfy the localized
energy identity, without global pressure or derivative integrability. -/
theorem difference_energy_balance {χ : Space → ℝ} {u v : VelocityField}
    {p q : PressureField} {t : ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hu : ContDiff ℝ ∞ (fun x : Space => u (t, x)))
    (hv : ContDiff ℝ ∞ (fun x : Space => v (t, x)))
    (hp : ContDiff ℝ ∞ (fun x : Space => p (t, x)))
    (hq : ContDiff ℝ ∞ (fun x : Space => q (t, x)))
    (htu : ∀ x, DifferentiableAt ℝ (fun s => u (s, x)) t)
    (htv : ∀ x, DifferentiableAt ℝ (fun s => v (s, x)) t)
    (hdu : ∀ x, spatialDivergence u t x = 0)
    (hdv : ∀ x, spatialDivergence v t x = 0)
    (heq : ∀ x, navierStokesResidual u p t x = navierStokesResidual v q t x) :
    energyRate χ (u - v) t =
      -2 * R3CompactEnergy.dissipation χ (fun x => (u - v) (t, x)) -
      2 * R3CompactEnergy.diffusionFlux χ (fun x => (u - v) (t, x)) +
      R3CompactEnergy.transportFlux χ (fun x => (u - v) (t, x)) (fun x => v (t, x)) -
      2 * R3CompactEnergy.coupling χ (fun x => (u - v) (t, x)) (fun x => u (t, x)) +
      2 * R3CompactEnergy.pressureFlux χ (fun x => (u - v) (t, x)) (fun x => (p - q) (t, x)) := by
  apply R3CompactEnergy.energy_balance hχ (hp.sub hq) (hu.sub hv) hu hv hc
  · intro x
    change spatialDivergence (u - v) t x = 0
    rw [PeriodicUniqueness.spatialDivergence_sub hu hv, hdu, hdv, sub_self]
  · exact hdv
  · intro x
    have h := PeriodicUniqueness.difference_equation hu hv hp hq (htu x) (htv x) (heq x)
    change temporalDerivative (u - v) t x = spatialLaplacian (u - v) t x -
      spatialDerivative (u - v) t x (v (t, x)) -
      spatialDerivative u t x ((u - v) (t, x)) - pressureGradient (p - q) t x
    rw [h]
    abel

end NavierStokes.R3LocalEnergyEvolution
