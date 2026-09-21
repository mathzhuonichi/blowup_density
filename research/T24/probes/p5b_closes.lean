import NSFormalization.Section3.T24.MultipleOmegaRegions

/-! The four canonical record fields, with the P5.1/P5.2 facts threaded explicitly.
The probe never assumes an inhabitant of MultipleRegionsOmegaAPI. -/
noncomputable section
namespace NSFormalization.Section3.T24.OmegaRegions.Probe
open Set MeasureTheory
open scoped ContDiff ENNReal Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T15 NSFormalization.Section3.T23
open NSFormalization.Source.PacketScaling (zeroPastField)
open NSFormalization.Section4.A02 (SpatialField)

variable {N : ℕ} {ν T M D : ℝ} {c : Fin N → Space} {r : Fin N → ℝ}
  {u f : VelocityField} {p : PressureField} {K Ω : Set Space} {ε : Fin N → ℝ}
  (placement : Fin N → DomainPlacementData u p f K)
  (component : ∀ j, ClassicalSolutionOmega ν Ω (0 : SpatialField)
    (scaledForce f (placement j).x₀ T (ε j)) T)
  (hd : Pairwise (fun i j : Fin N =>
    Disjoint (Metric.ball (c i) (r i)) (Metric.ball (c j) (r j))))
  (hs : ∀ j, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    x ∉ Metric.ball (c j) (r j) → (component j).velocity (t, x) = 0)
  (hp : ∀ j, (component j).velocity = scaledVelocity u (placement j).x₀ T (ε j) ∧
    (component j).pressure = domainNormalizePressure Ω (scaledPressure p (placement j).x₀ T (ε j)))
  (he : ∀ j, ε j ∈ Ioc (0 : ℝ) (placement j).ε₀)
  (ht : ∀ j, ε j ^ 2 < T)
  (hpt : ∀ j, (placement j).T = T)
  (hpc : ∀ j, (placement j).chartCenter = c j ∧ (placement j).chartRadius = r j)
  (hΩ : ∀ j, closure (Metric.ball (c j) (r j)) ⊆ Ω)
  (av : VelocityField)
  (ha : av = finiteVelocitySum (fun j => (component j).velocity))

include hd hs ha in
theorem agreement : ∀ j, ∀ t ∈ Ico (0 : ℝ) T,
    ∀ x ∈ Metric.ball (c j) (r j), av (t, x) = (component j).velocity (t, x) := by
  subst av
  exact region_agreement hd hs

include hd hs hp he ht ha in
theorem blowup (hb : SpeedUnboundedAtOne u) :
    ∀ j, SpeedUnboundedAtOn T (Metric.ball (c j) (r j)) av := by
  subst av
  exact region_blowup hd hs (fun j => (hp j).1) (fun j => (he j).1) ht hb

variable
  (hext : ContDiffOn ℝ ∞ (zeroPastField u) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
  (hK : IsCompact K)
  (hu : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t, x)) ⊆ K)
  (hsi : ∀ t ∈ Ico (0 : ℝ) 1, NavierStokesR3.ProblemStatement.SquareIntegrableAtTime u t)
  (hz : ∀ x : Space, u (0, x) = 0)
  (hM : IsLUB ((fun t : ℝ => Real.sqrt (NavierStokesR3.CompactEnergy.l2Sq u t)) ''
    Ico (0 : ℝ) 1) M)
  (hdi : IntegrableOn (NavierStokesR3.CompactEnergy.dissipation u) (Ioo (0 : ℝ) 1))
  (hD : D = Real.sqrt (∫ t in Ioo (0 : ℝ) 1, NavierStokesR3.CompactEnergy.dissipation u t))

include hd hs hp he hΩ ha hext hK hu hsi hz hM hdi hD in
theorem energy : energyEssSupOmega Ω T av ^ (2 : ℕ) ≤
    ENNReal.ofReal (M ^ 2 * ∑ j, ε j) := by
  subst av
  exact energy_bound hd hs placement ⟨hext, hK, hu, hsi, hz, hM, hdi, hD⟩
    he (fun j => (hp j).1) hΩ

include hd hp he hpt hpc hΩ ha hext hK hu hsi hz hM hdi hD in
theorem dissipation : energyGradientOmega Ω T av ^ (2 : ℕ) =
    ENNReal.ofReal (D ^ 2 * ∑ j, ε j) := by
  subst av
  exact dissipation_bound hd placement ⟨hext, hK, hu, hsi, hz, hM, hdi, hD⟩
    hpt hpc he (fun j => (hp j).1) hΩ

end NSFormalization.Section3.T24.OmegaRegions.Probe
