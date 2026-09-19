import NSFormalization.Section3.T23.Triple

/-! Fieldwise construction of the canonical ten-field domain solution.
Only the U4 no-slip conclusion and the matching packet supplier facts are
threaded; the U3 analytic fields are proved in the imported modules. -/
noncomputable section
namespace NSFormalization.Section3.T23.InsertedTriple
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T15 (scaledVelocity scaledPressure scaledForce)
open scoped ContDiff

variable {ν δ r : ℝ} {Ω K : Set Space} {a : SpatialField} {g : SpaceTimeField}
  {u f : VelocityField} {p : PressureField}
  {place : DomainPlacementData u p f K} {D : CutoffData}
  {reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)}

/-- The concrete normalized pressure has zero Ω-integral. -/
theorem pressure_gauge (hδ : 0 < δ) (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) {ε : ℝ}
    (hP : ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    {t : ℝ} (ht : t ∈ Ico 0 place.T) :
    (∫ x in Ω, pressure place reference ε (t, x)) = 0 := by
  apply domainNormalizePressure_integral ho hb hne
  apply SmoothOnClosedSlab.integrableOn_slice hb (p := fun z =>
    reference.pressure z + scaledPressure p place.x₀ place.T ε z) _ ht
  exact (reference.pressure_smooth.mono_time
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)).add
    ⟨_, isOpen_Iio.prod isOpen_univ, fun z hz => ⟨hz.1.2, mem_univ _⟩, hP⟩

/-- All ten fields, at the actual inserted triple and unchanged horizon. -/
def classicalSolution (hδ : 0 < δ) (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc 0 D.ε₀) (hplace : ε ∈ Ioc 0 place.ε₀)
    (hU : ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (hP : ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (hdiv : ∀ t : ℝ, t < place.T → ∀ x : Space,
      spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0)
    (heq : ∀ t : ℝ, t < place.T → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (scaledVelocity u place.x₀ place.T ε) (scaledPressure p place.x₀ place.T ε) t x =
        scaledForce f place.x₀ place.T ε (t, x))
    (hnoSlip : ∀ t ∈ Ico 0 place.T, ∀ x ∈ frontier Ω,
      velocity place D reference ε (t, x) = 0) :
    ClassicalSolutionOmega ν Ω a (force place D reference ε) place.T where
  velocity := velocity place D reference ε
  pressure := pressure place reference ε
  horizon_pos := place.time_pos
  velocity_smooth := velocity_smooth hδ C hε hU
  pressure_smooth := pressure_smooth hδ hb ho.measurableSet hP
  initial := fun _ hx => initial C hε hplace hx
  divergence := fun _ ht _ hx => incompressible hδ C hε hU hdiv ht hx
  momentum := fun _ ht _ hx => momentum hδ C hε hU hP heq ht hx
  no_slip := hnoSlip
  pressure_gauge := fun _ ht => pressure_gauge hδ ho hb hne hP ht

/-- The exact API solution field on the common threshold, with U4 threaded. -/
theorem solution (hδ : 0 < δ) (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    (C : WindowedCorrectionCore reference.velocity u K place.x₀ r place.T δ D)
    (s b : ℝ)
    (hU : ∀ ε ∈ Ioc (0 : ℝ) s, ContDiffOn ℝ ∞ (scaledVelocity u place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (hP : ∀ ε ∈ Ioc (0 : ℝ) s, ContDiffOn ℝ ∞ (scaledPressure p place.x₀ place.T ε)
      (Iio place.T ×ˢ (univ : Set Space)))
    (hdiv : ∀ ε ∈ Ioc (0 : ℝ) s, ∀ t : ℝ, t < place.T → ∀ x : Space,
      spatialDivergence (scaledVelocity u place.x₀ place.T ε) t x = 0)
    (heq : ∀ ε ∈ Ioc (0 : ℝ) s, ∀ t : ℝ, t < place.T → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (scaledVelocity u place.x₀ place.T ε) (scaledPressure p place.x₀ place.T ε) t x =
        scaledForce f place.x₀ place.T ε (t, x))
    (hnoSlip : ∀ ε ∈ Ioc (0 : ℝ) (threshold place D s b),
      ∀ t ∈ Ico 0 place.T, ∀ x ∈ frontier Ω, velocity place D reference ε (t, x) = 0) :
    ∀ ε ∈ Ioc (0 : ℝ) (threshold place D s b),
      ∃ w : ClassicalSolutionOmega ν Ω a (force place D reference ε) place.T,
        w.velocity = velocity place D reference ε ∧ w.pressure = pressure place reference ε := by
  intro ε hε
  have hc : ε ∈ Ioc (0 : ℝ) D.ε₀ := ⟨hε.1, hε.2.trans (eps_le_cutoff place D s b)⟩
  have hp : ε ∈ Ioc (0 : ℝ) place.ε₀ := ⟨hε.1, hε.2.trans (eps_le_scaling place D s b)⟩
  have hs : ε ∈ Ioc (0 : ℝ) s := ⟨hε.1, hε.2.trans (eps_le_supplier place D s b)⟩
  exact ⟨classicalSolution hδ ho hb hne C hc hp (hU ε hs) (hP ε hs)
    (hdiv ε hs) (heq ε hs) (hnoSlip ε hε), rfl, rfl⟩
end NSFormalization.Section3.T23.InsertedTriple
