import NSFormalization.Paper1.LocalizationBoundary
import NSFormalization.Source.InsertionFamily
import NSFormalization.Paper3.SobolevHilbertModel

/-! Concrete bounded-domain interface for Paper 1 `cor:boundary`. -/
noncomputable section
namespace NSFormalization.Paper1.BoundaryCorollary
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.LocalizationBoundary
open NSFormalization.Paper3
open scoped SchwartzMap

def IsDomainExtension (Ω : Set Space) (s : ℝ) (f : Space → ℂ)
    (h : SobolevHilbert s) : Prop :=
  ∀ ψ : SchwartzMap Space ℂ, (∀ x, x ∉ Ω → ψ x = 0) →
    sobolevRealization s h ψ = ∫ x in Ω, ψ x * f x

def domainSobolevNorm (Ω : Set Space) (s : ℝ) (f : Space → ℂ) : ℝ≥0∞ :=
  sInf ((fun h : SobolevHilbert s => ENNReal.ofReal ‖h‖) ''
    {h | IsDomainExtension Ω s f h})

def domainForceNorm (Ω : Set Space) (s : ℝ) (G : VelocityField) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ => ∑ i : Fin 3,
    domainSobolevNorm Ω s (fun x => (G (t, x) i : ℂ))) 1 volume

structure BoundedReference (Ω : Set Space) (ν T δ : ℝ)
    (a : Space → Space) (v : VelocityField) (π : PressureField) (g : VelocityField) : Prop where
  measurable : MeasurableSet Ω
  positive_time : 0 < T
  positive_extension : 0 < δ
  smooth : ContDiffOn ℝ ∞ v ((Icc (0 : ℝ) (T + δ)) ×ˢ closure Ω)
  pressure_smooth : ContDiffOn ℝ ∞ π ((Icc (0 : ℝ) (T + δ)) ×ˢ closure Ω)
  divergence_free : ∀ t ∈ Icc (0 : ℝ) (T + δ), ∀ x ∈ Ω,
    spatialDivergence v t x = 0
  equation : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Ω,
    Source.residual ν v π t x = g (t, x)
  initial : ∀ x ∈ Ω, v (0, x) = a x
  no_slip : ∀ t ∈ Icc (0 : ℝ) (T + δ), ∀ x ∈ frontier Ω, v (t, x) = 0

def BoundedFlow (Ω : Set Space) (ν : ℝ) (a : Space → Space)
    (g : VelocityField) (T : ℝ) : Prop :=
  ∃ velocity : VelocityField, ∃ pressure : PressureField,
    0 < T ∧
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) T ×ˢ closure Ω) ∧
    ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) T ×ˢ closure Ω) ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ Ω, spatialDivergence velocity t x = 0) ∧
    (∀ t ∈ Ioo (0 : ℝ) T, ∀ x ∈ Ω,
      Source.residual ν velocity pressure t x = g (t, x)) ∧
    (∀ x ∈ Ω, velocity (0, x) = a x) ∧
    (∀ t ∈ Ico (0 : ℝ) T, ∀ x ∈ frontier Ω, velocity (t, x) = 0)

theorem noSlip_of_boundary_agreement
    {Ω K : Set Space} {u v : VelocityField}
    (hboundary : ∀ t, ∀ x ∈ frontier Ω, v (t, x) = 0)
    (hcollar : ∀ t, ∀ x ∈ frontier Ω, x ∉ K → u (t, x) = v (t, x))
    (hK : ∀ x ∈ K, x ∉ frontier Ω) :
    ∀ t, ∀ x ∈ frontier Ω, u (t, x) = 0 := by
  intro t x hx
  have hxK : x ∉ K := fun h => hK x h hx
  rw [hcollar t x hx hxK, hboundary t x hx]

theorem bounded_energy_restriction
    {Ω : Set Space} (hΩ : MeasurableSet Ω) {u : VelocityField} {t : ℝ}
    (h0 : Integrable (fun x => ‖u (t, x)‖ ^ 2))
    (h1 : ∀ i : Fin 3, Integrable (fun x =>
      ‖NavierStokes.PeriodicIntegration.spatialPartial i
        (fun y => u (t, y)) x‖ ^ 2)) :
    domainL2Sq Ω u t ≤ ∫ x : Space, ‖u (t, x)‖ ^ 2 ∧
      domainDissipation Ω u t ≤ NavierStokesR3.CompactEnergy.dissipation u t := by
  exact ⟨domainL2Sq_le_whole hΩ h0, domainDissipation_le_whole hΩ h1⟩

/- The full bounded-domain insertion; local existence and zero-extension
   comparison are the explicit remaining bridge, represented by `sorry`. -/
theorem exists_interior_noSlip_insertion
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g)
    {B : Set Space} (hBopen : IsOpen B) (hBcompact : IsCompact B)
    (hBinterior : B ⊆ Ω) (hBnonempty : B.Nonempty) :
    ∃ (U G : ℝ → VelocityField), ∃ P : ℝ → PressureField,
      (∀ ε, 0 < ε → BoundedFlow Ω ν a (G ε) T) ∧
      (∀ ε, 0 < ε → ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ frontier Ω,
        U ε (t, x) = 0) ∧
      (∀ ε, 0 < ε → ∀ t ∈ Ico (0 : ℝ) T,
        tsupport (fun x => U ε (t, x) - v (t, x)) ⊆ B) ∧
      (∀ s : ℝ, s < (1 : ℝ) / 2 →
        Tendsto (fun ε : ℝ => domainForceNorm Ω s (G ε)) (𝓝[>] 0) (𝓝 0)) := by
  sorry

end NSFormalization.Paper1.BoundaryCorollary
