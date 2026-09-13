import NSFormalization.Paper1.BoundaryCorollary

/-! Safe bookkeeping bridge from a smooth bounded reference to its shorter-horizon flow predicate. -/
noncomputable section
namespace NSFormalization.Paper1.BoundaryCorollary
open Set
open NavierStokes NavierStokes.ProblemStatement
open scoped ContDiff Topology

/-- A `BoundedReference` already supplies a `BoundedFlow` on its reference horizon.
This is restriction/bookkeeping only; it does not assert local existence. -/
theorem boundedFlow_of_reference
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g) :
    BoundedFlow Ω ν a g T := by
  refine ⟨v, π, href.positive_time, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact href.smooth.mono (by
      rintro z ⟨⟨ht0, htT⟩, hx⟩
      exact ⟨⟨ht0, (le_of_lt htT).trans
        (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩, hx⟩)
  · exact href.pressure_smooth.mono (by
      rintro z ⟨⟨ht0, htT⟩, hx⟩
      exact ⟨⟨ht0, (le_of_lt htT).trans
        (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩, hx⟩)
  · intro t ht x hx
    exact href.divergence_free t ⟨ht.1,
      (le_of_lt ht.2).trans (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩ x hx
  · intro t ht x hx
    exact href.equation t ⟨ht.1,
      lt_of_lt_of_le ht.2
        (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩ x hx
  · intro x hx
    exact href.initial x hx
  · intro t ht x hx
    exact href.no_slip t ⟨ht.1,
      ht.2.le.trans (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩ x hx

/-! Support bookkeeping for the boundary insertion interface. -/
theorem noSlip_of_supported_difference
    {Ω B : Set Space} {U v : VelocityField}
    (hboundary : ∀ t, ∀ x ∈ frontier Ω, v (t, x) = 0)
    (hB : ∀ x ∈ B, x ∉ frontier Ω)
    (hsupport : ∀ t : ℝ, ∀ x : Space,
      x ∈ tsupport (fun y => U (t, y) - v (t, y)) → x ∈ B)
    : ∀ t, ∀ x ∈ frontier Ω, U (t, x) = 0 := by
  intro t x hx
  have hxB : x ∉ B := fun h => hB x h hx
  have hxSupport : x ∉ tsupport (fun y => U (t, y) - v (t, y)) :=
    fun h => hxB (hsupport t x h)
  have hdiff : U (t, x) - v (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y : Space => U (t, y) - v (t, y)) hxSupport
  rw [hboundary t x hx, sub_zero] at hdiff
  exact hdiff


/-- Pointwise support hypotheses assemble into a time-slice support inclusion. -/
theorem tsupport_difference_subset
    {B : Set Space} {U v : VelocityField}
    (hsupport : ∀ t : ℝ, ∀ x : Space,
      x ∈ tsupport (fun y => U (t, y) - v (t, y)) → x ∈ B) (t : ℝ) :
    tsupport (fun y => U (t, y) - v (t, y)) ⊆ B := by
  intro x hx
  exact hsupport t x hx

end NSFormalization.Paper1.BoundaryCorollary

namespace NSFormalization.Paper1.BoundaryCorollary
open Set
open NavierStokes NavierStokes.ProblemStatement

/-- A supported interior perturbation of a bounded reference inherits its
no-slip boundary condition on the reference horizon.  This is a bookkeeping
corollary: it uses only the reference no-slip field and the explicit support
separation from the boundary. -/
theorem noSlip_of_reference_and_supported_difference
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g)
    {B : Set Space} (hB : ∀ x ∈ B, x ∉ frontier Ω)
    {U : ℝ → VelocityField} {ε : ℝ} {t : ℝ}
    (hslice : ∀ t : ℝ, tsupport (fun x : Space =>
        U ε (t, x) - v (t, x)) ⊆ B)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∀ x ∈ frontier Ω, U ε (t, x) = 0 := by
  intro x hx
  have hboundary : v (t, x) = 0 := href.no_slip t (by
    constructor
    · exact ht.1
    · exact le_trans ht.2 (le_add_of_nonneg_right
        (le_of_lt href.positive_extension))) x hx
  have hxB : x ∉ B := fun h => hB x h hx
  have hxSupport : x ∉ tsupport (fun y : Space =>
      U ε (t, y) - v (t, y)) := fun h => hxB (hslice t h)
  have hdiff : U ε (t, x) - v (t, x) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y : Space => U ε (t, y) - v (t, y)) hxSupport
  rw [hboundary, sub_zero] at hdiff
  exact hdiff

end NSFormalization.Paper1.BoundaryCorollary

namespace NSFormalization.Paper1.BoundaryCorollary
open Set
open NavierStokes NavierStokes.ProblemStatement

/-- The reference no-slip condition restricted to its base horizon. -/
theorem reference_noSlip_on_horizon
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ frontier Ω, v (t, x) = 0 := by
  intro t ht x hx
  exact href.no_slip t ⟨ht.1,
    ht.2.trans (le_add_of_nonneg_right (le_of_lt href.positive_extension))⟩ x hx

end NSFormalization.Paper1.BoundaryCorollary

namespace NSFormalization.Paper1.BoundaryCorollary
open Set
open NavierStokes NavierStokes.ProblemStatement

/-! A reusable boundary bridge for parameterized insertion families.  The
support hypothesis is stated on each time slice, so no continuity or PDE
regularity is silently inferred. -/
theorem noSlip_of_horizon_support
    {Ω : Set Space} {ν T δ : ℝ} {a : Space → Space}
    {v : VelocityField} {π : PressureField} {g : VelocityField}
    (href : BoundedReference Ω ν T δ a v π g)
    {B : Set Space} (hB : ∀ x ∈ B, x ∉ frontier Ω)
    {U : ℝ → VelocityField} {ε : ℝ}
    (hslice : ∀ t : ℝ, tsupport (fun x : Space =>
        U ε (t, x) - v (t, x)) ⊆ B) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ frontier Ω, U ε (t, x) = 0 := by
  intro t ht x hx
  exact noSlip_of_reference_and_supported_difference href hB
    (fun s => hslice s) ht x hx

end NSFormalization.Paper1.BoundaryCorollary
