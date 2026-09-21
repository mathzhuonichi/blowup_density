import NSFormalization.Section3.T23.InteriorBlowup

/-! T23 U8: compact-domain lifespan and maximality. -/

noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

/-- A longer solution is uniformly bounded on the compact terminal slab,
including the boundary of the domain. -/
theorem ClassicalSolutionOmega.speed_bound {ν S T : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField}
    (w : ClassicalSolutionOmega ν Ω a g S) (hΩ : Bornology.IsBounded Ω) (hTS : T < S) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ closure Ω, ‖w.velocity (t, x)‖ ≤ C := by
  obtain ⟨N, _hN, hsub, hs⟩ := w.velocity_smooth
  have hsub' : Icc (0 : ℝ) T ×ˢ closure Ω ⊆ N := by
    intro z hz
    exact hsub ⟨⟨hz.1.1, hz.1.2.trans_lt hTS⟩, hz.2⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hΩ.isCompact_closure).exists_bound_of_continuousOn
    (hs.continuousOn.mono hsub')
  exact ⟨C, fun t ht x hx => hC (t, x) ⟨ht, hx⟩⟩

/-- Every actual solution horizon contributes to the defining supremum. -/
theorem domainLifespan_ge_horizon {ν T : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (w : ClassicalSolutionOmega ν Ω a g T) :
    ENNReal.ofReal T ≤ domainMaximalLifespan ν Ω a g := by
  exact le_iSup_of_le T (le_iSup_of_le (Nonempty.intro w) le_rfl)

/-- Uniqueness on the domain and an interior witness exclude every longer
solution. The scalar IBP input is supplied by `BoundaryIntegration`. -/
theorem domainLifespan_eq_of_interior {ν T : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (hν : 0 < ν)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hI : IBP Ω)
    (u : ClassicalSolutionOmega ν Ω a g T)
    (hblow : ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 T ∧ T - δ < t ∧ x ∈ Ω ∧ M < ‖u.velocity (t, x)‖) :
    domainMaximalLifespan ν Ω a g = ENNReal.ofReal T := by
  apply le_antisymm _ (domainLifespan_ge_horizon u)
  by_contra hcon
  have hcon' : ENNReal.ofReal T <
      ⨆ S : ℝ, ⨆ _ : Nonempty (ClassicalSolutionOmega ν Ω a g S), ENNReal.ofReal S :=
    not_le.mp hcon
  obtain ⟨S, hS⟩ := lt_iSup_iff.mp hcon'
  obtain ⟨⟨w⟩, hTS⟩ := lt_iSup_iff.mp hS
  have hTSr : T < S := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.horizon_pos.le).mp hTS
  obtain ⟨C, hC⟩ := w.speed_bound hb hTSr
  have hmax0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  obtain ⟨t, x, ht, _, hx, hlarge⟩ :=
    hblow (max C 0 + 1) (by linarith) T u.horizon_pos
  have heq := velocity_eq_of_ibp hν hI ho hb u w
    (show t ∈ Ico 0 (min T S) from ⟨ht.1.le, by rw [min_eq_left hTSr.le]; exact ht.2⟩) hx
  rw [heq] at hlarge
  have hbound := hC t ⟨ht.1.le, ht.2.le⟩ x (subset_closure hx)
  have := le_max_left C 0
  linarith

/-- Restriction preserves the literal total velocity and pressure fields. -/
def ClassicalSolutionOmega.restrictHorizon {ν T S : ℝ} {Ω : Set Space}
    {a : SpatialField} {g : SpaceTimeField} (u : ClassicalSolutionOmega ν Ω a g T)
    (hS : 0 < S) (hST : S ≤ T) : ClassicalSolutionOmega ν Ω a g S where
  velocity := u.velocity
  pressure := u.pressure
  horizon_pos := hS
  velocity_smooth := by
    obtain ⟨N, ho, hsub, hs⟩ := u.velocity_smooth
    exact ⟨N, ho, fun z hz => hsub ⟨⟨hz.1.1, hz.1.2.trans_le hST⟩, hz.2⟩, hs⟩
  pressure_smooth := by
    obtain ⟨N, ho, hsub, hs⟩ := u.pressure_smooth
    exact ⟨N, ho, fun z hz => hsub ⟨⟨hz.1.1, hz.1.2.trans_le hST⟩, hz.2⟩, hs⟩
  initial := u.initial
  divergence := fun t ht => u.divergence t ⟨ht.1, ht.2.trans_le hST⟩
  momentum := fun t ht => u.momentum t ⟨ht.1, ht.2.trans_le hST⟩
  no_slip := fun t ht => u.no_slip t ⟨ht.1, ht.2.trans_le hST⟩
  pressure_gauge := fun t ht => u.pressure_gauge t ⟨ht.1, ht.2.trans_le hST⟩

namespace U8

variable {U f : VelocityField} {p : PressureField} {K Ω : Set Space}
  (place : DomainPlacementData U p f K) (D : CutoffData)
  {ν δ : ℝ} {a : NSFormalization.Section4.A02.SpatialField} {g : VelocityField}
  (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
  {ε₀ : ℝ} {velocity force : ℝ → VelocityField} {pressure : ℝ → PressureField}
  (hspeed : SpeedUnboundedAtOne U) (hscale : ε₀ ≤ place.ε₀)
  (hball : closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω)
  (hformula : ∀ ε z, velocity ε z = reference.velocity z + D.correction ε z +
    NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε z)
  (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) place.T,
    tsupport (fun x => NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε (t, x)) ⊆
      Metric.ball place.chartCenter place.chartRadius)
  (hcancel : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (place.T - ε ^ 2) place.T,
    ∀ x ∈ tsupport (fun y => NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε (t, y)),
      reference.velocity (t, x) + D.correction ε (t, x) = 0)
  (hsolution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionOmega ν Ω a (force ε) place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε)

variable (hν : 0 < ν) (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hI : IBP Ω)
include hspeed hscale hball hformula hsupport hcancel hsolution hν ho hb hI

/-- The exact lifespan API field. Box IBP is discharged by `ibp_box`; the
regular-level branch retains precisely the scalar identity authorized in G1. -/
theorem lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T := by
  intro ε hε
  obtain ⟨w, hw, _⟩ := hsolution ε hε
  apply domainLifespan_eq_of_interior hν ho hb hI w
  intro M hM d hd
  obtain ⟨t, x, ht, hn, _, hx, hl⟩ :=
    interior place D reference hspeed hscale hball hformula hsupport hcancel ε hε M hM d hd
  exact ⟨t, x, ht, hn, hx, by rwa [hw]⟩

/-- Every shorter positive horizon is realized by the same total fields. -/
theorem maximal : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalDomainSolution ν Ω a (force ε) (velocity ε) (pressure ε) := by
  intro ε hε
  have hL := lifespan place D reference hspeed hscale hball hformula hsupport hcancel
    hsolution hν ho hb hI ε hε
  refine ⟨?_, ?_⟩
  · rw [hL]
    exact ENNReal.ofReal_pos.mpr place.time_pos
  · intro S hS hSL
    rw [hL] at hSL
    have hST : S ≤ place.T :=
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS.le).mp hSL).le
    obtain ⟨w, hw, hp⟩ := hsolution ε hε
    exact ⟨w.restrictHorizon hS hST, hw, hp⟩

omit ho hb hI in
/-- The box specialization has no unproved integration-by-parts premise. -/
theorem lifespan_box (hbox : IsBoxDomain Ω) : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    domainMaximalLifespan ν Ω a (force ε) = ENNReal.ofReal place.T := by
  exact lifespan place D reference hspeed hscale hball hformula hsupport hcancel hsolution
    hν hbox.open_bounded.1 hbox.open_bounded.2 (ibp_box hbox)

omit ho hb hI in
/-- Maximality on boxes follows from proved box IBP and the same family facts. -/
theorem maximal_box (hbox : IsBoxDomain Ω) : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    IsMaximalDomainSolution ν Ω a (force ε) (velocity ε) (pressure ε) := by
  exact maximal place D reference hspeed hscale hball hformula hsupport hcancel hsolution
    hν hbox.open_bounded.1 hbox.open_bounded.2 (ibp_box hbox)

end U8
end NSFormalization.Section3.T23
