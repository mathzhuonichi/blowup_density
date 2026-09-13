import NSFormalization.Paper1.PeriodicLifespan

/-!
# Conservative periodic forcing: a source-backed zero solution consequence

This is the exact conservative-force consequence used by Paper 1's
`prop:conservative` branch.  The uniqueness input is OpenAI's proved
periodic energy theorem, adapted to arbitrary positive viscosity in
`PeriodicUniqueness.classical_uniqueness_on_Icc`.

The negative-gradient force is identified with the actual residual of zero
velocity and pressure `-φ`. Restricting to closed presingular slabs proves
vanishing on the entire half-open classical lifespan. The final theorem
excludes conservative forces for the actual from-rest insertion.
-/
noncomputable section
namespace NSFormalization.Paper1.ConservativeForce

open Set
open scoped ContDiff
open NavierStokes NavierStokes.ProblemStatement

theorem zero_of_conservative_residual {ν S : ℝ} (hν : 0 < ν) (_hS : 0 < S)
    {u : VelocityField} {p φ : PressureField}
    (hu : ContDiffOn ℝ ∞ u (PeriodicUniqueness.slab 0 S))
    (hp : ContDiffOn ℝ ∞ p (PeriodicUniqueness.slab 0 S))
    (hφ : ContDiffOn ℝ ∞ φ (PeriodicUniqueness.slab 0 S))
    (huper : UnitSpatialPeriodsOn (Icc (0 : ℝ) S) u)
    (hpper : UnitSpatialPeriodsOn (Icc (0 : ℝ) S) p)
    (hφper : UnitSpatialPeriodsOn (Icc (0 : ℝ) S) φ)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      Source.residual ν u p t x =
        Source.residual ν (fun _ => 0) (fun z => -φ z) t x)
    (hinit : ∀ x, u (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) S, ∀ x, u (t, x) = 0 := by
  have hzero_smooth : ContDiffOn ℝ ∞ (fun _ : SpaceTime => (0 : Space))
      (PeriodicUniqueness.slab 0 S) := contDiffOn_const
  have hnegφ : ContDiffOn ℝ ∞ (fun z : SpaceTime => -φ z)
      (PeriodicUniqueness.slab 0 S) := hφ.neg
  have hzero_per : UnitSpatialPeriodsOn (Icc (0 : ℝ) S)
      (fun _ : SpaceTime => (0 : Space)) := by
    intro t ht x i
    simp
  have hnegφper : UnitSpatialPeriodsOn (Icc (0 : ℝ) S)
      (fun z : SpaceTime => -φ z) := by
    intro t ht x i
    simpa only [Pi.neg_apply] using congrArg Neg.neg (hφper t ht x i)
  have heq := NSFormalization.Paper1.PeriodicUniqueness.classical_uniqueness_on_Icc hν
    hu hzero_smooth hp hnegφ huper hzero_per hpper hnegφper
    (f := fun z : SpaceTime => Source.residual ν (fun _ => 0) (fun y => -φ y) z.1 z.2)
    hdiv
    (by intro t ht x; simp [spatialDivergence, spatialDerivative])
    (by intro t ht x; exact hNS t ht x)
    (by intro t ht x; rfl)
    (by intro x; simpa using hinit x)
  exact heq

/-- The physical conservative force is exactly the residual of the resting
velocity with pressure `-φ`, at every viscosity. -/
theorem zero_velocity_negative_potential_residual (ν : ℝ) (φ : PressureField)
    (t : ℝ) (x : Space) :
    Source.residual ν (fun _ => 0) (fun z => -φ z) t x =
      -pressureGradient φ t x := by
  simp [Source.residual, temporalDerivative, advection, spatialLaplacian,
    spatialDerivative, pressureGradient, fderiv_fun_neg, Finset.sum_neg_distrib]

/-- The periodic branch of conservative forcing from rest on a closed
classical slab, stated using the actual force `-∇φ`. -/
theorem zero_of_negative_gradient_on_Icc {ν b : ℝ} (hν : 0 < ν) (hb : 0 < b)
    {u : VelocityField} {p φ : PressureField}
    (hu : ContDiffOn ℝ ∞ u (PeriodicUniqueness.slab 0 b))
    (hp : ContDiffOn ℝ ∞ p (PeriodicUniqueness.slab 0 b))
    (hφ : ContDiffOn ℝ ∞ φ (PeriodicUniqueness.slab 0 b))
    (huper : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) u)
    (hpper : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) p)
    (hφper : UnitSpatialPeriodsOn (Icc (0 : ℝ) b) φ)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) b, ∀ x,
      Source.residual ν u p t x = -pressureGradient φ t x)
    (hinit : ∀ x, u (0, x) = 0) :
    ∀ t ∈ Icc (0 : ℝ) b, ∀ x, u (t, x) = 0 := by
  apply zero_of_conservative_residual hν hb hu hp hφ huper hpper hφper hdiv
    (hinit := hinit)
  intro t ht x
  rw [zero_velocity_negative_potential_residual]
  exact hNS t ht x

/-- Any smooth periodic solution from rest with conservative force vanishes
at every presingular time. No endpoint extension of the solution is assumed. -/
theorem zero_of_negative_gradient_on_Ico {ν S : ℝ} (hν : 0 < ν)
    {u : VelocityField} {p φ : PressureField}
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hφ : ContDiffOn ℝ ∞ φ (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (huper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) u)
    (hpper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) p)
    (hφper : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) φ)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      Source.residual ν u p t x = -pressureGradient φ t x)
    (hinit : ∀ x, u (0, x) = 0) :
    ∀ t ∈ Ico (0 : ℝ) S, ∀ x, u (t, x) = 0 := by
  intro t ht x
  by_cases ht0 : t = 0
  · simpa only [ht0] using hinit x
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hsub : PeriodicUniqueness.slab 0 t ⊆ Ico (0 : ℝ) S ×ˢ (univ : Set Space) :=
    fun z hz => ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
  have htime : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) S :=
    fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  exact zero_of_negative_gradient_on_Icc hν htpos
    (hu.mono hsub) (hp.mono hsub) (hφ.mono hsub)
    (fun s hs => huper s (htime hs))
    (fun s hs => hpper s (htime hs))
    (fun s hs => hφper s (htime hs))
    (fun s hs => hdiv s ⟨hs.1, hs.2.trans ht.2⟩)
    (fun s hs => hNS s ⟨hs.1, hs.2.trans ht.2⟩)
    hinit t ⟨ht.1, le_rfl⟩ x

/-- The force of any actual from-rest periodic insertion cannot be the
negative gradient of a smooth globally periodic potential on its lifespan. -/
theorem inserted_force_not_conservative {ν r T τ : ℝ}
    (hν : 0 < ν) (hτ : 0 ≤ τ)
    {v g U F : VelocityField} {q P : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (ha : ∀ x, v (0, x) = 0) :
    ¬ ∃ φ : PressureField,
      ContDiffOn ℝ ∞ φ (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) ∧
      UnitSpatialPeriodsOn (Ico (0 : ℝ) T) φ ∧
      (∀ t ∈ Ioo (0 : ℝ) T, ∀ x,
        g (t, x) + F (t, x) = -pressureGradient φ t x) := by
  rintro ⟨φ, hφ, hφper, hf⟩
  have hz := zero_of_negative_gradient_on_Ico hν
    h.velocity_smooth h.pressure_smooth hφ h.velocity_periodic
    h.pressure_periodic hφper
    (fun t ht => h.divergence_free t ⟨ht.1.le, ht.2⟩)
    (fun t ht x => (h.equation t ht x).trans (hf t ht x))
    (fun x => ((h.history 0 hτ x).1).trans (ha x))
  obtain ⟨t, x, ht, _, _, hlarge⟩ :=
    h.local_speed_unbounded 1 zero_lt_one 1 zero_lt_one
  have hbad : (1 : ℝ) < 0 := by
    simpa only [hz t ⟨ht.1.le, ht.2⟩ x, norm_zero] using hlarge
  exact (not_lt_of_ge zero_le_one) hbad

end NSFormalization.Paper1.ConservativeForce
