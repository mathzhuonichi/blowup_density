import NSFormalization.Section4.A02.Energy
import NSFormalization.Section4.A02.Bounds
import NSFormalization.Section4.A02.Restrict
import NSFormalization.Source.BoundedViscosityUniqueness

/-!
# A02 units U2 and U3: velocity uniqueness and the pressure gauge

`research/A02/COMPARISON.md` §3, units **U2** and **U3**; the two fields of
`UniquenessAPI` (`research/A02/Spec.lean:263-281`).

* `velocity_unique` (U2): two classical whole-space solutions of the *same*
  datum `(ν, a, f)` on horizons `T₁, T₂` have equal velocity fields on the
  common half-open interval `Ico 0 (min T₁ T₂)`.  Route (COMPARISON row U2):
  `NSFormalization.Source.BoundedViscosityUniqueness.classical_uniqueness_on_Icc`
  (`Source/BoundedViscosityUniqueness.lean:23`) on each closed slab `Icc 0 T'`
  with `T' < min T₁ T₂`, then the union over `T'` (implication **I2**).  Its
  hypotheses are discharged by lane 049's `ClassicalSolutionR.uniformFiniteEnergy`
  (U1a, `A02/Energy.lean`), `ClassicalSolutionR.exists_velocity_bound` and
  `exists_gradient_bound` (U1b, `A02/Bounds.lean`); `residual` and the R3
  `navierStokesResidual` used by `ClassicalSolutionR.momentum` are `rfl`-equal,
  so the two momentum fields (both `= f`) give equal residuals.

* `pressure_gauge` (U3): the two pressures are gauge-equivalent
  (`PressureGaugeEquivOn`, differ by a function of time alone) on the same
  interval.  Route (COMPARISON row U3, implication **I3**): from `momentum` at
  both solutions and U2's equal velocities the *velocity part* of the residual
  agrees at interior times, so `pressureGradient u₁.pressure = pressureGradient
  u₂.pressure` on `Ioo 0 (min T₁ T₂)`; `inner_pressureGradient`
  (`vendor/…/NavierStokes/PeriodicUniqueness.lean:307`) turns that into equal
  spatial Fréchet derivatives, `is_const_of_fderiv_eq_zero` makes the pressure
  difference spatially constant on the interior, and continuity of `pressure` at
  `t = 0` (`pressure_smooth` on `Ico 0 T ×ˢ univ`) carries the constant to the
  closed left endpoint, which is exactly the endpoint the `momentum`-on-`Ioo`
  field leaves as a separate step.

The slab-congruence facts U3 needs (`slice_eq_of_eqOn`,
`spatialDerivative_eq_of_eqOn`, `temporalDerivative_eq_of_eqOn`) are reused
directly from `A02/Restrict.lean`'s `section Congr`; since lane 040 both files
share the one `A02/SolutionClass.lean` restatement of the D01 objects, so
`Restrict`, `Energy` and `Bounds` co-import cleanly.
-/

noncomputable section

open Set MeasureTheory Filter
open NavierStokesR3 NavierStokesR3.ProblemStatement
open NavierStokes.ProblemStatement
  (spatialDerivative spatialDivergence temporalDerivative advection spatialLaplacian
    pressureGradient)
open NSFormalization.Source
open scoped ContDiff RealInnerProductSpace Topology

namespace NSFormalization.Section4.A02

/-! ## 0. Pressure-slice smoothness helpers -/

/-- A spatial slice of a pressure field is differentiable at every point of an
*interior* time `t ∈ Ioo 0 T`, because `(t, y)` is then in the interior of the
slab `Ico 0 T ×ˢ univ` where the field is smooth. -/
private theorem pressure_slice_differentiableAt {p : SpaceTimeScalar} {T t : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (ht : t ∈ Ioo (0 : ℝ) T) (y : Space) :
    DifferentiableAt ℝ (fun z : Space => p (t, z)) y := by
  have hAt : ContDiffAt ℝ ∞ p (t, y) :=
    hp.contDiffAt (prod_mem_nhds (Ico_mem_nhds_iff.mpr ht) univ_mem)
  exact (hAt.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)

/-- A time slice `s ↦ p (s, y)` of a pressure field is continuous on `Ico 0 T`. -/
private theorem pressure_time_continuousOn {p : SpaceTimeScalar} {T : ℝ}
    (hp : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space))) (y : Space) :
    ContinuousOn (fun s : ℝ => p (s, y)) (Ico (0 : ℝ) T) :=
  hp.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn)
    (fun _ hs => ⟨hs, mem_univ y⟩)

/-! ## 1. Unit U2: velocity uniqueness -/

/-- **Core of U2.**  Two classical whole-space solutions of the same datum agree
on the common half-open interval.  `classical_uniqueness_on_Icc` on each
`Icc 0 T'`, `T' < min T₁ T₂`, then the union over `T'`. -/
theorem velocity_unique_core {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} (hν : 0 < ν)
    {T₁ T₂ : ℝ} (u₁ : ClassicalSolutionR ν a f T₁) (u₂ : ClassicalSolutionR ν a f T₂) :
    ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
      u₁.velocity (t, x) = u₂.velocity (t, x) := by
  intro t ht x
  have hm : (0 : ℝ) < min T₁ T₂ := lt_min u₁.horizon_pos u₂.horizon_pos
  obtain ⟨T', hT'pos, htT', hT'lt⟩ :
      ∃ T', 0 < T' ∧ t < T' ∧ T' < min T₁ T₂ :=
    ⟨(t + min T₁ T₂) / 2, by linarith [ht.1], by linarith [ht.2], by linarith [ht.2]⟩
  have hT'T₁ : T' < T₁ := lt_of_lt_of_le hT'lt (min_le_left _ _)
  have hT'T₂ : T' < T₂ := lt_of_lt_of_le hT'lt (min_le_right _ _)
  obtain ⟨B, hB0, hB⟩ := u₁.exists_velocity_bound hT'pos.le hT'T₁
  obtain ⟨Gb, hG0, hG⟩ := u₁.exists_gradient_bound hT'pos.le hT'T₁
  have huniq :=
    BoundedViscosityUniqueness.classical_uniqueness_on_Icc (T := T') (ν := ν) hT'pos hν
      (u₁.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hT'T₁⟩, hz.2⟩))
      (u₂.velocity_smooth.mono (fun _ hz => ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hT'T₂⟩, hz.2⟩))
      (u₁.pressure_smooth.mono (fun _ hz => ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hT'T₁⟩, hz.2⟩))
      (u₂.pressure_smooth.mono (fun _ hz => ⟨⟨hz.1.1, lt_of_le_of_lt hz.1.2 hT'T₂⟩, hz.2⟩))
      (u₁.uniformFiniteEnergy hT'pos.le hT'T₁) (u₂.uniformFiniteEnergy hT'pos.le hT'T₂)
      hB0 hB hG0 hG
      (fun s hs y => u₁.divergence s ⟨hs.1.le, hs.2.trans hT'T₁⟩ y)
      (fun s hs y => u₂.divergence s ⟨hs.1.le, hs.2.trans hT'T₂⟩ y)
      (fun s hs y => by
        have h₁ := u₁.momentum s ⟨hs.1, hs.2.trans hT'T₁⟩ y
        have h₂ := u₂.momentum s ⟨hs.1, hs.2.trans hT'T₂⟩ y
        show residual ν u₁.velocity u₁.pressure s y = residual ν u₂.velocity u₂.pressure s y
        calc residual ν u₁.velocity u₁.pressure s y
            = NavierStokesR3.ProblemStatement.navierStokesResidual ν u₁.velocity u₁.pressure s y :=
              rfl
          _ = f (s, y) := h₁
          _ = NavierStokesR3.ProblemStatement.navierStokesResidual ν u₂.velocity u₂.pressure s y :=
              h₂.symm
          _ = residual ν u₂.velocity u₂.pressure s y := rfl)
      (fun y => (u₁.initial y).trans (u₂.initial y).symm)
  exact huniq t ⟨ht.1, htT'.le⟩ x

/-- **Spec field `UniquenessAPI.velocity_unique`** (`research/A02/Spec.lean:267-272`),
verbatim. -/
theorem velocity_unique :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
          (u₂ : ClassicalSolutionR ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x) :=
  fun _ _ _ hν _ _ _ _ u₁ u₂ => velocity_unique_core hν u₁ u₂

/-! ## 2. Unit U3: the pressure gauge -/

/-- **Core of U3.**  The two pressures are gauge-equivalent on the common
half-open interval. -/
theorem pressure_gauge_core {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} (hν : 0 < ν)
    {T₁ T₂ : ℝ} (u₁ : ClassicalSolutionR ν a f T₁) (u₂ : ClassicalSolutionR ν a f T₂) :
    PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure := by
  have hm : (0 : ℝ) < min T₁ T₂ := lt_min u₁.horizon_pos u₂.horizon_pos
  have hvel := velocity_unique_core hν u₁ u₂
  have hvelOn : ∀ z ∈ Ico (0 : ℝ) (min T₁ T₂) ×ˢ (univ : Set Space),
      u₁.velocity z = u₂.velocity z := fun z hz => hvel z.1 hz.1 z.2
  -- Interior constancy of the pressure difference in space.
  have hInterior : ∀ t ∈ Ioo (0 : ℝ) (min T₁ T₂), ∀ x,
      u₂.pressure (t, x) - u₁.pressure (t, x)
        = u₂.pressure (t, 0) - u₁.pressure (t, 0) := by
    intro t ht x
    have ht₁ : t ∈ Ioo (0 : ℝ) T₁ := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have ht₂ : t ∈ Ioo (0 : ℝ) T₂ := ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
    have htIco : t ∈ Ico (0 : ℝ) (min T₁ T₂) := ⟨ht.1.le, ht.2⟩
    have hsd : spatialDerivative u₁.velocity t = spatialDerivative u₂.velocity t :=
      spatialDerivative_eq_of_eqOn hvelOn htIco
    -- equal pressure gradients at every point, from momentum + equal velocities
    have hpg : ∀ y, pressureGradient u₁.pressure t y = pressureGradient u₂.pressure t y := by
      intro y
      have hval : u₁.velocity (t, y) = u₂.velocity (t, y) := hvel t htIco y
      have hadv : advection u₁.velocity t y = advection u₂.velocity t y := by
        simp only [advection, hsd, hval]
      have hlap : spatialLaplacian u₁.velocity t y = spatialLaplacian u₂.velocity t y := by
        simp only [spatialLaplacian, hsd]
      have htemp : temporalDerivative u₁.velocity t y = temporalDerivative u₂.velocity t y :=
        temporalDerivative_eq_of_eqOn hvelOn ht y
      have hres :
          NavierStokesR3.ProblemStatement.navierStokesResidual ν u₁.velocity u₁.pressure t y
            = NavierStokesR3.ProblemStatement.navierStokesResidual ν u₂.velocity u₂.pressure t y :=
        (u₁.momentum t ht₁ y).trans (u₂.momentum t ht₂ y).symm
      have expand₁ :
          NavierStokesR3.ProblemStatement.navierStokesResidual ν u₁.velocity u₁.pressure t y
            = temporalDerivative u₂.velocity t y + advection u₂.velocity t y
              - ν • spatialLaplacian u₂.velocity t y + pressureGradient u₁.pressure t y := by
        rw [show
              NavierStokesR3.ProblemStatement.navierStokesResidual ν u₁.velocity u₁.pressure t y
                = temporalDerivative u₁.velocity t y + advection u₁.velocity t y
                  - ν • spatialLaplacian u₁.velocity t y + pressureGradient u₁.pressure t y from rfl,
            htemp, hadv, hlap]
      have expand₂ :
          NavierStokesR3.ProblemStatement.navierStokesResidual ν u₂.velocity u₂.pressure t y
            = temporalDerivative u₂.velocity t y + advection u₂.velocity t y
              - ν • spatialLaplacian u₂.velocity t y + pressureGradient u₂.pressure t y := rfl
      rw [expand₁, expand₂] at hres
      exact add_left_cancel hres
    -- turn equal gradients into equal spatial Fréchet derivatives
    have hd₁ : ∀ y, DifferentiableAt ℝ (fun z : Space => u₁.pressure (t, z)) y :=
      fun y => pressure_slice_differentiableAt u₁.pressure_smooth ht₁ y
    have hd₂ : ∀ y, DifferentiableAt ℝ (fun z : Space => u₂.pressure (t, z)) y :=
      fun y => pressure_slice_differentiableAt u₂.pressure_smooth ht₂ y
    have hfd : ∀ y, fderiv ℝ (fun z : Space => u₁.pressure (t, z)) y
                  = fderiv ℝ (fun z : Space => u₂.pressure (t, z)) y := by
      intro y
      ext w
      rw [← NavierStokes.PeriodicUniqueness.inner_pressureGradient u₁.pressure t y w,
          ← NavierStokes.PeriodicUniqueness.inner_pressureGradient u₂.pressure t y w, hpg y]
    -- the difference has zero derivative everywhere, hence is constant
    have hgdiff : Differentiable ℝ (fun z : Space => u₂.pressure (t, z) - u₁.pressure (t, z)) :=
      fun y => (hd₂ y).sub (hd₁ y)
    have hgfd : ∀ y, fderiv ℝ (fun z : Space => u₂.pressure (t, z) - u₁.pressure (t, z)) y = 0 := by
      intro y
      rw [fderiv_fun_sub (hd₂ y) (hd₁ y), ← hfd y, sub_self]
    exact is_const_of_fderiv_eq_zero hgdiff hgfd x 0
  -- Endpoint `t = 0`: carry the constant across by continuity.
  have hEndpoint : ∀ x, u₂.pressure (0, x) - u₁.pressure (0, x)
      = u₂.pressure (0, 0) - u₁.pressure (0, 0) := by
    intro x
    set φ : ℝ → ℝ := fun s =>
      (u₂.pressure (s, x) - u₁.pressure (s, x)) - (u₂.pressure (s, 0) - u₁.pressure (s, 0))
      with hφ
    have hc : ContinuousOn φ (Ico (0 : ℝ) (min T₁ T₂)) := by
      have c1x := (pressure_time_continuousOn u₁.pressure_smooth x).mono
        (Ico_subset_Ico (le_refl (0 : ℝ)) (min_le_left T₁ T₂))
      have c2x := (pressure_time_continuousOn u₂.pressure_smooth x).mono
        (Ico_subset_Ico (le_refl (0 : ℝ)) (min_le_right T₁ T₂))
      have c10 := (pressure_time_continuousOn u₁.pressure_smooth 0).mono
        (Ico_subset_Ico (le_refl (0 : ℝ)) (min_le_left T₁ T₂))
      have c20 := (pressure_time_continuousOn u₂.pressure_smooth 0).mono
        (Ico_subset_Ico (le_refl (0 : ℝ)) (min_le_right T₁ T₂))
      exact (c2x.sub c1x).sub (c20.sub c10)
    have hzero_on : ∀ s ∈ Ioo (0 : ℝ) (min T₁ T₂), φ s = 0 := by
      intro s hs
      have hI := hInterior s hs x
      simp only [hφ]
      linarith
    have hclosure : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) (min T₁ T₂)) := by
      rw [closure_Ioo (ne_of_lt hm)]; exact ⟨le_rfl, hm.le⟩
    have hneBot : (𝓝[Ioo (0 : ℝ) (min T₁ T₂)] (0 : ℝ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hclosure
    have hcwa : ContinuousWithinAt φ (Ioo (0 : ℝ) (min T₁ T₂)) 0 :=
      (hc.continuousWithinAt ⟨le_rfl, hm⟩).mono Ioo_subset_Ico_self
    have hev : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝[Ioo (0 : ℝ) (min T₁ T₂)] 0] φ :=
      eventually_nhdsWithin_of_forall (fun s hs => (hzero_on s hs).symm)
    have htend0 : Tendsto φ (𝓝[Ioo (0 : ℝ) (min T₁ T₂)] 0) (𝓝 (0 : ℝ)) :=
      Tendsto.congr' hev tendsto_const_nhds
    have hφ0 : φ 0 = 0 := tendsto_nhds_unique hcwa htend0
    simp only [hφ] at hφ0
    linarith
  -- Assemble the gauge with `c t = u₂.pressure (t,0) - u₁.pressure (t,0)`.
  refine ⟨fun s => u₂.pressure (s, 0) - u₁.pressure (s, 0), fun t ht x => ?_⟩
  have hkey : u₂.pressure (t, x) - u₁.pressure (t, x)
      = u₂.pressure (t, 0) - u₁.pressure (t, 0) := by
    rcases ht.1.lt_or_eq with hpos | h0
    · exact hInterior t ⟨hpos, ht.2⟩ x
    · rw [← h0]; exact hEndpoint x
  show u₂.pressure (t, x) = u₁.pressure (t, x) + (u₂.pressure (t, 0) - u₁.pressure (t, 0))
  linarith [hkey]

/-- **Spec field `UniquenessAPI.pressure_gauge`** (`research/A02/Spec.lean:277-281`),
verbatim. -/
theorem pressure_gauge :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
          (u₂ : ClassicalSolutionR ν a f T₂),
          PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) u₁.pressure u₂.pressure :=
  fun _ _ _ hν _ _ _ _ u₁ u₂ => pressure_gauge_core hν u₁ u₂

end NSFormalization.Section4.A02
