import NSFormalization.Paper1.PeriodicUniqueness
import NSFormalization.Source.LocalApproximatingInsertion

/-! Actual periodic classical solution horizons and their supremum. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace NSFormalization.Paper1.PeriodicLifespan
open NavierStokes NavierStokes.ProblemStatement

/-- An actual periodic smooth solution; no continuation conclusion is assumed. -/
structure Flow (ν : ℝ) (a : Space → Space) (f : VelocityField) (S : ℝ) where
  velocity : VelocityField
  pressure : PressureField
  horizon_pos : 0 < S
  velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ univ)
  pressure_smooth : ContDiffOn ℝ ∞ pressure (Ico (0 : ℝ) S ×ˢ univ)
  velocity_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) velocity
  pressure_periodic : UnitSpatialPeriodsOn (Ico (0 : ℝ) S) pressure
  initial : ∀ x, velocity (0, x) = a x
  divergence : ∀ t ∈ Ico (0 : ℝ) S, ∀ x, spatialDivergence velocity t x = 0
  equation : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
    Source.residual ν velocity pressure t x = f (t, x)

/-- Supremum of horizons for which the displayed actual flow exists. The
empty supremum is zero. This is not a chosen maximal solution. -/
def lifespan (ν : ℝ) (a : Space → Space) (f : VelocityField) : ℝ≥0∞ :=
  ⨆ S : ℝ, ⨆ (_ : Nonempty (Flow ν a f S)), ENNReal.ofReal S

theorem horizon_le_lifespan {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (U : Flow ν a f S) : ENNReal.ofReal S ≤ lifespan ν a f :=
  le_iSup_of_le S (le_iSup_of_le ⟨U⟩ le_rfl)

theorem lifespan_le_iff {ν T : ℝ} (hT : 0 ≤ T) (a : Space → Space)
    (f : VelocityField) :
    lifespan ν a f ≤ ENNReal.ofReal T ↔ ∀ S, Nonempty (Flow ν a f S) → S ≤ T := by
  constructor
  · intro h S hS
    exact (ENNReal.ofReal_le_ofReal_iff hT).mp
      ((horizon_le_lifespan hS.some).trans h)
  · intro h
    exact iSup_le (fun S => iSup_le (fun hS => ENNReal.ofReal_le_ofReal (h S hS)))

theorem lifespan_le_iff_no_extension {ν T : ℝ} (hT : 0 ≤ T)
    (a : Space → Space) (f : VelocityField) :
    lifespan ν a f ≤ ENNReal.ofReal T ↔ ∀ S, T < S → IsEmpty (Flow ν a f S) := by
  rw [lifespan_le_iff hT]
  constructor
  · intro h S hTS
    exact ⟨fun U => (not_lt_of_ge (h S ⟨U⟩)) hTS⟩
  · intro h S hS
    by_contra hST
    exact (h S (lt_of_not_ge hST)).false hS.some

/-- The elementary two-case alternative uses actual solution witnesses. -/
theorem bad_or_regular_reference {ν T : ℝ} (hT : 0 ≤ T)
    (a : Space → Space) (f : VelocityField) :
    lifespan ν a f ≤ ENNReal.ofReal T ∨ ∃ S, T < S ∧ Nonempty (Flow ν a f S) := by
  by_cases h : lifespan ν a f ≤ ENNReal.ofReal T
  · exact Or.inl h
  · right
    have hn : ¬ ∀ S, Nonempty (Flow ν a f S) → S ≤ T := by
      simpa only [← lifespan_le_iff hT] using h
    push Not at hn
    obtain ⟨S, hS, hTS⟩ := hn
    exact ⟨S, hTS, hS⟩

theorem insertion_lifespan_le {ν r T τ : ℝ} (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτT : τ < T) {a : Space → Space} {v g U F : VelocityField} {q P : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (ha : ∀ x, v (0,x) = a x) :
    lifespan ν a (fun z => g z + F z) ≤ ENNReal.ofReal T := by
  apply (lifespan_le_iff_no_extension (hτ.trans_lt hτT).le a _).mpr
  intro S hTS
  refine ⟨fun W => ?_⟩
  exact PeriodicUniqueness.no_later_classical_solution hν hτ hTS h
    W.velocity_smooth W.pressure_smooth W.velocity_periodic W.pressure_periodic
    (fun t ht => W.divergence t ⟨ht.1.le,ht.2⟩) W.equation
    (fun x => (W.initial x).trans (ha x).symm)

/-- The actual inserted fields themselves furnish the endpoint horizon `T`.
The force is exactly the background force plus the constructed perturbation.
This construction uses the smoothness, PDE, incompressibility and preserved
history already proved by `PeriodicInsertion.Properties`; it does not invoke
an arbitrary-data local existence theorem. -/
def insertionFlow {ν r T τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T)
    {a : Space → Space} {v g U F : VelocityField} {q P : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (ha : ∀ x, v (0, x) = a x) :
    Flow ν a (fun z => g z + F z) T where
  velocity := U
  pressure := P
  horizon_pos := hτ.trans_lt hτT
  velocity_smooth := h.velocity_smooth
  pressure_smooth := h.pressure_smooth
  velocity_periodic := h.velocity_periodic
  pressure_periodic := h.pressure_periodic
  initial := fun x => ((h.history 0 hτ x).1).trans (ha x)
  divergence := h.divergence_free
  equation := h.equation

/-- The same inserted velocity and pressure attain horizon `T`, while the
proved periodic uniqueness and local blowup rule out every later horizon.
Consequently the supremum of actual periodic flow horizons is exactly `T`.
No assertion about a separately chosen maximal-solution object is made. -/
theorem insertion_lifespan_eq {ν r T τ : ℝ} (hν : 0 < ν) (hτ : 0 ≤ τ)
    (hτT : τ < T) {a : Space → Space} {v g U F : VelocityField} {q P : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P)
    (ha : ∀ x, v (0, x) = a x) :
    lifespan ν a (fun z => g z + F z) = ENNReal.ofReal T := by
  apply le_antisymm (insertion_lifespan_le hν hτ hτT h ha)
  exact horizon_le_lifespan (insertionFlow hτ hτT h ha)


/-- Every actual reference extending past T admits the fixed-profile periodic
insertion family. Each family member has lifespan exactly T. -/
theorem exists_periodic_insertion_family {ν T τ r S : ℝ}
    (hν : 0 < ν) (hτ : 0 ≤ τ) (hτT : τ < T) (hr : 0 < r) (hrhalf : r < 1/2)
    {a : Space → Space} {g : VelocityField} (W : Flow ν a g S) (hTS : T < S) :
    ∃ vhat u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField,
    ∃ K : Set Space, ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      ContDiff ℝ ∞ vhat ∧
      NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ 0 < ε₀ ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        let V := Source.LocalReferenceInsertion.velocityOn u W.velocity vhat 0 T θ η ε
        let Q := Source.InsertionFamily.pressure p W.pressure 0 T ε
        let G := Source.InsertionFamily.force ν f vhat 0 T θ η ε
        PeriodicInsertion.Properties ν r T τ W.velocity W.pressure g
          (PeriodicInsertion.velocity T W.velocity V) (PeriodicInsertion.force G)
          (PeriodicInsertion.pressure T W.pressure Q) ∧
        lifespan ν a (fun z => g z + PeriodicInsertion.force G z) = ENNReal.ofReal T := by
  have heq : T + (S-T) = S := by ring
  obtain ⟨vhat,u,p,f,K,θ,η,ε₀,hvhat,_,hc,_,hθ,hη,hθc,hηc,hε₀,hfamily⟩ :=
    Source.LocalReferenceInsertion.exists_local_reference_insertion_family hν (sub_pos.mpr hTS)
      (by simpa only [heq] using W.velocity_smooth)
      (by simpa only [heq] using W.pressure_smooth)
      (by simpa only [heq] using W.divergence) hτ hτT
      (fun t ht => W.equation t ⟨ht.1,ht.2.trans hTS⟩) (0 : Space) hr
  refine ⟨vhat,u,p,f,K,θ,η,ε₀,hvhat,hc,hθ,hη,hθc,hηc,hε₀,?_⟩
  intro ε hε
  have hsub : Ico (0 : ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0 : ℝ) S ×ˢ univ :=
    fun z hz => ⟨⟨hz.1.1,hz.1.2.trans hTS⟩,hz.2⟩
  have hh := PeriodicInsertion.of_insertion hτ hτT hrhalf
    (W.velocity_smooth.mono hsub) (W.pressure_smooth.mono hsub)
    (fun t ht => W.velocity_periodic t ⟨ht.1,ht.2.trans hTS⟩)
    (fun t ht => W.pressure_periodic t ⟨ht.1,ht.2.trans hTS⟩)
    (fun t ht => W.equation t ⟨ht.1,ht.2.trans hTS⟩) (hfamily ε hε)
  exact ⟨hh,insertion_lifespan_eq hν hτ hτT hh W.initial⟩

end NSFormalization.Paper1.PeriodicLifespan
