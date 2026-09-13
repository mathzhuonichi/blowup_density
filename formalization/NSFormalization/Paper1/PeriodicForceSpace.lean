import NSFormalization.Paper1.PeriodicLifespan

/-!
# The smooth periodic force class in Paper 1

The spatially periodic lift is smooth on all of spacetime. Its time support
lies in a compact subset of `(0, infinity)`, exactly as required by the paper's
force class. Compact spatial support of a periodic lift is neither assumed nor
claimed. The insertion theorem below keeps every total force in this class and
uses the proved supremum of actual flow horizons as its lifespan notion.
-/
noncomputable section
open Set
open scoped ContDiff

namespace NSFormalization.Paper1.PeriodicForceSpace
open NavierStokes.ProblemStatement PeriodicLifespan

/-- The lifted version of `C_c^infinity(T^3 × (0,infinity); R^3)`.
Only the temporal support is required to be compact in the Euclidean lift. -/
structure IsTestForce (f : VelocityField) : Prop where
  smooth : ContDiff ℝ ∞ f
  periodic : UnitSpatialPeriodsOn univ f
  time_support : ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioi 0 ∧ tsupport f ⊆ K ×ˢ univ

/-- The actual smooth forcing space, before a particular norm topology is chosen. -/
abbrev TestForce := {f : VelocityField // IsTestForce f}

theorem isTestForce_zero : IsTestForce (0 : VelocityField) := by
  refine ⟨contDiff_const, fun _ _ _ _ => rfl, ∅, isCompact_empty, empty_subset _, ?_⟩
  simp

theorem IsTestForce.add {f g : VelocityField} (hf : IsTestForce f) (hg : IsTestForce g) :
    IsTestForce (f + g) := by
  obtain ⟨K, hK, hKpos, hKf⟩ := hf.time_support
  obtain ⟨L, hL, hLpos, hLg⟩ := hg.time_support
  refine ⟨hf.smooth.add hg.smooth, ?_, K ∪ L, hK.union hL, ?_, ?_⟩
  · intro t ht x i
    exact congrArg₂ (· + ·) (hf.periodic t ht x i) (hg.periodic t ht x i)
  · exact union_subset hKpos hLpos
  · intro z hz
    have hsupport := tsupport_binop_subset (fun a b : Space => a + b) (by simp) f g hz
    exact hsupport.elim (fun h => ⟨Or.inl (hKf h).1, mem_univ _⟩)
      (fun h => ⟨Or.inr (hLg h).1, mem_univ _⟩)

/-- A common upper endpoint for the zero time slices also bounds their closed
topological support. No boundedness of the spatial lift is used. -/
theorem tsupport_time_le {f : VelocityField} {B : ℝ}
    (hB : ∀ t : ℝ, B ≤ t → ∀ x : Space, f (t, x) = 0) :
    tsupport f ⊆ Prod.fst ⁻¹' Iic B := by
  apply closure_minimal _ (isClosed_Iic.preimage continuous_fst)
  intro z hz
  by_contra hn
  exact hz (hB z.1 (lt_of_not_ge hn).le z.2)

/-- The actual perturbation has compact positive time support whenever the
preserved history includes a strictly positive time. -/
theorem testForce_of_insertion {ν r T τ : ℝ} (hτ : 0 < τ)
    {v g U F : VelocityField} {q P : PressureField}
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P) : IsTestForce F := by
  obtain ⟨B, _, hB⟩ := h.force_future_support
  refine ⟨h.force_smooth, h.force_periodic, Icc τ B, isCompact_Icc, ?_, ?_⟩
  · intro t ht
    exact hτ.trans_le ht.1
  · intro z hz
    exact ⟨⟨(h.force_supported_after hz).1.le, tsupport_time_le hB hz⟩, mem_univ _⟩

/-- The background force plus the actual inserted perturbation remains in the
same force class as the reference. -/
theorem totalForce_of_insertion {ν r T τ : ℝ} (hτ : 0 < τ)
    {v g U F : VelocityField} {q P : PressureField}
    (hg : IsTestForce g)
    (h : PeriodicInsertion.Properties ν r T τ v q g U F P) :
    IsTestForce (fun z => g z + F z) :=
  hg.add (testForce_of_insertion hτ h)

/-- A regular reference yields actual periodic singular forces in Paper 1's
smooth positive-time force class, all with the same initial velocity and
exact deadline. The scale and the compact original perturbation are retained
explicitly, so quantitative periodization estimates can be attached to these
same fields rather than to an unrelated existence witness. -/
theorem exists_testForce_insertion_family {ν T τ r S : ℝ}
    (hν : 0 < ν) (hτ : 0 < τ) (hτT : τ < T) (hr : 0 < r) (hrhalf : r < 1/2)
    {a : Space → Space} {g : VelocityField} (hg : IsTestForce g)
    (W : Flow ν a g S) (hTS : T < S) :
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
        IsTestForce (fun z => g z + PeriodicInsertion.force G z) ∧
        lifespan ν a (fun z => g z + PeriodicInsertion.force G z) = ENNReal.ofReal T := by
  obtain ⟨vhat, u, p, f, K, θ, η, ε₀, hvhat, hc, hθ, hη, hθc, hηc, hε₀, hfamily⟩ :=
    exists_periodic_insertion_family hν hτ.le hτT hr hrhalf W hTS
  refine ⟨vhat, u, p, f, K, θ, η, ε₀, hvhat, hc, hθ, hη, hθc, hηc, hε₀, ?_⟩
  intro ε hε
  obtain ⟨hp, hLife⟩ := hfamily ε hε
  exact ⟨hp, totalForce_of_insertion hτ hg hp, hLife⟩

end NSFormalization.Paper1.PeriodicForceSpace
