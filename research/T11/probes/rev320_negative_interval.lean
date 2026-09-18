import NSFormalization.Section3.T11.ClassicalAssembly

noncomputable section
namespace NSFormalization.Section3.T11
open Set
open NSFormalization.Section3.T10

/- Reviewer negative probe: widening the endpoint interval from Ico to Ioo
   must not be discharged by the delivered Sobolev theorem. -/
example {T : ℝ} {u : ℝ → PeriodicSobolev 3} (h : PersistenceInput T u) :
    ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
      ContinuousOn G (Ioo (0 : ℝ) T) ∧
        ∀ t ∈ Ioo (0 : ℝ) T,
          IsPeriodicDatum (m : ℝ) (fun x ↦ torusPhysicalVelocity u (t, x)) (G t) := by
  exact persistence_physical_sobolev h

end NSFormalization.Section3.T11
