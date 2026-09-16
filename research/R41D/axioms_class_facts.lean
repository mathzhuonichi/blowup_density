import NSFormalization.Section4.R41.ClassFacts
import Contracts.V1.Data

/-!
Axiom and vocabulary audit for R41D gaps G2--G5.  The equality theorems below
are deliberately `rfl`: the formalization-side restatements are literally the
V1 contract definitions, rather than merely propositionally equivalent copies.
-/

noncomputable section

open scoped ENNReal

namespace ClassFactsConformance

open Set
open NSFormalization.Section4
open BlowupDensity.Contracts.V1

theorem memForceRapid_eq : R41.MemForceRapid = Data.MemForceRapid := rfl
theorem forceClassRapid_eq : R41.forceClassRapid = Data.forceClassRapid := rfl
theorem initialClassSchwartz_eq : R41.initialClassSchwartz = Data.initialClassSchwartz := rfl
theorem memForceR_eq : D01.MemForceR = Data.MemForceR := rfl
theorem forceClassR_eq : R41.forceClassR = Data.forceClassR := rfl
theorem memForceCompact_eq : D01.MemForceCompact = Data.MemForceCompact := rfl
theorem forceSobolevENorm_eq : D01.forceSobolevENorm = Data.forceSobolevENorm := rfl

/-- G2 in the registered contract vocabulary. -/
theorem contract_memForceR_of_memForceRapid {f : Data.SpaceTimeField}
    (hf : Data.MemForceRapid f) : Data.MemForceR f := by
  rw [← memForceRapid_eq] at hf
  rw [← memForceR_eq]
  exact R41.memForceR_of_memForceRapid hf

/-- Set-level G2 in the registered contract vocabulary. -/
theorem contract_forceClassRapid_subset_forceClassR :
    Data.forceClassRapid ⊆ Data.forceClassR := by
  rw [← forceClassRapid_eq, ← forceClassR_eq]
  exact R41.forceClassRapid_subset_forceClassR

/-- G3 in the registered contract vocabulary. -/
theorem contract_memForceRapid_of_compact_difference (g f : Data.SpaceTimeField)
    (hg : Data.MemForceRapid g)
    (hfg : Data.MemForceCompact (fun z => f z - g z)) : Data.MemForceRapid f := by
  rw [← memForceRapid_eq] at hg ⊢
  rw [← memForceCompact_eq] at hfg
  exact R41.memForceRapid_of_compact_difference g f hg hfg

/-- G4 in the registered contract vocabulary. -/
theorem contract_initialClassSchwartz_subset_initialClassR :
    Data.initialClassSchwartz ⊆ Data.initialClassR := by
  rw [← initialClassSchwartz_eq]
  exact R41.initialClassSchwartz_subset_initialClassR

/-- Strengthened G5 in the registered contract vocabulary. -/
theorem contract_forceSobolevENorm_zero (q : ℝ≥0∞) (s : ℝ) :
    Data.forceSobolevENorm q s (0 : Data.SpaceTimeField) = 0 := by
  rw [← forceSobolevENorm_eq]
  exact R41.forceSobolevENorm_zero q s

/-- The exact `q = 1 ∨ q = 2` G5 interface. -/
theorem contract_forceSobolevENorm_zero_of_one_or_two (q : ℝ≥0∞)
    (hq : q = 1 ∨ q = 2) (s : ℝ) :
    Data.forceSobolevENorm q s (0 : Data.SpaceTimeField) = 0 := by
  rw [← forceSobolevENorm_eq]
  exact R41.forceSobolevENorm_zero_of_one_or_two q hq s

/-- Pointwise algebra accompanying G5. -/
theorem contract_sub_self_force (g : Data.SpaceTimeField) :
    (fun z => g z - g z) = 0 :=
  R41.sub_self_force g

#print axioms R41.memForceR_of_memForceRapid
#print axioms R41.forceClassRapid_subset_forceClassR
#print axioms R41.memForceRapid_of_compact_difference
#print axioms R41.initialClassSchwartz_subset_initialClassR
#print axioms R41.forceSobolevENorm_zero
#print axioms R41.forceSobolevENorm_zero_of_one_or_two
#print axioms R41.sub_self_force

#print axioms contract_memForceR_of_memForceRapid
#print axioms contract_forceClassRapid_subset_forceClassR
#print axioms contract_memForceRapid_of_compact_difference
#print axioms contract_initialClassSchwartz_subset_initialClassR
#print axioms contract_forceSobolevENorm_zero
#print axioms contract_forceSobolevENorm_zero_of_one_or_two
#print axioms contract_sub_self_force

/-! Non-vacuity checks.  Zero is admitted by the task when no nonzero rapid
force is already registered; these examples instantiate the G2, G4 and G5 interfaces (G3 is exercised only through its zero compact-difference instance; see REVIEW_234). -/

example : Data.MemForceRapid (0 : Data.SpaceTimeField) := by
  rw [← memForceRapid_eq]
  refine ⟨contDiffOn_const, fun N k => ⟨0, fun t ht x => ?_⟩⟩
  simp

example : Data.MemForceR (0 : Data.SpaceTimeField) :=
  contract_memForceR_of_memForceRapid (by
    rw [← memForceRapid_eq]
    refine ⟨contDiffOn_const, fun N k => ⟨0, fun t ht x => ?_⟩⟩
    simp)

example : (0 : Data.SpatialField) ∈ Data.initialClassR := by
  apply contract_initialClassSchwartz_subset_initialClassR
  rw [← initialClassSchwartz_eq]
  refine ⟨⟨0, by simp⟩, ?_⟩
  intro x
  simp [NavierStokes.ProblemStatement.spatialDivergence,
    NavierStokes.ProblemStatement.spatialDerivative]

example : Data.forceSobolevENorm 1 0 (0 : Data.SpaceTimeField) = 0 :=
  contract_forceSobolevENorm_zero 1 0

end ClassFactsConformance
