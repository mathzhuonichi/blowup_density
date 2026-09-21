import Contracts.V3.LocalForceTheory
import Bindings.LocalForceTheory
import TestSupport.Axioms

namespace BlowupDensity.Tests
open Set
open NavierStokes.ProblemStatement
open Contracts.V1.Data Contracts.V3.LocalForceTheory
open scoped ContDiff

theorem checkedLocalForceTheory : Contracts.V3.LocalForceTheory.LocalForceTheoryAPI :=
  Bindings.LocalForceTheory.localForceTheory

run_cmd TestSupport.checkAxioms ``checkedLocalForceTheory

/-- A permanent periodic force is admitted even if its irrelevant negative
time values have a jump at zero. No temporal support or global extension of
the original function is required. -/
example (c : Space) : SmoothForceT (fun z => if 0 ≤ z.1 then c else 0) := by
  intro S _
  refine ⟨fun _ => c, contDiff_const, fun _ _ _ _ => rfl, ?_⟩
  intro t ht x
  simp only [ite_eq_left ht.1]

/-- Time-independent smooth Sobolev forcing is admitted without assuming
that its half-line time integrals are finite. -/
example (a : SpatialField) (ha : MemHInfty a) : SmoothForceR (fun z => a z.2) := by
  refine ⟨(ha.1.comp contDiff_snd).contDiffOn, ?_⟩
  intro m
  obtain ⟨A, hA⟩ := ha.2 m
  exact ⟨fun _ => A, fun _ _ => hA, contDiff_const.contDiffOn⟩

end BlowupDensity.Tests
