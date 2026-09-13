import Contracts.V1.InsertionLifespan
import Bindings.InsertionLifespan
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked,
and each of the two manuscript displays is written out by hand from the record
so a later edit cannot silently weaken it. -/

noncomputable section
namespace BlowupDensity.Tests

open Set

/-- An implementation must supply the two lifespan clauses of Theorem 4.2
(`paper/sections/04-whole-space.tex:32,34`) for the given inserted family under
the manuscript's `g ∈ F_R` and regular-through-`T+delta` hypotheses.  The final
`rfl` (lane-092 review finding 5) pins `A.family = F`, so the clauses are about
the **given** family, not a substituted one. -/
theorem checkedInsertionLifespan :
    Contracts.V1.InsertionLifespan.insertionLifespanStatement :=
  fun _ν _P F hg hreg =>
    ⟨Bindings.InsertionLifespan.insertionLifespanAPI F hg hreg, rfl⟩

run_cmd TestSupport.checkAxioms ``checkedInsertionLifespan

/-! ## The two manuscript displays, by hand from the record -/

/-- `T + delta < T^nu_{max,R}(a, g)`, the definite article of "*the* solution ...
regular through `T + delta`" (`paper/sections/04-whole-space.tex:32`). -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P) :
    ENNReal.ofReal (A.family.T + A.family.margin) <
      Contracts.V1.Data.maximalLifespanR ν A.family.a A.family.g :=
  A.referenceLifespan

/-- `T^nu_{max,R}(a, g_eps) = T` for every `eps ∈ (0, eps0]`, the first display
of `paper/sections/04-whole-space.tex:34`. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.family.ε₀) :
    Contracts.V1.Data.maximalLifespanR ν A.family.a (A.family.force ε) =
      ENNReal.ofReal A.family.T :=
  A.lifespan ε hε

/-! ## The two derived hypotheses stay derivable (lane-092 findings 1, 2):
`0 < ν` and `a ∈ X_R` are determined by the ambient contracts, not carried. -/

/-- `0 < ν` is a field of the packet, not a hypothesis. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν) : 0 < ν := P.viscosity_pos

/-- `a ∈ X_R` is derived from the reference solution, not a hypothesis. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P) :
    A.family.a ∈ Contracts.V1.Data.initialClassR :=
  Bindings.InsertionLifespan.initialClassR_a A.family

end BlowupDensity.Tests
