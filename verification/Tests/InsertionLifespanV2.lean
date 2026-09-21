import Contracts.V2.InsertionLifespan
import Bindings.InsertionFromData
import TestSupport.Axioms

/-! Exact-type and transitive-axiom tests for the current insertion, lifespan, maximality and blowup conclusions. -/

noncomputable section
namespace BlowupDensity.Tests

open Set

/-- Full Theorem 4.2: the building block is selected before the reference and
region, and every conclusion concerns one family and the given reference. -/
theorem checkedInsertionLifespanV2 :
    Contracts.V2.InsertionLifespan.wholeSpaceInsertionStatement :=
  Bindings.wholeSpaceInsertion_holds

run_cmd TestSupport.checkAxioms ``checkedInsertionLifespanV2

/-! ## The three new manuscript exports, by hand from the record -/

/-- `04-whole-space.tex:32,53`: for every `ε ∈ (0, ε₀]` the inserted pair is a
full-horizon `Data.ClassicalSolutionR ν a g_ε T` with velocity `family.velocity ε`
and pressure `family.pressure ε`. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.family.ε₀) :
    ∃ w : Contracts.V1.Data.ClassicalSolutionR ν A.family.a (A.family.force ε) A.family.T,
      w.velocity = A.family.velocity ε ∧ w.pressure = A.family.pressure ε :=
  A.solution ε hε

/-- `04-whole-space.tex:53`: for every `ε ∈ (0, ε₀]` the inserted pair `(u_ε, p_ε)`
is the maximal classical solution of `(ν, a, g_ε)`. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.family.ε₀) :
    Contracts.V2.MaximalPartial.IsMaximalSolution ν A.family.a (A.family.force ε)
      (A.family.velocity ε) (A.family.pressure ε) :=
  A.maximal ε hε

/-- The second display of Theorem 4.2, `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞`
(`04-whole-space.tex:35`), for every `ε ∈ (0, ε₀]`, in the frozen
`Contracts.V1.MaximalPartial` `limsupLeft`/`speedENorm` vocabulary. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.family.ε₀) :
    Contracts.V1.MaximalPartial.limsupLeft A.family.T
        (fun t => Contracts.V1.MaximalPartial.speedENorm
          (fun x : Contracts.V1.Space => A.family.velocity ε (t, x))) = ⊤ :=
  A.blowup_limsup ε hε

/-! ## Version one is recoverable, and its two clauses stay accessible -/

/-- The inherited first lifespan display `T + delta < T^ν_{max,R}(a, g)`
(`04-whole-space.tex:32`) stays accessible on the version-two record. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P) :
    ENNReal.ofReal (A.family.T + A.family.margin) <
      Contracts.V1.Data.maximalLifespanR ν A.family.a A.family.g :=
  A.referenceLifespan

/-- The inherited second lifespan display `T^ν_{max,R}(a, g_ε) = T`
(`04-whole-space.tex:34`) stays accessible on the version-two record. -/
example (ν : ℝ) (P : Contracts.V1.PacketAPI ν)
    (A : Contracts.V2.InsertionLifespan.InsertionLifespanV2API ν P)
    (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.family.ε₀) :
    Contracts.V1.Data.maximalLifespanR ν A.family.a (A.family.force ε) =
      ENNReal.ofReal A.family.T :=
  A.lifespan ε hε

end BlowupDensity.Tests
