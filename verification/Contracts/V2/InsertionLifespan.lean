import Contracts.V1.InsertionLifespan
import Contracts.V2.MaximalPartial

/-! Whole-space gluing in a prescribed region.

`InsertionLifespanV2API` extends the proved family record with a classical
solution on the full horizon, maximality and essential-supremum blowup.
`wholeSpaceInsertionStatement` is the public raw-data statement: all analytic
construction records are outputs, and the given reference fields and region
are retained in every conclusion. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.InsertionLifespan

open Set
open BlowupDensity.Contracts.V1
open scoped ENNReal Topology

/-- **The two lifespan clauses of Theorem 4.2, version 2.**  Version one's
`InsertionLifespanAPI` (the inherited `family`, the two manuscript hypotheses
`memForce`/`regular`, and the two lifespan clauses `referenceLifespan`/`lifespan`),
together with the three exports the version-one review named as owed
(`research/R42/REVIEW_CONTRACT.md:443-452`): the inserted pair as a full-horizon
classical solution, its identification as the maximal solution, and the
essential-supremum form of the blow-up.

Every field of `Contracts.V1.InsertionLifespan.InsertionLifespanAPI` is inherited
verbatim through `toInsertionLifespanAPI`; see `Contracts/V1/InsertionLifespan.lean`
for their docstrings and manuscript citations.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure InsertionLifespanV2API (ν : ℝ) (P : PacketAPI ν) extends
    Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P where
  /-- "there are `g_ε ∈ F_R` and **a solution** `u_ε`" (`04-whole-space.tex:32`),
  and "Proposition~\ref{prop:local} identifies **the solution**"
  (`04-whole-space.tex:53`): for every `ε ∈ (0, ε₀]` the inserted pair
  `(u_ε, p_ε)` is a `Data.ClassicalSolutionR ν a g_ε T` on the **full** horizon
  `[0,T)` — one velocity `family.velocity ε`, one pressure `family.pressure ε`,
  one `sobolev` path continuous on all of `[0,T)`, and `∇p_ε ∈ L²` at every
  `t < T`.  This is the object `R42.insertion_lifespan` did not export
  (`research/R42/REVIEW_CONTRACT.md:386-387,450-452`), from which a consumer
  recovers `sobolev`/`pressure_gradient` for `u_ε`.  Discharged by
  `Bindings.InsertionLifespan.sol_fullHorizon` (lane 098). -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    ∃ w : Data.ClassicalSolutionR ν family.a (family.force ε) family.T,
      w.velocity = family.velocity ε ∧ w.pressure = family.pressure ε
  /-- "Proposition~\ref{prop:local} identifies the solution with the unique
  maximal solution" (`04-whole-space.tex:53`; `research/section4/STATEMENTS.md:346`):
  for every `ε ∈ (0, ε₀]` the inserted pair `(u_ε, p_ε)` **is** the maximal
  classical solution of `(ν, a, g_ε)`, stated in the registered
  `Contracts.V2.MaximalPartial.IsMaximalSolution` vocabulary (contract
  `A02.maximal_partial_v2`).  Not asserted by `R42.insertion_lifespan`, which gives
  only the lifespan number (`research/R42/REVIEW_CONTRACT.md:447-449`).  Discharged
  by `Bindings.InsertionLifespan.isMaximalSolution_of_inserted` (lane 098). -/
  maximal : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Contracts.V2.MaximalPartial.IsMaximalSolution ν family.a (family.force ε)
      (family.velocity ε) (family.pressure ε)
  /-- The **second display** of Theorem 4.2, `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞`
  (`04-whole-space.tex:35`; `research/section4/STATEMENTS.md:348`), for every
  `ε ∈ (0, ε₀]`, in the frozen `Contracts.V1.MaximalPartial` vocabulary
  (`limsupLeft`/`speedENorm` = `⟪D01:limsupLeft⟫`/`⟪D01:normLinfty⟫`,
  `Contracts/V1/MaximalPartial.lean:101,106`).  `R42.insertion_lifespan` registers
  the blow-up only in the pointwise `SpeedUnboundedAt` form
  (`research/R42/REVIEW_CONTRACT.md:443-446`); this field states the displayed
  essential-supremum form, the one the binding proves inside `lifespan_upper`
  (`Bindings/InsertionLifespan.lean:215-217`) through
  `limsupLeft_speedENorm_eq_top`.  The spatial slice is `fun x => family.velocity ε
  (t, x)` because `family.velocity` is spacetime-valued (see the module docstring's
  fidelity note). -/
  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Contracts.V1.MaximalPartial.limsupLeft family.T
        (fun t => Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => family.velocity ε (t, x))) = ⊤

/-- The complete Theorem 4.2, strengthened to any prescribed nonempty open
set. One building block is selected for each viscosity before the reference
solution and region are quantified. All conclusions use one inserted family,
with its velocity and pressure pinned to the given reference fields. -/
def wholeSpaceInsertionStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ P : PacketAPI ν,
    ∀ T δ : ℝ, 0 < T → 0 < δ →
    ∀ a : Data.SpatialField, a ∈ Data.initialClassR →
    ∀ g : Data.SpaceTimeField, Data.MemForceR g →
    ∀ R : Data.ClassicalSolutionR ν a g (T + δ),
    ∀ B : Set Space, IsOpen B → B.Nonempty →
    ∃ L : InsertionLifespanV2API ν P,
      L.family.a = a ∧ L.family.g = g ∧ L.family.T = T ∧
      L.family.v = R.velocity ∧ L.family.π = R.pressure ∧ L.family.ball ⊆ B ∧
      (∀ ε ∈ Ioc (0 : ℝ) L.family.ε₀,
        Data.MemForceR (L.family.force ε) ∧
        Data.maximalLifespanR ν a (L.family.force ε) = ENNReal.ofReal T ∧
        Contracts.V1.MaximalPartial.limsupLeft T
          (fun t => Contracts.V1.MaximalPartial.speedENorm
            (fun x : Space => L.family.velocity ε (t, x))) = ⊤ ∧
        (∃ U : Data.ClassicalSolutionR ν a (L.family.force ε) T,
          U.velocity = L.family.velocity ε ∧ U.pressure = L.family.pressure ε) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ T - 2 * ε ^ 2 → ∀ x : Space,
          L.family.velocity ε (t, x) = R.velocity (t, x)) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          tsupport (fun x : Space => L.family.velocity ε (t, x) - R.velocity (t, x)) ⊆ B) ∧
        Data.MemForceCompact (fun z => L.family.force ε z - g z) ∧
        (∀ z ∈ tsupport (fun z => L.family.force ε z - g z), z.2 ∈ B) ∧
        Data.energyENorm T (fun z => L.family.velocity ε z - R.velocity z) ≤
          ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
            L.family.scaling.correctionEnergyConst * ε ^ ((3 : ℝ) / 2))) ∧
      (∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < 2 / q.toReal - 3 / 2 →
        Filter.Tendsto (fun ε : ℝ => Data.forceSobolevENorm q s
          (fun z => L.family.force ε z - g z)) (𝓝[>] 0) (𝓝 0))

end BlowupDensity.Contracts.V2.InsertionLifespan
