import Contracts.V1.Data
import Contracts.V1.Uniqueness

/-! Stable specification for the **already-proved part of A02's maximal-solution
interface**, beyond the registered uniqueness half (`A02.uniqueness`,
`Contracts/V1/Uniqueness.lean`).

Task `collaboration/tasks/A02.md`, graph node `A02`
(`formalization/blueprint/DEPENDENCY_GRAPH.md`, `A02 ← A01`; consumers
`A02 → A04`, `A02 → C01`, `A02 → R42`).  `prop:local`
(`paper/sections/02-preliminaries.tex:105`) asserts local existence, uniqueness
and continuation; A01 owns existence, A04 the continuation criterion, and A02
owns the middle third.  `research/A02/Spec.lean` bundles the whole obligation as
`MaximalSolutionAPI`; the uniqueness clauses are registered as `A02.uniqueness`,
and this record fixes the **ten further fields already discharged** by the merged
proof modules `formalization/NSFormalization/Section4/A02/{Restrict,Order,Patch}.lean`
(lanes 032/041/…).

## What this record fixes (the ten proved fields), with the paper it comes from

* `restrict` (`Spec.lean:345-348`; `appendix-a-local-theory.tex:124`,
  "Patching these local solutions"): restriction to a shorter horizon.
* `pressure_normalization` (`Spec.lean:399-403`; `02-preliminaries.tex:31,96-100`):
  the canonical basepoint pressure gauge `p ↦ p − p(·,x₀)`.
* `horizon_le_lifespan` (`Spec.lean:372-375`; `research/A01/Spec.lean:371-372`):
  the local horizon is below the maximal lifespan — stated **with the A01
  `solution` clause as an explicit hypothesis**, exactly as `Order.lean` proves
  it (A01 will discharge that hypothesis; see the field docstring).
* `patch` (`Spec.lean:357-367`; `appendix-a-local-theory.tex:124-125`): two local
  solutions of one datum patch to a solution on the union of their intervals.
* `lifespan_le_iff`, `lifespan_le_iff_no_extension` (`Spec.lean:443-455`;
  `02-preliminaries.tex:42`, `04-whole-space.tex:53`): the two shapes in which
  `T^ν_{max,R}(a,f) ≤ T` is decided.
* `lifespan_ge_of_forall_shorter` (`Spec.lean:463-466`; `04-whole-space.tex:34,53`):
  a solution on every strictly shorter interval pushes the lifespan up to `T`.
* `regularThrough_iff` (`Spec.lean:476-478`; `02-preliminaries.tex:34-36`):
  "regular through `T`" ↔ `T` is strictly below the maximal lifespan.
* `referenceLifespan` (`Spec.lean:500-504`; `04-whole-space.tex:32`): a
  `RegularThrough` hypothesis upgraded to one margin `δ` carrying a solution on
  `[0,T+δ)`, a strictly longer realized horizon, and the strict lifespan
  inequality R42 declares.
* `lifespan_le_of_unbounded` (`Spec.lean:576-582`; `04-whole-space.tex:53`): if
  `(u,p)` is a classical solution on every `[0,S)`, `S < T`, and its `L^∞` speed
  blows up at `T`, then the lifespan is at most `T`.

The uniqueness half is **carried** as the field `uniqueness :
Contracts.V1.Uniqueness.UniquenessAPI`, so this record structurally includes the
already-registered contract (the way `InsertionFamilyAPI` carries `ScalingAPI`).

## Out of scope: the rest of `MaximalSolutionAPI`, each owed by a later lane

Not included, because not yet proved on this branch:

* the restated **A01 interface fields** `horizon`, `localSolution`,
  `horizonLowerBound` (`Spec.lean:316-332`) — A01's obligation;
* `exists_maximal`, `maximal_unique` (`Spec.lean:421-434`) and the
  `IsMaximalSolution` predicate (`Spec.lean:210-214`) they depend on;
* the quantitative restart `restart`, `restart_datum`, `restart_force`
  (`Spec.lean:512-558`);
* Theorem 4.2's packaged identification `insertion_lifespan_eq`
  (`Spec.lean:609-626`).

Nothing here asserts `eq:mild`, the continuation criterion `eq:criterion` (A04),
or any smallness, common-horizon, compact-support or `p ∈ L²` side condition.
The Grönwall coefficient's finiteness and the `L^∞` embedding `‖z‖_∞ ≤ C‖z‖_{H²}`
of `eq:Rproduct` (the edge `A03 → A02` of `research/A02/COMPARISON.md` §5) are
steps of the discharging proofs, not fields.

## The narrowing to `F_R`, recorded deliberately

`prop:local` quantifies over "each force smooth into every `H^m` on compact time
intervals" (`02-preliminaries.tex:107-109`); `MemForceR` (`Data.lean:544`)
additionally demands the `L¹_t`/`L²_t` finiteness of `eq:Rclasses` at every
order, so the datum fields are stated on the strictly smaller class
`F_c ⊆ F_rd ⊆ F_R` Section 4 quantifies over (`04-whole-space.tex:183-192`).
The initial class `initialClassR` is `X_R` verbatim (`02-preliminaries.tex:12`).
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.MaximalPartial

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## The two objects `Data.lean` does not define, restated verbatim

`limsupLeft` and `speedENorm` are `⟪D01:limsupLeft⟫` and `⟪D01:normLinfty⟫`
(`research/section4/STATEMENTS.md:1209,1171`), which `Contracts/V1/Data.lean`
does not define.  They are restated **token-for-token** from
`research/A02/Spec.lean:135-136,148-149` and are used only by
`lifespan_le_of_unbounded`.  `formalization/NSFormalization/Section4/A02/Patch.lean`
carries a byte-identical copy; `verification/Bindings/MaximalPartial.lean` states
the `rfl` bridge between the two. -/

/-- `research/A02/Spec.lean:135-136`, `04-whole-space.tex:35`,
`02-preliminaries.tex:47-48`: the left limit superior `limsup_{t↑T} φ(t)`, valued
in `ℝ≥0∞` so that unboundedness is literally `= ⊤`. -/
def limsupLeft (T : ℝ) (φ : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup φ (nhdsWithin T (Iio T))

/-- `research/A02/Spec.lean:148-149`, `04-whole-space.tex:35`: the `L^∞(R³)` norm
`‖z‖_{L^∞}` of a spatial field, the essential supremum over `volume`. -/
def speedENorm (z : SpatialField) : ℝ≥0∞ :=
  eLpNorm z ⊤ (volume : Measure Space)

/-- **The proved part of A02's maximal-solution interface** beyond
`A02.uniqueness`.  Ten fields of `research/A02/Spec.lean`'s `MaximalSolutionAPI`,
discharged by `formalization/NSFormalization/Section4/A02/{Restrict,Order,Patch}.lean`,
in the vocabulary of `Contracts/V1/Data.lean`; plus the registered uniqueness
record, carried as a field.  See the module docstring for the excluded fields. -/
structure MaximalPartialAPI where
  /-- The registered uniqueness half of `prop:local` (`A02.uniqueness`,
  `Contracts/V1/Uniqueness.lean`), carried structurally so that this record
  includes it — the analogue of `InsertionFamilyAPI` carrying `ScalingAPI`.  A02
  owns both halves; only uniqueness was registered first. -/
  uniqueness : Contracts.V1.Uniqueness.UniquenessAPI
  /-- `appendix-a-local-theory.tex:124` "Patching these local solutions":
  restriction to a shorter positive horizon, with the *same* velocity and
  pressure fields.  `research/A02/Spec.lean:345-348`, discharged by
  `Section4/A02/Restrict.lean` `exists_restrict`. -/
  restrict : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), ∀ S : ℝ, 0 < S → S ≤ T →
      ∃ w : ClassicalSolutionR ν a f S,
        w.velocity = u.velocity ∧ w.pressure = u.pressure
  /-- `appendix-a-local-theory.tex:124-125`: two local solutions of the same
  datum patch to one solution on the union of their intervals, agreeing with each
  on its own interval (velocities pointwise, pressures up to the gauge).
  `research/A02/Spec.lean:357-367`, discharged by `Section4/A02/Patch.lean`
  `patch`. -/
  patch : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
    0 < ν → a ∈ initialClassR → MemForceR f →
      ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
        (u₂ : ClassicalSolutionR ν a f T₂),
        ∃ w : ClassicalSolutionR ν a f (max T₁ T₂),
          (∀ t ∈ Ico (0 : ℝ) T₁, ∀ x : Space,
              w.velocity (t, x) = u₁.velocity (t, x)) ∧
          (∀ t ∈ Ico (0 : ℝ) T₂, ∀ x : Space,
              w.velocity (t, x) = u₂.velocity (t, x)) ∧
          PressureGaugeEquivOn (Ico (0 : ℝ) T₁) u₁.pressure w.pressure ∧
          PressureGaugeEquivOn (Ico (0 : ℝ) T₂) u₂.pressure w.pressure
  /-- `research/A01/Spec.lean:371-372`, the inequality A01 explicitly assigns to
  A02: the local horizon is below the maximal lifespan.  `research/A02/Spec.lean:372-375`.

  Stated **in the form `Section4/A02/Order.lean` proves it**
  (`horizon_le_lifespan_of_localSolution`): the A01 clause
  ⟪A01:LocalTheoryAPI.solution⟫ (`research/A01/Spec.lean:318-321`) — the local
  classical solution on `[0, horizon)` for every manuscript datum — is an
  **explicit hypothesis** here rather than an ambient A01 field.  Instantiating
  it at A01's `LocalTheoryAPI.solution` once A01 is registered gives the original
  spec field verbatim; A02's own content is only the order-theoretic
  `le_iSup`. -/
  horizon_le_lifespan : ∀ (horizon : ℝ → SpatialField → SpaceTimeField → ℝ),
    (∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ClassicalSolutionR ν a f (horizon ν a f)) →
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f
  /-- `02-preliminaries.tex:31,96-100`: **the canonical pressure gauge**, the
  field that makes one pressure serve every horizon: subtracting the value at a
  fixed basepoint `x₀` is again a classical pressure for the same velocity.
  `research/A02/Spec.lean:399-403`, discharged by `Section4/A02/Restrict.lean`
  `exists_pressure_normalization`. -/
  pressure_normalization : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionR ν a f T) (x₀ : Space),
      ∃ w' : ClassicalSolutionR ν a f T,
        w'.velocity = w.velocity ∧
        ∀ z : SpaceTime, w'.pressure z = w.pressure z - w.pressure (z.1, x₀)
  /-- `02-preliminaries.tex:42` eq:Rsingularforces through `Data.lean` `breakdownSetIn`:
  `T^ν_{max,R}(a,f) ≤ T` is exactly "no classical solution has a horizon beyond
  `T`".  `research/A02/Spec.lean:443-446`, discharged by `Section4/A02/Order.lean`
  `lifespan_le_iff`.  `0 ≤ T` is needed because `ENNReal.ofReal` collapses the
  negative reals. -/
  lifespan_le_iff : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
    0 ≤ T →
      (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
        ∀ S : ℝ, Nonempty (ClassicalSolutionR ν a f S) → S ≤ T)
  /-- The same characterization in the contrapositive shape Theorem 4.2 argues in
  (`04-whole-space.tex:53`).  `research/A02/Spec.lean:451-455`, discharged by
  `Section4/A02/Order.lean` `lifespan_le_iff_no_extension`. -/
  lifespan_le_iff_no_extension : ∀ (ν : ℝ) (a : SpatialField)
      (f : SpaceTimeField) (T : ℝ), 0 ≤ T →
      (maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
        ∀ S : ℝ, T < S → IsEmpty (ClassicalSolutionR ν a f S))
  /-- The lower half of "`T^ν_{max,R}(a,g_ε) = T` exactly"
  (`04-whole-space.tex:34,53`): a solution on every strictly shorter interval
  pushes the lifespan up to `T`.  `research/A02/Spec.lean:463-466`, discharged by
  `Section4/A02/Order.lean` `lifespan_ge_of_forall_shorter`. -/
  lifespan_ge_of_forall_shorter : ∀ (ν : ℝ) (a : SpatialField)
      (f : SpaceTimeField) (T : ℝ), 0 < T →
      (∀ b : ℝ, 0 < b → b < T → Nonempty (ClassicalSolutionR ν a f b)) →
        ENNReal.ofReal T ≤ maximalLifespanR ν a f
  /-- `02-preliminaries.tex:34-36` against `:32`: "regular through `T`" and "`T`
  is strictly below the maximal lifespan" are the same condition.
  `research/A02/Spec.lean:476-478`, discharged by `Section4/A02/Order.lean`
  `regularThrough_iff`. -/
  regularThrough_iff : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
      (T : ℝ), 0 < T →
      (RegularThrough ν a f T ↔ ENNReal.ofReal T < maximalLifespanR ν a f)
  /-- `04-whole-space.tex:32` "the solution … regular through `T+δ` for some
  `δ > 0`", the shape R42 declares (`research/section4/STATEMENTS.md:332-333`): a
  `RegularThrough` hypothesis upgraded to one margin `δ` carrying a solution on
  `[0,T+δ)`, a *strictly* longer realized horizon (the middle conjunct, which
  lets R42 read its reference on the closed `Icc 0 (T+δ)`), and the strict
  lifespan inequality.  `research/A02/Spec.lean:500-504`, discharged by
  `Section4/A02/Order.lean` `referenceLifespan`. -/
  referenceLifespan : ∀ (ν : ℝ) (a : SpatialField) (g : SpaceTimeField)
      (T : ℝ), 0 < T → RegularThrough ν a g T →
      ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a g (T + δ)) ∧
        (∃ S : ℝ, T + δ < S ∧ Nonempty (ClassicalSolutionR ν a g S)) ∧
        ENNReal.ofReal (T + δ) < maximalLifespanR ν a g
  /-- The upper half of Theorem 4.2's "`T^ν_{max,R}(a,g_ε) = T` exactly"
  (`04-whole-space.tex:53`): if `(u,p)` is a classical solution on every `[0,S)`
  with `S < T` and its `L^∞` speed has `limsup_{t↑T} = ⊤`, then no classical
  solution of the same datum reaches beyond `T`, so the lifespan is at most `T`.
  `research/A02/Spec.lean:576-582`, discharged by `Section4/A02/Patch.lean`
  `lifespan_le_of_unbounded`.  The blow-up hypothesis is written in the
  manuscript's own `L^∞` norm `speedENorm` (`04-whole-space.tex:35`); the
  discharging proof's `‖z‖_∞ ≤ C‖z‖_{H²}` step is A03's, not a field here. -/
  lifespan_le_of_unbounded : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
      (T : ℝ), 0 < ν → a ∈ initialClassR → MemForceR f → 0 < T →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ S : ℝ, 0 < S → S < T →
            ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p) →
        limsupLeft T (fun t => speedENorm (fun x : Space => u (t, x))) = ⊤ →
          maximalLifespanR ν a f ≤ ENNReal.ofReal T

end BlowupDensity.Contracts.V1.MaximalPartial
