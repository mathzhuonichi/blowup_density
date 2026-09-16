import Bindings.GridAssemblyNorms
import Bindings.MainThresholds
import Bindings.FluxCancellation

/-!
# Reconciled specification: Theorem 4.7 (`thm:Rgrid`)

This is the reconciliation of the two blind drafts of the identical whole-space
cell-observation theorem (`paper/sections/04-whole-space.tex:297-304`).  It uses
the raw-data existence shape of Draft B: the regular reference and the entire
finite grid family are fixed before one inserted family is chosen.  The common
ball has Draft A's literal containment in one cell of each grid, rather than the
stronger closure/interior condition used by the proof at line 306.

The convergence clause at `04-whole-space.tex:303` imports only the two limits
at lines 221-226, not Proposition 4.6's completed-space density assertions at
lines 218-220.  Consequently no completed-density proposition is a field below.
The definitional checks after the records nevertheless verify the registered
abbreviations used by the sibling Proposition 4.6 specification.

There is no local placeholder predicate: grids, observations, solution data,
lifespan, support, and every norm are registered in `Contracts.V1.Data`.
-/

noncomputable section

namespace BlowupDensity.Research.R47.Draft

open Set Filter Topology
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- The single inserted family whose existence is asserted in Theorem 4.7
(`paper/sections/04-whole-space.tex:297-304`).  Parameters are ordered as the
raw regular reference `(ν,a,g,T,δ,reference)`, then the complete prescribed
finite grid family `(n,grids)`.  Every field below concerns this one family.
-/
structure RGridFamily (ν : ℝ) (a : SpatialField) (g : SpaceTimeField)
    (T δ : ℝ) (reference : ClassicalSolutionR ν a g (T + δ))
    (n : ℕ) (grids : Fin n → Grid) where
  /-- `04-whole-space.tex:303`: center of the one common support ball.
  Non-vacuity: it is used by `containingCell` and all three support fields, so
  it is not unused witness data. -/
  center : Space
  /-- `04-whole-space.tex:303`: radius of the one common support ball.
  Non-vacuity: the next field makes this radius strictly positive, and the ball
  is used by every spatial localization clause. -/
  radius : ℝ
  /-- `04-whole-space.tex:303`: the common ball has positive radius.
  Non-vacuity: `0 < radius` ensures `Metric.ball center radius` is nonempty. -/
  radius_pos : 0 < radius
  /-- `04-whole-space.tex:303-304`: after the grid family is fixed, choose one
  cell of each grid which contains the same open ball.  The cell index may
  depend on `i`, but the ball may not.
  Non-vacuity: `RGridAPI.choose` quantifies over every `n`, including nonempty
  families; for each such grid this is an actual set containment. -/
  containingCell : ∀ i : Fin n, ∃ k : Fin 3 → ℤ,
    Metric.ball center radius ⊆ (grids i).cell k
  /-- `04-whole-space.tex:32,298`: one cutoff for all sufficiently small
  insertion scales in the chosen family.
  Non-vacuity: `eps_pos` makes the admissible interval `(0,ε₀]` nonempty. -/
  ε₀ : ℝ
  /-- `04-whole-space.tex:32,298`: positivity of the scale cutoff.
  Non-vacuity: together with real density it supplies positive admissible
  scales, so subsequent `ε ∈ Ioc 0 ε₀` clauses are not vacuous. -/
  eps_pos : 0 < ε₀
  /-- `04-whole-space.tex:32,298`: the single total family of inserted forces
  `g_ε`, chosen only after all prescribed grids.
  Non-vacuity: its values are constrained by `force_mem`, observations,
  lifespan, convergence, and support; totality is needed by the `ε → 0+` limit. -/
  force : ℝ → SpaceTimeField
  /-- `04-whole-space.tex:32,298`: for every real scale, a classical solution
  with the original datum `a` and the corresponding force `g_ε`; values outside
  `(0,ε₀]` are arbitrary extensions used to make the limiting family total.
  Non-vacuity: on admissible scales the solutions are constrained by history,
  observations, exact lifespan, convergence, and support. -/
  solution : ∀ ε : ℝ, ClassicalSolutionR ν a (force ε) T
  /-- `04-whole-space.tex:32,298`: every admissible inserted force belongs to
  the manuscript class `F_R`.
  Non-vacuity: `eps_pos` makes the quantified scale interval nonempty, and
  `MemForceR` imposes the registered smoothness and Sobolev conditions. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, MemForceR (force ε)
  /-- `04-whole-space.tex:36,298`: for each admissible scale, the inserted
  velocity equals the fixed reference pointwise throughout the inherited early
  history `0 ≤ t ≤ T-2ε²`; quantifiers are `ε`, membership, `t`, both time
  inequalities, then `x`.
  Non-vacuity: whenever the displayed time inequalities hold this constrains
  every spatial point, rather than naming an uninterpreted history predicate. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t → t ≤ T - 2 * ε ^ 2 →
    ∀ x : Space, (solution ε).velocity (t, x) = reference.velocity (t, x)
  /-- `04-whole-space.tex:38,298`: at each admissible scale, `g_ε-g` is smooth
  and compactly supported in positive spacetime.
  Non-vacuity: `MemForceCompact` is the registered concrete compact-force class,
  not a placeholder proposition, and `eps_pos` supplies admissible scales. -/
  forceDifference_compact : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    MemForceCompact (fun z => force ε z - g z)
  /-- `04-whole-space.tex:298-302`: quantifying in the order `ε`, admissibility,
  prescribed grid `i`, then `t ∈ [0,T)`, every cell average of `u_ε(t)` equals
  the corresponding average of the fixed reference velocity.
  Non-vacuity: `RGridAPI.choose` assumes `T>0`, so the time interval contains
  zero; equality of `gridObservation` functions constrains every cell index. -/
  velocity_observations : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ i : Fin n,
    ∀ t ∈ Ico (0 : ℝ) T,
      gridObservation (grids i) (fun x => (solution ε).velocity (t, x)) =
        gridObservation (grids i) (fun x => reference.velocity (t, x))
  /-- `04-whole-space.tex:298-302`: in the same order `ε`, admissibility, `i`,
  then `t ∈ [0,T)`, every cell average of `g_ε(t)` equals that of `g(t)`.
  Non-vacuity: positive `T` and `ε₀` make the time and scale ranges inhabited,
  while function equality constrains the infinitely many cells of each grid. -/
  force_observations : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ i : Fin n,
    ∀ t ∈ Ico (0 : ℝ) T,
      gridObservation (grids i) (fun x => force ε (t, x)) =
        gridObservation (grids i) (fun x => g (t, x))
  /-- `04-whole-space.tex:303`: for every admissible scale the registered
  maximal lifespan is exactly `T`, not merely bounded above by it.
  Non-vacuity: equality to finite `ENNReal.ofReal T` rules out both a longer
  lifespan and the default infinite lifespan. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    maximalLifespanR ν a (force ε) = ENNReal.ofReal T
  /-- `04-whole-space.tex:303`, invoking `04-whole-space.tex:221-223`: the
  energy norm of `u_ε-reference` tends to zero along positive scales.
  Non-vacuity: `energyENorm` is `ℝ≥0∞`-valued and fail-safe, so an infinite
  energy difference cannot satisfy convergence to zero. -/
  energy_convergence : Tendsto
    (fun ε : ℝ => energyENorm T
      (fun z => (solution ε).velocity z - reference.velocity z))
    (𝓝[>] 0) (𝓝 0)
  /-- `04-whole-space.tex:303`, invoking `04-whole-space.tex:224-228`: the sum
  of the literal `L¹_tL²_x`, `L²_tH⁻¹_x`, and `L²_tḢ⁻¹_x` norms of the force
  difference tends to zero along positive scales.  The last norm is applied to
  the compact difference, not to the background force.
  Non-vacuity: all three summands are nonnegative `ℝ≥0∞` norms, so convergence
  of their sum forces simultaneous smallness and excludes infinite summands. -/
  force_convergence : Tendsto
    (fun ε : ℝ => mixedLebesgueENorm 1 2 (fun z => force ε z - g z) +
      forceSobolevENorm 2 (-1) (fun z => force ε z - g z) +
      forceHomogeneousENorm 2 (-1) (fun z => force ε z - g z))
    (𝓝[>] 0) (𝓝 0)
  /-- `04-whole-space.tex:303-304`: for each admissible scale and every
  `t ∈ [0,T)`, the spatial support of `u_ε-reference` lies in the common ball.
  Non-vacuity: positive `T` and `ε₀` make both ranges inhabited, and the field
  gives concrete topological-support containment at each such time. -/
  velocity_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) T,
    tsupport (fun x => (solution ε).velocity (t, x) - reference.velocity (t, x)) ⊆
      Metric.ball center radius
  /-- `04-whole-space.tex:303-304`: for each admissible scale, choose one
  time-dependent but spatially constant gauge `c`; after subtracting it, the
  pressure difference is supported in the common ball for every `t ∈ [0,T)`.
  The quantifier over `c` precedes the quantifier over time.
  Non-vacuity: a single gauge must satisfy every presingular time, so it cannot
  be selected independently at each point or replace the support condition. -/
  pressure_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∃ c : ℝ → ℝ,
    ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x => (solution ε).pressure (t, x) -
        reference.pressure (t, x) - c t) ⊆ Metric.ball center radius
  /-- `04-whole-space.tex:303-304`, inheriting `04-whole-space.tex:38`: for
  every admissible scale, every point in the full spacetime support of `g_ε-g`
  has its spatial coordinate in the common ball, including times after `T`.
  Non-vacuity: this is global spacetime support containment and is paired with
  the substantive compactness assertion `forceDifference_compact`. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ z ∈ tsupport (fun z => force ε z - g z), z.2 ∈ Metric.ball center radius

/-- Theorem 4.7 (`paper/sections/04-whole-space.tex:297-304`) in universal
existence form.  The exact order is `ν`, positivity; `a`, initial-class
membership; `g`, force-class membership; `T`, positivity; `δ`, positivity;
the actual reference solution; `n`; the complete finite grid family; then one
simultaneous `RGridFamily` witness.
-/
structure RGridAPI where
  /-- `04-whole-space.tex:298`: every positive-viscosity regular reference and
  every prescribed `Fin n` family of complete uniform Cartesian grids admits
  one family carrying all clauses at once.
  Non-vacuity: this universally quantifies the raw hypotheses and produces a
  `Nonempty RGridFamily`; it is not conditional on an already chosen insertion
  family and cannot choose a different witness for each grid. -/
  choose : ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
    ∀ reference : ClassicalSolutionR ν a g (T + δ),
    ∀ n : ℕ, ∀ grids : Fin n → Grid,
      Nonempty (RGridFamily ν a g T δ reference n grids)


end BlowupDensity.Research.R47.Draft

noncomputable section
namespace BlowupDensity.Bindings
open Set Filter MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4.I03 (CompactHomogeneousRealization)
open BlowupDensity.Research.R47.Draft
open scoped ENNReal Topology

/-- Construct the insertion in the prescribed common grid cell ball.
The specification structures above are copied verbatim from R47/Spec.lean. -/
def rGridFamily_of_data (hreal : CompactHomogeneousRealization)
    (ν : ℝ) (hν : 0 < ν) (a : SpatialField) (_ha : a ∈ initialClassR)
    (g : SpaceTimeField) (hg : MemForceR g) (T : ℝ) (hT : 0 < T)
    (δ : ℝ) (hδ : 0 < δ) (reference : ClassicalSolutionR ν a g (T + δ))
    (n : ℕ) (grids : Fin n → Grid) : RGridFamily ν a g T δ reference n grids := by
  classical
  apply Classical.choice
  obtain ⟨x₀, r, hr, hcell⟩ := exists_ball_in_common_cell n grids 0
  let P := insertionFromData_packet ν hν
  have hsub : Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) ⊆
      Ico (0 : ℝ) (T + δ) ×ˢ (univ : Set Space) :=
    prod_mono Ioo_subset_Ico_self Subset.rfl
  let C : CorrectionAPI ν P := correction P (T := T) (δ := δ) (r := r)
    (v := reference.velocity) (π := reference.pressure) (g := g) x₀ hT hδ hr
    (reference.velocity_smooth.mono hsub) (reference.pressure_smooth.mono hsub)
    (fun t ht => reference.divergence t ⟨ht.1.le, ht.2⟩) reference.momentum
  let A := insertionFamily (scaling C thresholds) reference rfl rfl
  -- Clamp only the arbitrary total extension; all admissible scales are fixed.
  let e : ℝ → ℝ := fun ε => if ε ∈ Ioc (0 : ℝ) A.ε₀ then ε else A.ε₀
  have he (ε : ℝ) : e ε ∈ Ioc (0 : ℝ) A.ε₀ := by
    dsimp [e]
    split_ifs with h
    · exact h
    · exact ⟨A.eps_pos, le_rfl⟩
  have heq (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) A.ε₀) : e ε = ε := by
    dsimp only [e]
    split_ifs
    rfl
  choose U hU hπ using fun ε => InsertionLifespan.sol_fullHorizon A (he ε)
  have hd (ε : ℝ) : (fun z => A.force ε z - g z) =
      C.forceCorrection ε + scaledForce P.force C.x₀ C.T ε := by
    funext z
    rw [A.force_formula]
    change g z + C.forceCorrection ε z + scaledForce P.force C.x₀ C.T ε z - g z = _
    simp only [Pi.add_apply]
    abel
  have hm := grid_mixed_limit C
  have hh := grid_homogeneous_limit hreal C
  have hgA : A.scaling.correction.g = g := rfl
  have hs := A.forceConvergence 2 (Or.inr rfl) (-1) (by
    rw [A.scaling.thresholds.formula]; norm_num)
  rw [hgA] at hs
  have hf : Tendsto (fun ε : ℝ => mixedLebesgueENorm 1 2 (fun z => A.force ε z - g z) +
      forceSobolevENorm 2 (-1) (fun z => A.force ε z - g z) +
      forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - g z))
      (𝓝[>] 0) (𝓝 0) := by
    have hm' : Tendsto (fun ε : ℝ => mixedLebesgueENorm 1 2 (fun z => A.force ε z - g z))
        (𝓝[>] 0) (𝓝 0) := by simpa only [hd] using hm
    have hh' : Tendsto (fun ε : ℝ => forceHomogeneousENorm 2 (-1) (fun z => A.force ε z - g z))
        (𝓝[>] 0) (𝓝 0) := by simpa only [hd] using hh
    simpa only [add_zero] using (hm'.add hs).add hh'
  have hw : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioc (0 : ℝ) A.ε₀ := Ioc_mem_nhdsGT A.eps_pos
  refine ⟨{
    center := x₀
    radius := r
    radius_pos := hr
    containingCell := hcell
    ε₀ := A.ε₀
    eps_pos := A.eps_pos
    force := fun ε => A.force (e ε)
    solution := U
    force_mem := ?_
    history := ?_
    forceDifference_compact := ?_
    velocity_observations := ?_
    force_observations := ?_
    lifespan := ?_
    energy_convergence := ?_
    force_convergence := ?_
    velocity_support := ?_
    pressure_support := ?_
    force_support := ?_ }⟩
  · intro ε hε
    exact InsertionLifespan.memForceR_force A hg (he ε)
  · intro ε hε t ht ht' x
    rw [hU, heq ε hε]
    exact A.history ε hε t ht ht' x
  · intro ε hε
    exact A.forceDifference_compact (e ε) (he ε)
  · intro ε hε i t ht
    obtain ⟨k, hk⟩ := hcell i
    rw [hU, heq ε hε]
    exact velocity_gridObservation_eq A hε ht (grids i) k hk
  · intro ε hε i t ht
    obtain ⟨k, hk⟩ := hcell i
    exact force_gridObservation_eq' A hg (he ε) ht (grids i) k hk
  · intro ε hε
    exact InsertionLifespan.lifespan_eq A hg (he ε)
  · apply (mainThresholds_energyConvergence A).congr'
    filter_upwards [hw] with ε hε
    rw [hU, heq ε hε]
    rfl
  · apply hf.congr'
    filter_upwards [hw] with ε hε
    rw [heq ε hε]
  · intro ε hε t ht
    rw [hU, heq ε hε]
    exact A.velocityDifference_support ε hε t ht
  · intro ε hε
    refine ⟨fun _ => 0, fun t ht => ?_⟩
    simp only [hπ, heq ε hε, sub_zero]
    exact A.pressureDifference_support ε hε t ht
  · intro ε hε z hz
    exact A.forceDifference_ball (e ε) (he ε) z hz

/-- Theorem 4.7, with the choose statement copied token for token. -/
theorem rGrid_choose_of_realization (hreal : CompactHomogeneousRealization) :
    ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
    ∀ reference : ClassicalSolutionR ν a g (T + δ),
    ∀ n : ℕ, ∀ grids : Fin n → Grid,
      Nonempty (RGridFamily ν a g T δ reference n grids) := by
  intro ν hν a ha g hg T hT δ hδ reference n grids
  exact ⟨rGridFamily_of_data hreal ν hν a ha g hg T hT δ hδ reference n grids⟩

end BlowupDensity.Bindings
