import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.A02.Order

/-!
# R42: the S-level pieces of the lifespan identification of Theorem 4.2

`paper/sections/04-whole-space.tex:34,53` (the two lifespan clauses of
`thm:Rinsert`) assert, for the inserted family `u_eps` of Theorem 4.2:

* `T^nu_{max,R}(a, g_eps) = T` -- the perturbed solution's maximal lifespan is
  exactly the packet's singular time `T` (blow-up there), and
* `T + delta < T^nu_{max,R}(a, g)` -- the reference for `a` with force `g`
  lives strictly past `T + delta`.

These are the clauses collected, deliberately **unregistered**, in
`Contracts.V1.InsertionLifespanAPI`.  They are discharged, in the split recorded
in `research/R42/LIFESPAN_SPLIT.md`, by feeding `A02`'s registered maximal-solution
interface (`MaximalPartial.lean`: `lifespan_le_of_unbounded`,
`lifespan_ge_of_forall_shorter`, `referenceLifespan`) the fact that `u_eps`
solves on every `[0,S)`, `S < T`, together with its `L^infinity` blow-up.

This module proves the **S-level, contract-free** analytic lemmas of that split.
Because `NSFormalization` is an upstream Lake package of the `Contracts` library
these are stated in the vocabulary of `Mathlib` and `NavierStokes.ProblemStatement`;
`verification/Bindings/*` will consume them against the versioned notions
(`Data.speedENorm`, `Data.maximalLifespanR`, `MaximalPartial.limsupLeft`).

Contents.

1. `limsup_eq_top_of_le_add_const` -- the abstract `ENNReal` limsup transfer: a
   blow-up survives a bounded additive perturbation.
2. `eLpNormTop_le_ofReal`, `eLpNormTop_le_add` -- the `L^infinity` (essential
   supremum) bound of a pointwise-bounded field, and the triangle inequality
   feeding (1).
3. `limsup_eLpNormTop_add_eq_top` -- the concrete `L^infinity` blow-up transfer
   `limsup ‖U‖_inf = ⊤ ∧ ‖w‖ ≤ C ⟹ limsup ‖U + w‖_inf = ⊤` of
   `04-whole-space.tex:35`, combining (1) and (2).
4. `hasCompactSupport_of_tsupport_subset_ball` -- the velocity difference
   `u_eps - v = w_eps + U_eps`, spatially supported in the ball `B`
   (`04-whole-space.tex:37-38`), has compact spatial support at each time.
5. `exists_isSobolevDatum_of_contDiff_hasCompactSupport` -- a compactly supported
   smooth spatial field has an angular Sobolev datum at every real order, the
   `HasCompactSupport` entry point of `Data.ClassicalSolutionR.sobolev`
   (`02-preliminaries.tex:29`), via the `D01` unit
   `NSFormalization.Section4.D01.exists_isSobolevDatum_of_contDiff_memLp`.
6. `memForceR_insertedForce` -- split item #3 (now S, review finding 2):
   `g_eps in F_R` from `g in F_R` and the compact force difference
   `g_eps - g in C_c^infinity`, one application of the *registered* D01 unit
   `D01.memForceR_of_compact_difference`.
7. `lt_maximalLifespanR_of_regularThrough` -- split item #6 strict half (S under
   the manuscript's own hypothesis, review finding 4): `T+delta < T^nu_{max,R}(a,g)`
   from `RegularThrough nu a g (T+delta)` in one step via `A02.regularThrough_iff`.

The remaining pieces (`LIFESPAN_SPLIT.md`): (2a) the pointwise `SpeedUnboundedAt`
⟹ essSup `limsupLeft` transfer (**M**); (1e-i) the *time-continuity* of the
correction's datum path (**M**, via `D01.contDiff_angularPath` after a time cutoff;
the additivity 1e-ii and `ContinuousOn.add` are already registered) to build
`u_eps`'s `sobolev` field; and the `RegularThrough (T+delta)` hypothesis a
correct-strength reference (an R42-V2) must carry -- item #6 (6).
-/

noncomputable section

open MeasureTheory Filter
open scoped ContDiff ENNReal
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01

namespace NSFormalization.Section4.R42

/-! ## 1. The abstract `ENNReal` limsup transfer -/

/-- **A blow-up survives a bounded additive perturbation.**  In `ℝ≥0∞`, if
`f a ≤ g a + C` pointwise with `C` finite and `limsup f L = ⊤`, then
`limsup g L = ⊤`.

This is the order-theoretic core of the `L^infinity` blow-up clause
`limsup_{t↑T} ‖u_eps(t)‖_inf = ⊤` (`paper/sections/04-whole-space.tex:35`): a
bounded correction (the background `v + w_eps`, or the correction `w_eps`) cannot
tame an unbounded speed. -/
theorem limsup_eq_top_of_le_add_const {α : Type*} {L : Filter α} {f g : α → ℝ≥0∞}
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hle : ∀ a, f a ≤ g a + C) (htop : Filter.limsup f L = ⊤) :
    Filter.limsup g L = ⊤ := by
  by_contra h
  have hlt : Filter.limsup g L < ⊤ := lt_top_iff_ne_top.mpr h
  obtain ⟨b, hgb, hbtop⟩ := exists_between hlt
  have hev : ∀ᶠ a in L, g a < b := eventually_lt_of_limsup_lt hgb
  have hfb : ∀ᶠ a in L, f a ≤ b + C :=
    hev.mono (fun a ha => (hle a).trans (by gcongr))
  have hle2 : Filter.limsup f L ≤ b + C := limsup_le_of_le (h := hfb)
  rw [htop] at hle2
  exact (ENNReal.add_ne_top.mpr ⟨hbtop.ne, hC⟩) (top_le_iff.mp hle2)

/-! ## 2. `L^infinity` bounds via the essential supremum -/

/-- The `L^infinity(R³)` norm of a field bounded by a constant `C ≥ 0` is at most
`C`.  `Data.speedENorm z = eLpNorm z ⊤ volume` is exactly `eLpNorm _ ⊤ volume`, so
this bounds the speed norm of the correction `w_eps`, whose slices are uniformly
bounded (`CorrectionAPI.correction_derivative_bound` at order `0`). -/
theorem eLpNormTop_le_ofReal {w : Space → Space} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ x, ‖w x‖ ≤ C) :
    eLpNorm w ⊤ (volume : Measure Space) ≤ ENNReal.ofReal C := by
  rw [eLpNorm_exponent_top]
  refine eLpNormEssSup_le_of_ae_nnnorm_bound (C := C.toNNReal) ?_
  filter_upwards with x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC]
  exact hw x

/-- The reverse triangle inequality for the `L^infinity` norm against a
pointwise-bounded perturbation `w`: `‖u‖_inf ≤ ‖u + w‖_inf + C`.  With `u = U_eps`
the rescaled packet and `w = v + w_eps` (or `w = -v - w_eps`) the bounded
background, this is the pointwise hypothesis of `limsup_eq_top_of_le_add_const`.
The measurability hypotheses hold for the smooth slices of Theorem 4.2. -/
theorem eLpNormTop_le_add {u w : Space → Space} {C : ℝ} (hC : 0 ≤ C)
    (hu : AEStronglyMeasurable u (volume : Measure Space))
    (hwm : AEStronglyMeasurable w (volume : Measure Space))
    (hw : ∀ x, ‖w x‖ ≤ C) :
    eLpNorm u ⊤ (volume : Measure Space) ≤
      eLpNorm (fun x => u x + w x) ⊤ (volume : Measure Space) + ENNReal.ofReal C := by
  have h1 : u = (fun x => u x + w x) + (fun x => -w x) := by funext x; simp
  calc eLpNorm u ⊤ (volume : Measure Space)
      = eLpNorm ((fun x => u x + w x) + (fun x => -w x)) ⊤ (volume : Measure Space) := by
        rw [← h1]
    _ ≤ eLpNorm (fun x => u x + w x) ⊤ (volume : Measure Space)
          + eLpNorm (fun x => -w x) ⊤ (volume : Measure Space) :=
        eLpNorm_add_le (hu.add hwm) hwm.neg le_top
    _ ≤ eLpNorm (fun x => u x + w x) ⊤ (volume : Measure Space) + ENNReal.ofReal C := by
        gcongr
        rw [show (fun x => -w x) = (fun x => (-w) x) from rfl, eLpNorm_neg]
        exact eLpNormTop_le_ofReal hC hw

/-- **The `L^infinity` blow-up transfer of `04-whole-space.tex:35`.**  If the
family of slices `a ↦ U a` has `limsup ‖U a‖_inf = ⊤` along `L` and `w` is
uniformly bounded by `C`, then `a ↦ U a + w a` also has `limsup ‖U a + w a‖_inf = ⊤`.

Instantiated at `L = 𝓝[<] T`, `U a = U_eps(a,·)` and `w a = (v + w_eps)(a,·)` this
turns the rescaled packet's essential-supremum blow-up
(`ScalingAPI.scaledBlowup`, in essSup form) into the inserted velocity's, feeding
`MaximalPartial.lifespan_le_of_unbounded`.  `Filter.limsup · (𝓝[<] T)` is exactly
`MaximalPartial.limsupLeft T` and `eLpNorm · ⊤ volume` is `Data.speedENorm`. -/
theorem limsup_eLpNormTop_add_eq_top {α : Type*} {L : Filter α}
    {u w : α → Space → Space} {C : ℝ} (hC : 0 ≤ C)
    (hu : ∀ a, AEStronglyMeasurable (u a) (volume : Measure Space))
    (hwm : ∀ a, AEStronglyMeasurable (w a) (volume : Measure Space))
    (hw : ∀ a x, ‖w a x‖ ≤ C)
    (htop : Filter.limsup (fun a => eLpNorm (u a) ⊤ (volume : Measure Space)) L = ⊤) :
    Filter.limsup (fun a => eLpNorm (fun x => u a x + w a x) ⊤ (volume : Measure Space)) L
      = ⊤ :=
  limsup_eq_top_of_le_add_const ENNReal.ofReal_ne_top
    (fun a => eLpNormTop_le_add hC (hu a) (hwm a) (hw a)) htop

/-! ## 3. Compact spatial support of the velocity difference -/

/-- A field whose `tsupport` sits inside a metric ball has compact support: the
`tsupport` is closed and contained in a (compact) closed ball of the proper space
`R³`.  Applied to `u_eps(t,·) - v(t,·) = w_eps(t,·) + U_eps(t,·)`, whose
`tsupport ⊆ ball x0 r` (`04-whole-space.tex:37-38`,
`InsertionFamilyAPI.velocityDifference_support`), this is the compact-support
input to the datum lemma below. -/
theorem hasCompactSupport_of_tsupport_subset_ball {d : Space → Space} {c : Space}
    {r : ℝ} (h : tsupport d ⊆ Metric.ball c r) : HasCompactSupport d :=
  IsCompact.of_isClosed_subset (isCompact_closedBall c r) (isClosed_tsupport d)
    (h.trans Metric.ball_subset_closedBall)

/-! ## 4. The angular Sobolev datum of a compactly supported smooth field -/

/-- **A compactly supported smooth spatial field has an angular Sobolev datum at
every real order.**  This is the `HasCompactSupport` entry point to
`Data.ClassicalSolutionR.sobolev` (`02-preliminaries.tex:29`) for the correction
`w_eps + U_eps = u_eps - v`: every spatial jet of a smooth compactly supported
field is continuous with compact support, hence in `L²`, so the `D01` unit
`exists_isSobolevDatum_of_contDiff_memLp` produces the datum.

The `NSFormalization.Section4.D01.IsSobolevDatum` here is *definitionally*
`Contracts.V1.Data.IsSobolevDatum`. -/
theorem exists_isSobolevDatum_of_contDiff_hasCompactSupport {z : Space → Space}
    (hz : ContDiff ℝ ∞ z) (hcs : HasCompactSupport z) (s : ℝ) :
    ∃ A : RealVectorSobolev s, IsSobolevDatum s z A := by
  refine exists_isSobolevDatum_of_contDiff_memLp hz (fun n => ?_) s
  exact (hz.continuous_iteratedFDeriv (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
    (hcs.iteratedFDeriv n)

/-! ## 5. Force class and reference lifespan (registered-unit one-liners) -/

/-- **Split item #3 (S).**  `g_eps ∈ F_R` from `g ∈ F_R` and the compact force
difference `g_eps - g ∈ C_c^infinity` (`04-whole-space.tex:48,51,185`).  This is a
single application of the **registered** D01 unit
`NSFormalization.Section4.D01.memForceR_of_compact_difference` (`ForceClass.lean:401`,
`Contracts/V1/DatumLemmas.lean:381`), whose second argument is exactly
`InsertionFamilyAPI.forceDifference_compact ε hε`
(`Contracts/V1/InsertionFamily.lean:272`, `Data.MemForceCompact (fun z => force ε z - g z)`).

Stated against the D01 restatements `MemForceR`, `MemForceCompact` (`ForceClass.lean:158,169`,
definitionally `Contracts.V1.Data.MemForceR`/`MemForceCompact`, `rfl`-bridged in
`Bindings/DatumLemmas.lean`); the binding supplies `hd` from `forceDifference_compact`
and `hg` from the new hypothesis field `hg : MemForceR g` that an R42-V2 asserting
`memF` must add (`InsertionFamilyAPI` carries no such field; `research/R42/ATTEMPTS.md §5b`). -/
theorem memForceR_insertedForce {g gε : VelocityField} (hg : MemForceR g)
    (hd : MemForceCompact (fun z => gε z - g z)) : MemForceR gε :=
  memForceR_of_compact_difference hg hd

open NSFormalization.Section4.A02 in
/-- **Split item #6, strict half (S under the manuscript's hypothesis).**
`T + delta < T^nu_{max,R}(a, g)`, the `InsertionLifespanAPI.referenceLifespan`
clause (`04-whole-space.tex:32`), in one step from `RegularThrough nu a g (T+delta)`
via the *registered* `A02.regularThrough_iff` (`Section4/A02/Order.lean:135`).

The hypothesis is the manuscript's own "the solution … **regular through `T+delta`**"
(`02-preliminaries.tex:34-36`, `04-whole-space.tex:32`), i.e.
`Data.RegularThrough nu a g (T+delta)` = a classical solution on `[0, T+delta+delta')`.
`InsertionFamilyAPI.reference` currently gives only the **half-open** horizon
`Data.ClassicalSolutionR nu a g (T+delta)` (a solution on `[0, T+delta)`), which yields
only the non-strict `ofReal (T+delta) ≤ maximalLifespanR` (`le_iSup`); the strict `<`
needs this stronger hypothesis, so a correct-strength R42-V2 must carry
`RegularThrough nu a g (T+delta)` (equivalently read `reference` on the closed
`Icc 0 (T+delta)`).  Then `family.margin` is untouched and no A02 margin
identification arises (`research/R42/LIFESPAN_SPLIT.md §6`). -/
theorem lt_maximalLifespanR_of_regularThrough {ν : ℝ} {a : SpatialField}
    {g : SpaceTimeField} {T δ : ℝ} (hTδ : 0 < T + δ)
    (h : RegularThrough ν a g (T + δ)) :
    ENNReal.ofReal (T + δ) < maximalLifespanR ν a g :=
  (regularThrough_iff ν a g (T + δ) hTδ).mp h

end NSFormalization.Section4.R42
