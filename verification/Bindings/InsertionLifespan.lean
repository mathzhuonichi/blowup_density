import Contracts.V1.InsertionFamily
import Contracts.V1.InsertionLifespan
import Contracts.V1.MaximalPartial
import Contracts.V1.DatumLemmas
import Contracts.V2.MaximalPartial
import Bindings.MaximalPartial
import Bindings.DatumLemmas
import NSFormalization.Section4.R42.SolutionOnShorter
import NSFormalization.Section4.R42.BlowupEssSup
import NSFormalization.Section4.R42.FullHorizon

/-! Lifespan and maximality of the inserted whole-space solution.

The lower bound comes from classical solutions on every shorter interval.
The upper bound follows from the essential-supremum blow-up and maximal
uniqueness. The reference solution remains regular beyond the prescribed
insertion time. These results supply the current lifespan record and its
full-horizon extension. -/

noncomputable section

namespace BlowupDensity.Bindings.InsertionLifespan

open Set
open BlowupDensity.Contracts.V1
open scoped ENNReal

variable {ν : ℝ} {P : PacketAPI ν} (F : InsertionFamilyAPI ν P) {ε : ℝ}

/-! ## 1. `sol_on_shorter` (split #1)

The inserted pair `(u_ε, p_ε)` is a classical solution `Data.ClassicalSolutionR`
on every shorter horizon `0 < S < T`, with velocity `u_ε` and pressure `p_ε`.
This is the reviewer-verified 22-line instantiation of the merged
`classicalSolutionR_of_inserted` (`research/R42/REVIEW_SOL_SHORTER.md`): the
reference is moved into the `A02` restatement by `uniqueness_toA02`, the datum
threshold `t₁ = T − 2ε² > 0` comes from `ScalingAPI.eps_time`, the three
history/support hypotheses are the API fields rewritten through
`reference_velocity` / `reference_pressure`, and the resulting `A02` solution is
moved back to `Data.ClassicalSolutionR` by `maximalPartial_ofA02`. -/
theorem sol_on_shorter (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    ∀ S : ℝ, 0 < S → S < F.T →
      ∃ w : Data.ClassicalSolutionR ν F.a (F.force ε) S,
        w.velocity = F.velocity ε ∧ w.pressure = F.pressure ε := by
  intro S hS0 hST
  have hεS : ε ∈ Ioc (0 : ℝ) F.scaling.ε₀ := ⟨hε.1, hε.2.trans F.eps_le_scaling⟩
  have ht₁ : 0 < F.scaling.correction.T - 2 * ε ^ 2 := by
    have := lt_of_lt_of_le (F.scaling.eps_time ε hεS) (min_le_left _ _); linarith
  have href : F.reference.velocity = F.scaling.correction.v := F.reference_velocity
  have hrefp : F.reference.pressure = F.scaling.correction.π := F.reference_pressure
  obtain ⟨w, hv, hp⟩ := NSFormalization.Section4.R42.classicalSolutionR_of_inserted
    (uniqueness_toA02 F.reference) F.scaling.correction.margin_pos ht₁
    (F.velocity ε) (F.pressure ε)
    (F.velocity_smooth ε hε) (F.pressure_smooth ε hε) (F.initial ε hε)
    (F.incompressible ε hε) (F.momentum ε hε)
    (by intro t h0 h1 x
        show F.velocity ε (t, x) = F.reference.velocity (t, x)
        rw [href]; exact F.history ε hε t h0 h1 x)
    (by intro t ht
        show tsupport (fun x => F.velocity ε (t, x) - F.reference.velocity (t, x)) ⊆ _
        rw [href]; exact F.velocityDifference_support ε hε t ht)
    (by intro t ht
        show tsupport (fun x => F.pressure ε (t, x) - F.reference.pressure (t, x)) ⊆ _
        rw [hrefp]; exact F.pressureDifference_support ε hε t ht)
    hS0 hST
  exact ⟨maximalPartial_ofA02 w, hv, hp⟩

/-! ## 2. `memForceR_force` (split #3)

`g_ε ∈ F_R` from `g ∈ F_R` and the compact force difference `g_ε − g ∈ C_c^∞`,
one application of the registered D01 unit
`datumLemmas.memForceR_of_compact_difference`.  `F.g` unfolds to
`F.scaling.correction.g`, so `F.forceDifference_compact ε hε` is exactly the
`Data.MemForceCompact (fun z => F.force ε z − F.g z)` the field consumes. -/
theorem memForceR_force (hg : Data.MemForceR F.g) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Data.MemForceR (F.force ε) :=
  datumLemmas.memForceR_of_compact_difference F.g (F.force ε) hg
    (F.forceDifference_compact ε hε)

/-! ## 2b. `initialClassR_a` — `a ∈ X_R`, derived (not a hypothesis)

`F.a ∈ Data.initialClassR = {a | MemHInfty a ∧ IsSolenoidal a}` (`Data.lean:509`)
follows from the reference solution at `t = 0`: `F.a = F.reference.velocity(0,·)`
(`F.reference.initial`), which is smooth (`D01.contDiff_slice` on
`F.reference.velocity_smooth`, already in this module's import closure via
`Bindings.DatumLemmas`), has the datum path `F.reference.sobolev` at `t = 0`, and
is divergence-free (`F.reference.divergence` at `t = 0`).  Derivation supplied by
the lane-092 reviewer (`research/R42/REVIEW_BINDING.md` finding 2,
`/tmp/r42rev092/Scratch.lean`); this replaces the earlier `ha` hypothesis. -/
theorem initialClassR_a : F.a ∈ Data.initialClassR := by
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) (F.scaling.correction.T + F.scaling.correction.δ) :=
    ⟨le_rfl, F.reference.horizon_pos⟩
  have ha_eq : (fun y : Space => F.reference.velocity (0, y)) = F.a :=
    funext F.reference.initial
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := NSFormalization.Section4.D01.contDiff_slice F.reference.velocity_smooth hzero
    rwa [ha_eq] at h
  · intro m
    obtain ⟨G, _, hGd⟩ := F.reference.sobolev m
    exact ⟨G 0, by rw [← ha_eq]; exact hGd 0 hzero⟩
  · intro x
    have h := F.reference.divergence 0 hzero x
    simpa only [Data.IsSolenoidal, NavierStokes.ProblemStatement.spatialDivergence,
      NavierStokes.ProblemStatement.spatialDerivative, ← ha_eq] using h

/-! ## 3. `lifespan_lower` (split #5)

`ofReal T ≤ maximalLifespanR ν a g_ε`, from `sol_on_shorter` and the registered
`lifespan_ge_of_forall_shorter`.  Its only structural input `0 < T` is
`CorrectionAPI.time_pos`, so this clause needs no extra hypothesis. -/
theorem lifespan_lower (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    ENNReal.ofReal F.T ≤ Data.maximalLifespanR ν F.a (F.force ε) :=
  maximalPartial.lifespan_ge_of_forall_shorter ν F.a (F.force ε) F.T
    F.scaling.correction.time_pos
    (fun b hb0 hbT => ⟨(sol_on_shorter F hε b hb0 hbT).choose⟩)

/-! ## 4. `lifespan_upper` (split #4)

`maximalLifespanR ν a g_ε ≤ ofReal T`, from `sol_on_shorter`, `memForceR_force`,
the essSup blow-up transfer, and the registered `lifespan_le_of_unbounded`.  The
blow-up hypothesis is produced from the pointwise `F.blowup` and the slice
continuity of `F.velocity_smooth` via lane 080's `limsupLeft_speedENorm_eq_top`;
its `A02.limsupLeft`/`A02.speedENorm` conclusion is definitionally the contract's
`MaximalPartial.limsupLeft`/`speedENorm` (`Bindings/MaximalPartial.lean:57,61`,
both `rfl`). -/
theorem lifespan_upper (hg : Data.MemForceR F.g) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Data.maximalLifespanR ν F.a (F.force ε) ≤ ENNReal.ofReal F.T := by
  have hgε : Data.MemForceR (F.force ε) := memForceR_force F hg hε
  have hblow : MaximalPartial.limsupLeft F.T
      (fun t => MaximalPartial.speedENorm (fun x : Space => F.velocity ε (t, x))) = ⊤ :=
    NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top (F.blowup ε hε)
      (NSFormalization.Section4.R42.continuous_slice_of_velocity_smooth
        (F.velocity_smooth ε hε))
  exact maximalPartial.lifespan_le_of_unbounded ν F.a (F.force ε) F.T P.viscosity_pos
    (initialClassR_a F) hgε F.scaling.correction.time_pos (F.velocity ε) (F.pressure ε)
    (sol_on_shorter F hε) hblow

/-! ## 5. `lifespan_eq` — the `lifespan` field

`T^ν_{max,R}(a, g_ε) = T` (`04-whole-space.tex:34`), `le_antisymm` of the two
bounds. -/
theorem lifespan_eq (hg : Data.MemForceR F.g) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Data.maximalLifespanR ν F.a (F.force ε) = ENNReal.ofReal F.T :=
  le_antisymm (lifespan_upper F hg hε) (lifespan_lower F hε)

/-! ## 6. `referenceLifespan` — the `referenceLifespan` field (split #6)

`ofReal (T+δ) < maximalLifespanR ν a g` (`04-whole-space.tex:32`), one step from
the registered `maximalPartial.regularThrough_iff` at `T' = T+δ`.  The positivity
`0 < T+δ` is `add_pos time_pos margin_pos`.  Because the field is taken in `Data`
vocabulary, no `A02`/`Data` `RegularThrough` bridge is needed. -/
theorem referenceLifespan (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    ENNReal.ofReal (F.T + F.margin) < Data.maximalLifespanR ν F.a F.g :=
  (maximalPartial.regularThrough_iff ν F.a F.g (F.T + F.margin)
    (add_pos F.scaling.correction.time_pos F.scaling.correction.margin_pos)).mp hreg

/-- Package the reference force and regularity hypotheses with the two proved
lifespan conclusions for the given inserted family. -/
def insertionLifespanAPI (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P where
  family := F
  memForce := hg
  regular := hreg
  referenceLifespan := referenceLifespan F hreg
  lifespan := fun _ε hε => lifespan_eq F hg hε

/-- Regression guard (lane-092 review finding 5): the two clauses of the
registered record are about the **given** family `F`, not a substituted one. -/
theorem insertionLifespanAPI_family (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    (insertionLifespanAPI F hg hreg).family = F := rfl

/-! ## 9. `sol_fullHorizon` and `isMaximalSolution_of_inserted` (lane 098)

The inserted pair on the **full** horizon `[0,T)`, and its identification as the
maximal classical solution.

* `sol_fullHorizon` instantiates lane 098's
  `NSFormalization.Section4.R42.classicalSolutionR_of_inserted_fullHorizon`
  (`Section4/R42/FullHorizon.lean`) exactly as §1's `sol_on_shorter` instantiates
  `classicalSolutionR_of_inserted`, but at the horizon `F.T` itself — the only
  differences from `sol_on_shorter` are the dropped `∀ S, 0 < S → S < F.T` binder
  and the trailing `hS0 hST` replaced by `F.scaling.correction.time_pos` (the
  `0 < T` that `classicalSolutionR_of_inserted_fullHorizon` needs, since
  `F.reference.horizon_pos` only gives `0 < T + δ`).  This is the single
  `Data.ClassicalSolutionR ν F.a (F.force ε) F.T` object — one velocity, one
  pressure, one `sobolev` path continuous on all of `[0,F.T)`, and `∇p_ε ∈ L²` at
  every `t < F.T` — that the family from `sol_on_shorter` does not assemble
  (`contracts.json:188`: `sobolev`/`pressure_gradient` for `u_ε` are "NOT
  asserted" by the registered `R42.insertion_lifespan`).

* `isMaximalSolution_of_inserted` records, in the **registered** Data/V2 vocabulary
  (`Contracts.V2.MaximalPartial.IsMaximalSolution`, contract `A02.maximal_partial_v2`,
  inhabited by `Bindings.maximalPartialV2`), that `(u_ε, p_ε)` **is** the maximal
  classical solution for `(ν, a, g_ε)`.  Under `lifespan_eq`
  (`Data.maximalLifespanR ν a g_ε = ofReal T`) the predicate's `∀ S` clause
  quantifies only over `S < T` (the endpoint `S = T` is never asked for, since the
  guard is strict), so it is discharged by `sol_on_shorter` directly — 5 lines,
  no A02↔Data bridge, needing only `hg` (through `lifespan_eq`) and
  `CorrectionAPI.time_pos`.  The A02-vocabulary form
  `NSFormalization.Section4.A02.IsMaximalSolution` is then one `.mpr` of
  `Bindings.maximalPartial_isMaximalSolution_iff` away.

Both are reviewer-verified (`research/R42/REVIEW_FULL_HORIZON.md`,
`/tmp/r42rev098/Scratch.lean` §B1/§B2). -/
theorem sol_fullHorizon (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    ∃ w : Data.ClassicalSolutionR ν F.a (F.force ε) F.T,
      w.velocity = F.velocity ε ∧ w.pressure = F.pressure ε := by
  have hεS : ε ∈ Ioc (0 : ℝ) F.scaling.ε₀ := ⟨hε.1, hε.2.trans F.eps_le_scaling⟩
  have ht₁ : 0 < F.scaling.correction.T - 2 * ε ^ 2 := by
    have := lt_of_lt_of_le (F.scaling.eps_time ε hεS) (min_le_left _ _); linarith
  have href : F.reference.velocity = F.scaling.correction.v := F.reference_velocity
  have hrefp : F.reference.pressure = F.scaling.correction.π := F.reference_pressure
  obtain ⟨w, hv, hp⟩ :=
    NSFormalization.Section4.R42.classicalSolutionR_of_inserted_fullHorizon
      (uniqueness_toA02 F.reference) F.scaling.correction.margin_pos ht₁
      (F.velocity ε) (F.pressure ε)
      (F.velocity_smooth ε hε) (F.pressure_smooth ε hε) (F.initial ε hε)
      (F.incompressible ε hε) (F.momentum ε hε)
      (by intro t h0 h1 x
          show F.velocity ε (t, x) = F.reference.velocity (t, x)
          rw [href]; exact F.history ε hε t h0 h1 x)
      (by intro t ht
          show tsupport (fun x => F.velocity ε (t, x) - F.reference.velocity (t, x)) ⊆ _
          rw [href]; exact F.velocityDifference_support ε hε t ht)
      (by intro t ht
          show tsupport (fun x => F.pressure ε (t, x) - F.reference.pressure (t, x)) ⊆ _
          rw [hrefp]; exact F.pressureDifference_support ε hε t ht)
      F.scaling.correction.time_pos
  exact ⟨maximalPartial_ofA02 w, hv, hp⟩

/-- **`(u_ε, p_ε)` is the maximal classical solution** of `(ν, a, g_ε)`, in the
registered Data/V2 vocabulary.  Five lines from `lifespan_eq` (needing only `hg`)
and `sol_on_shorter`, since the `IsMaximalSolution` predicate quantifies its
solution clause strictly below `T^ν_{max,R} = T`. -/
theorem isMaximalSolution_of_inserted (hg : Data.MemForceR F.g)
    (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Contracts.V2.MaximalPartial.IsMaximalSolution ν F.a (F.force ε)
      (F.velocity ε) (F.pressure ε) := by
  have hlife := lifespan_eq F hg hε
  refine ⟨hlife ▸ ENNReal.ofReal_pos.mpr F.scaling.correction.time_pos,
    fun S hS0 hSlt => ?_⟩
  rw [hlife] at hSlt
  exact sol_on_shorter F hε S hS0
    ((ENNReal.ofReal_lt_ofReal_iff F.scaling.correction.time_pos).mp hSlt)

end BlowupDensity.Bindings.InsertionLifespan
