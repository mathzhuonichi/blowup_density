import Contracts.V1.TorusLocalTheory
import Contracts.V1.MaximalPartial
import Contracts.V1.Correction
import Contracts.V1.MainThresholds
import Contracts.V1.CompletedDensity

/-!
# T19 draft A: the density package on `T³`
# (`prop:density`, `cor:mixed`, `cor:closure`, `prop:projection`)

Statement-only, double-blind **draft A** of the T19 node
(`collaboration/SECTION3_PLAN.md` §3, row T19).  This file contains no proofs.
It renders, clause by clause, the four results of the density subsection of
`paper/sections/03-torus.tex`:

* `PeriodicDensityAPI`  — `prop:density`, density for each fixed initial
  velocity (`:349-382`);
* `MixedRegionAPI`      — `cor:mixed`, the sufficient mixed-norm region
  `3/p+2/q>3` (`:528-539`);
* `StrongClosureAPI`    — `cor:closure`, strong closure in energy and
  dissipation (`:540-563`);
* `ProjectionAPI`       — `prop:projection`, projection of extended singular
  data, quantifier order `∀a∃f` (`:564-631`).

Each structure carries one field per clause of the paper *statement and proof*;
each field cites `03-torus.tex:<line>`, states the exact quantifier order, and
carries a non-vacuity note.  Every field is a concrete statement in the
registered T10/T11 vocabulary (`Contracts/V1/TorusData.lean`,
`Contracts/V1/TorusLocalTheory.lean`, `Contracts/V1/MaximalPartial.lean`,
`Contracts/V1/Data.lean`, `Contracts/V1/Correction.lean` `alpha`) plus the
small unregistered torus mixed/Sobolev *carrier* block copied verbatim from
`research/T18/Spec.lean`.  All four structures are **`Prop`-valued**: each of the
four results is a pure `∀∃` statement that exports no distinguished constant or
datum at the T19 level (the packet/scaling/correction constants `M`, `D`,
`C_{p,q}`, `C_s` all live inside T18's `PeriodicInsertionAPI`, and the smallness
constant `c` inside T20's `prop:critical`; T19 only consumes their conclusions).

## What T19 consumes, and what is *not* copied

The proofs of all four results use `thm:insertion` (T18) in the regular-reference
case and `prop:local` (T11) for the dichotomy on `T_max`.  Following the shape of
the *registered Section 4 counterparts* `MainThresholdsAPI.regularReferenceApproximation`
(`Contracts/V1/MainThresholds.lean`) and
`CompletedDensityAPI.strongTrajectoryClosure` (`Contracts/V1/CompletedDensity.lean`),
which spell the insertion output out directly in registered vocabulary rather
than re-exporting the whole insertion record, the regular-reference fields here
name the *conclusions* of `thm:insertion` (`force ε ∈ forceClassT`, exact
`maximalLifespanT = ofReal T`, the closeness limits) in the registered torus
vocabulary.  T18's `PeriodicInsertionAPI` / `periodicInsertionStatement` — and
the whole T13/T14/T15/T16/T17 machinery they carry — are therefore *not* copied
here (copying them verbatim would drag in the entire ≈1900-line T18 chain, none
of whose interior objects T19 reasons about).  The precise T18/T11 fields each
proof will consume are tabulated in `research/T19/COMPARISON_A.md`.  T20
(`prop:critical`) is **not** consumed by T19: it feeds `cor:nondensity`, which is
node T21, so no T20 vocabulary is copied (`SECTION3_PLAN.md` rows T19/T21).

The threshold is the torus value `s_c = 1/2` (`03-torus.tex:351`,
`SECTION3_PLAN.md` §4: only `q = 1`).  Numerically `1/2 = criticalOrder 1`
(`Contracts/V1/Data.lean` `criticalOrder`, `MainThresholdsAPI.thresholdValues`),
but the paper writes `s < 1/2` literally, so the fields do too.
-/

noncomputable section

namespace BlowupDensity.T19.DraftA

open Set Filter Topology MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal Topology BigOperators

/-! ## 0. Copied carrier vocabulary (unregistered torus mixed/Sobolev honesty guards)

The torus mixed-Lebesgue norm and the two Bochner-path honesty predicates are
*not* registered (only the whole-space `Data.mixedLebesgueENorm` is).  They are
needed to state `cor:mixed` in the relative `L^q(0,∞;L^p(T³))` topology and to
make the closeness limits non-vacuous.  Copied verbatim (T13 copy policy: same
names, delimited block, provenance comment) so the file is self-contained. -/

-- copied verbatim from research/T18/Spec.lean:396-433
-- (torus mixed/Sobolev carriers; dependencies resolve through the registered
--  Contracts.V1.TorusData / .TorusLocalTheory / .Data imports above)

/-- `03-torus.tex:129-133`: `G(t)` is the normalized-Haar `L^p(T³)`
slice of the periodic physical field. -/
def IsPeriodicLebesgueSlicePath (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) (G : ℝ → Lp Space p periodicTorusMeasure) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    (G t : PeriodicTorus → Space) =ᵐ[periodicTorusMeasure]
      torusLift (fun x ↦ f (t, x))

/-- `03-torus.tex:129-133`: the torus
`L^q(0,∞;L^p(T³))` extended norm. -/
def mixedLebesgueENormT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → Lp Space p periodicTorusMeasure //
      IsPeriodicLebesgueSlicePath p f G ∧
        AEStronglyMeasurable G forceTimeMeasure},
    eLpNorm G.1 q forceTimeMeasure

/-- `03-torus.tex:129-133`: an honest torus mixed Bochner path; this guard
prevents the mixed identity from degenerating to `⊤=⊤`. -/
def MemMixedLebesgueT (q p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → Lp Space p periodicTorusMeasure,
    IsPeriodicLebesgueSlicePath p f G ∧ MemLp G q forceTimeMeasure

/-- `03-torus.tex:133-138`: an honest periodic Sobolev Bochner path; the
registered `IsPeriodicDatum` includes Haar integrability. -/
def MemForceSobolevT (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : Prop :=
  ∃ G : ℝ → PeriodicSobolev s,
    IsPeriodicSobolevPath s f G ∧ MemLp G q forceTimeMeasure

-- end copied block

/-! ## 1. Local abbreviations for the paper's sets and one norm

`prop:density`'s breakdown set `B_{ν,a,T}` is the registered `breakdownSetT`.
The trajectory sets `R_{a,T}`/`S_{a,T}` of `cor:closure`, the extended data set
`𝔅_{ν,T}` of `prop:projection`, and the `L²(0,T;L²(T³))` quantity used in the
`cor:closure` norm-equivalence are the paper's own objects, restated over the
registered vocabulary (they are *not* stubs of any imported record). -/

/-- `03-torus.tex:544-545` `cor:closure`: `R_{a,T}`, the trajectories with
initial velocity `a` and force in `𝓕` smooth through `T` — i.e. the velocity of
some classical solution that is regular through `T`
(`RegularThroughT`, a solution on `[0,T+δ)` for some `δ>0`). -/
def RegularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ) (u : SpaceTimeField) :
    Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : ClassicalSolutionT ν a g (T + δ), w.velocity = u

/-- `03-torus.tex:545-547` `cor:closure`: `S_{a,T}`, the trajectories with
initial velocity `a`, force in `𝓕` smooth on `[0,T)` (a classical solution on the
horizon `T`), finite energy norm `E_T`, and unbounded maximum velocity at `T`.
Unboundedness is the registered ess-sup form
`limsupLeft T (t ↦ speedENorm (u(t,·))) = ⊤`
(`Contracts/V1/MaximalPartial.lean`). -/
def SingularTrajectoryT (ν : ℝ) (a : SpatialField) (T : ℝ) (u : SpaceTimeField) :
    Prop :=
  ∃ g : SpaceTimeField, g ∈ forceClassT ∧
    (∃ w : ClassicalSolutionT ν a g T, w.velocity = u) ∧
    energyENormT T u ≠ ⊤ ∧
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => u (t, x))) = ⊤

/-- `03-torus.tex:566-568` `prop:projection`: the extended singular-data set
`𝔅_{ν,T} = {(a,f) ∈ 𝓧×𝓕 : T_max^ν(a,f) ≤ T}`. -/
def extendedBreakdownSetT (ν T : ℝ) : Set (SpatialField × SpaceTimeField) :=
  {p | p.1 ∈ initialClassT ∧ p.2 ∈ forceClassT ∧
    maximalLifespanT ν p.1 p.2 ≤ ENNReal.ofReal T}

/-- `03-torus.tex:555-556` `cor:closure`: the torus `L²(0,T;L²(T³))` extended
norm, the left-hand side of the time-embedding inequality used to identify the
`E_T` metric with the `L²_tH¹_x` sum norm. -/
def spaceTimeL2L2ENormT (T : ℝ) (z : SpaceTimeField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (torusLift (fun x => z (t, x))) 2 periodicTorusMeasure) ^ (2 : ℝ))
    ^ ((2 : ℝ)⁻¹)

/-! ## 2. `prop:density` (`03-torus.tex:349-382`) -/

/-- **`prop:density` — density for each fixed initial velocity,
`paper/sections/03-torus.tex:349-357`, proof `:358-380`.**

For `a ∈ 𝓧`, `ν>0`, `T>0`, `s<1/2`: every force `g ∈ 𝓕` is approximated in the
relative `L^1_tH^s_x` topology by a force whose maximal lifespan is at most `T`.
`Prop`-valued: the statement exports no datum or constant (the constants are
internal to `thm:insertion`). -/
structure PeriodicDensityAPI : Prop where
  /-- `03-torus.tex:351-357`, the whole proposition: for `a ∈ 𝓧`, `ν>0`, `T>0`
  and `s<1/2`, the breakdown set `B_{ν,a,T}` is relatively dense in `𝓕` for the
  `L^1_tH^s_x` pseudometric.  Registered `RelativelyDenseT 1 s forceClassT
  (breakdownSetT ν a T)` unfolds to exactly the paper's
  `∀ g∈𝓕 ∀ρ>0 ∃f: ‖f-g‖_{L^1_tH^s} < ρ ∧ T_max^ν(a,f) ≤ T`
  (`f ∈ breakdownSetT` is `f∈𝓕 ∧ maximalLifespanT ν a f ≤ ofReal T`).

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ s, s<1/2 →`
  density.  `1/2 = criticalOrder 1` (the torus fixes `q=1`, `SECTION3_PLAN.md`
  §4), written literally as `03-torus.tex:351`.

  Non-vacuity: the conclusion is the registered positive-radius density
  predicate, whose distance is the fail-safe `ℝ≥0∞` norm `forceSobolevENormT`,
  and whose witness must live in the registered breakdown set — never `True`. -/
  density :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

  /-- `03-torus.tex:360-363`, the first (already-singular) case of the
  dichotomy: "If `T_max^ν(a,g) ≤ T`, choose `f=g`.  It already belongs to
  `B_{ν,a,T}` and the norm difference is zero."  Rendered as the density
  conclusion witnessed by `f=g`: the zero-difference force is an admissible
  breakdown approximant at every radius.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `maximalLifespanT ν a g ≤ ofReal T → ∀ s, ∀ r, 0<r →`.

  Non-vacuity: the witness `f` lies in `breakdownSetT ν a T` and the strict
  bound forces `forceSobolevENormT 1 s 0 = 0 < r` (norm of the zero field), a
  genuine `ℝ≥0∞` fact, not a definitional identity. -/
  alreadySingularApprox :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          maximalLifespanT ν a g ≤ ENNReal.ofReal T →
            ∀ s : ℝ, ∀ r : ℝ≥0∞, 0 < r →
              ∃ f ∈ breakdownSetT ν a T,
                forceSobolevENormT 1 s (fun z => f z - g z) < r

  /-- `03-torus.tex:364-380`, the second (regular-reference) case: "If
  `T_max^ν(a,g) > T`, choose `δ>0` with `T+δ<T_max`, use its smooth solution as
  reference in `thm:insertion`.  For every sufficiently small `ε`, that theorem
  supplies `g_ε ∈ B_{ν,a,T}` with lifespan exactly `T`; `eq:Hsclose` tends to
  zero for `0≤s<1/2`, and its `s=0` case plus `L²↪H^s` for `s<0`."  One inserted
  force family `f = g_ε`, valid across all admissible `s`.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `ofReal T < maximalLifespanT ν a g → ∃ ε₀, 0<ε₀ ∧ ∃ f, (per-ε) ∧`
  `(0≤s<1/2 limits) ∧ (s<0 limits)`.

  TORUS/proof distinction (`03-torus.tex:625-631`): the family has lifespan
  *exactly* `T` (`= ofReal T`), stronger than the `≤` that `density` asserts —
  `thm:insertion` gives singularity exactly at `T` about a regular reference,
  whereas `density` only needs breakdown *by* `T`.

  Non-vacuity: for each `ε ∈ (0,ε₀)` the inserted force is a genuine element of
  `forceClassT`, the difference has a strongly-measurable finite `H^s` path
  (`MemForceSobolevT`, the honesty guard that keeps the `⨅`-norm limit
  meaningful), the maximal lifespan equals `ofReal T`, and `T` carries a full
  classical solution; the two `Tendsto` conjuncts are limits of registered
  `ℝ≥0∞` norms along the nontrivial filter `𝓝[>]0`. -/
  regularReferenceApprox :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ENNReal.ofReal T < maximalLifespanT ν a g →
            ∃ ε₀ : ℝ, 0 < ε₀ ∧
              ∃ f : ℝ → SpaceTimeField,
                (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                  f ε ∈ forceClassT ∧
                  (fun z => f ε z - g z) ∈ forceClassT ∧
                  maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                  Nonempty (ClassicalSolutionT ν a (f ε) T)) ∧
                (∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    MemForceSobolevT 1 s (fun z => f ε z - g z)) ∧
                  Tendsto
                    (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))) ∧
                (∀ s : ℝ, s < 0 →
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    MemForceSobolevT 1 s (fun z => f ε z - g z)) ∧
                  Tendsto
                    (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)))

/-- **`prop:density` in the paper's quantifier order,
`03-torus.tex:351-357`.**  The headline proposition; equals field
`PeriodicDensityAPI.density`. -/
def periodicDensityStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

/-! ## 3. `cor:mixed` (`03-torus.tex:528-539`) -/

/-- **`cor:mixed` — a sufficient mixed-norm region,
`paper/sections/03-torus.tex:528-534`, proof `:535-538`.**

For fixed `a ∈ 𝓧`, `B_{ν,a,T}` is dense in `𝓕` for the relative
`L^q(0,∞;L^p(T³))` topology whenever `1≤p,q≤∞` and `3/p+2/q>3`.  `Prop`-valued
for the same reason as `prop:density`. -/
structure MixedRegionAPI : Prop where
  /-- `03-torus.tex:536-537`, the proof's arithmetic driver: the region
  `3/p+2/q>3` (with `ℝ≥0∞.toReal ∞ = 0`) is exactly `α(p,q)>0`, and then
  `α(p,q)+1>0`.  `α(p,q) = alpha p q = -3+3/p.toReal+2/q.toReal`
  (`Contracts/V1/Correction.lean`), the `ε`-exponent of `eq:Fclose`.  This
  mirrors `MainThresholdsAPI.thresholdValues`/`R41.threshold_arithmetic`.

  Exact quantifier order: `∀ p q : ℝ≥0∞, region →`.

  Non-vacuity: both conjuncts are explicit strict inequalities on the registered
  exponent `alpha`, which drives `eq:Fclose = C_{p,q}(ε^{α}+ε^{α+1}) → 0`. -/
  mixedRegionArithmetic :
    ∀ p q : ℝ≥0∞, 3 < 3 / p.toReal + 2 / q.toReal →
      0 < BlowupDensity.Contracts.V1.alpha p q ∧
        0 < BlowupDensity.Contracts.V1.alpha p q + 1

  /-- `03-torus.tex:530-534`, the corollary itself: for `a ∈ 𝓧`, `ν>0`, `T>0`,
  and every `(p,q)` in the region `1≤p,q≤∞`, `3/p+2/q>3`, the breakdown set is
  relatively dense in `𝓕` for the `L^q_tL^p_x` pseudometric.  Written directly
  (there is no registered `RelativelyDense`-in-mixed predicate): every `g∈𝓕` and
  radius `r>0` yield `f ∈ B_{ν,a,T}` with `mixedLebesgueENormT q p (f-g) < r`.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T →`
  `∀ (p q : ℝ≥0∞) [Fact (1≤p)], 1≤q → 3/p+2/q>3 → ∀ g, g∈𝓕 → ∀ r, 0<r →`.
  `[Fact (1≤p)]` supplies `1≤p` (needed by the norm) and `p≤∞` is automatic in
  `ℝ≥0∞`; `1≤q` is explicit; the `∞` endpoints are included exactly as `:531`.

  Non-vacuity: the distance is the copied torus mixed norm `mixedLebesgueENormT`,
  and `< r` forces it finite, so the witness `f` is a real breakdown force whose
  mixed difference is genuinely small. -/
  mixedDensity :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          3 < 3 / p.toReal + 2 / q.toReal →
            ∀ g : SpaceTimeField, g ∈ forceClassT →
              ∀ r : ℝ≥0∞, 0 < r →
                ∃ f ∈ breakdownSetT ν a T,
                  mixedLebesgueENormT q p (fun z => f z - g z) < r

  /-- `03-torus.tex:535`, the already-singular case (same as `prop:density`):
  when `T_max^ν(a,g) ≤ T`, the reference `g` is itself the breakdown approximant
  and the mixed distance to it is zero.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `maximalLifespanT ν a g ≤ ofReal T → ∀ (p q) [Fact (1≤p)], 1≤q → ∀ r, 0<r →`.

  Non-vacuity: the witness lies in `breakdownSetT` and `mixedLebesgueENormT q p
  0 = 0 < r`, a genuine `ℝ≥0∞` fact about the zero field. -/
  alreadySingularMixedApprox :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          maximalLifespanT ν a g ≤ ENNReal.ofReal T →
            ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
              ∀ r : ℝ≥0∞, 0 < r →
                ∃ f ∈ breakdownSetT ν a T,
                  mixedLebesgueENormT q p (fun z => f z - g z) < r

  /-- `03-torus.tex:535-538`, the regular-reference case with `eq:Fclose`: for
  a reference regular past `T` (`ofReal T < maximalLifespanT`), one inserted force
  family `g_ε ∈ B_{ν,a,T}` has lifespan exactly `T`, and — because `α(p,q)>0`
  (hence `α(p,q)+1>0`) on the region — its mixed difference to `g` tends to zero.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `ofReal T < maximalLifespanT ν a g → ∃ ε₀, 0<ε₀ ∧ ∃ f, (per-ε) ∧`
  `(∀ (p q) [Fact (1≤p)], 1≤q → region → honesty ∧ Tendsto)`.

  Non-vacuity: the same inserted family serves every admissible `(p,q)`; each has
  an honest torus mixed path (`MemMixedLebesgueT`) so the `⨅`-norm limit is
  meaningful, and the lifespan is the registered `= ofReal T`. -/
  regularReferenceMixedApprox :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ENNReal.ofReal T < maximalLifespanT ν a g →
            ∃ ε₀ : ℝ, 0 < ε₀ ∧
              ∃ f : ℝ → SpaceTimeField,
                (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                  f ε ∈ forceClassT ∧
                  maximalLifespanT ν a (f ε) = ENNReal.ofReal T) ∧
                ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
                  3 < 3 / p.toReal + 2 / q.toReal →
                    (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                      MemMixedLebesgueT q p (fun z => f ε z - g z)) ∧
                    Tendsto
                      (fun ε : ℝ => mixedLebesgueENormT q p (fun z => f ε z - g z))
                      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))

/-- **`cor:mixed` in the paper's quantifier order, `03-torus.tex:530-534`.** -/
def mixedRegionStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
        3 < 3 / p.toReal + 2 / q.toReal →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f ∈ breakdownSetT ν a T,
                mixedLebesgueENormT q p (fun z => f z - g z) < r

/-! ## 4. `cor:closure` (`03-torus.tex:540-563`) -/

/-- **`cor:closure` — strong closure in energy and dissipation,
`paper/sections/03-torus.tex:540-552`, proof `:553-562`.**

Fix `a ∈ 𝓧`.  The regular trajectories `R_{a,T}` lie in the `E_T`-closure of the
singular trajectories `S_{a,T}` (`eq:closure`), and every reference pair `(v,g)`
has approximants `(u_ε,g_ε)→(v,g)` in `E_T × L^1_tH^s_x` for `s<1/2`.
`Prop`-valued. -/
structure StrongClosureAPI : Prop where
  /-- `03-torus.tex:555-560`, the norm identification behind `eq:closure`:
  `‖z‖_{L²(0,T;L²)} ≤ T^{1/2} ‖z‖_{L^∞(0,T;L²)}`.  Here the right side is the
  registered `energyEssSupT` (first summand of `E_T`) and the left the copied
  `spaceTimeL2L2ENormT`; together with the shared gradient term this shows `E_T`
  and the `L²_tH^1_x` sum norm control each other, the equivalence "used in
  `eq:closure`".

  Exact quantifier order: `∀ T, 0<T → ∀ z`.

  Non-vacuity: a genuine `ℝ≥0∞` inequality relating two honest space-time norms,
  with the constant `T^{1/2} = Real.sqrt T`; not a tautology. -/
  energyTimeEmbedding :
    ∀ T : ℝ, 0 < T → ∀ z : SpaceTimeField,
      spaceTimeL2L2ENormT T z ≤
        ENNReal.ofReal (Real.sqrt T) * energyEssSupT T z

  /-- `03-torus.tex:546-547` `eq:closure`: `R_{a,T} ⊆ closure(S_{a,T})^{E_T}`.
  Rendered as the `ε`-approximation form of membership in the `E_T`-closure
  (exactly as `RelativelyDenseT` renders density, avoiding a `TopologicalSpace`
  instance): every regular trajectory is `E_T`-approximated by singular
  trajectories.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ u,`
  `RegularTrajectoryT ν a T u → ∀ r, 0<r → ∃ u', SingularTrajectoryT ∧ dist<r`.

  Non-vacuity: `u'` is a genuine singular trajectory (finite `E_T`, unbounded
  speed at `T`) and the distance is the registered `energyENormT` of the actual
  difference; `RegularTrajectoryT`/`SingularTrajectoryT` are the paper's `R`/`S`
  spelled over registered classical solutions. -/
  closureInEnergy :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
              energyENormT T (fun z => u z - u' z) < r

  /-- `03-torus.tex:548-552`, simultaneous pair convergence: for each reference
  pair `(v,g)` — `g∈𝓕` regular through `T`, `v` its velocity — and every fixed
  `s<1/2`, there are approximating pairs `(u_ε,g_ε)` with `u_ε` a singular
  trajectory (`g_ε∈𝓕`, lifespan exactly `T`, `u_ε` its velocity, finite `E_T`,
  blow-up at `T`) such that `u_ε→v` in `E_T` and `g_ε→g` in `L^1_tH^s_x`
  simultaneously.  Mirrors `CompletedDensityAPI.strongTrajectoryClosure`.

  Exact quantifier order: `∀ a, a∈𝓧 → ∀ ν, 0<ν → ∀ T, 0<T → ∀ g, g∈𝓕 →`
  `∀ δ, 0<δ → ∀ reference : ClassicalSolutionT ν a g (T+δ) → ∃ ε₀, 0<ε₀ ∧`
  `∃ u f, (per-ε) ∧ (E_T limit) ∧ (∀ s<1/2, L^1_tH^s limit)`.

  Non-vacuity: the single family `(u,f)` witnesses both limits; each `u ε` is a
  registered `SingularTrajectoryT`, the two limits are of registered `ℝ≥0∞`
  norms along `𝓝[>]0`, and the reference velocity `v = reference.velocity` is an
  actual regular trajectory (so the pair really lies in `R_{a,T}`). -/
  simultaneousPairConvergence :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              ∃ ε₀ : ℝ, 0 < ε₀ ∧
                ∃ u f : ℝ → SpaceTimeField,
                  (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                    f ε ∈ forceClassT ∧
                    maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                    (∃ w : ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧
                    SingularTrajectoryT ν a T (u ε)) ∧
                  Tendsto
                    (fun ε : ℝ =>
                      energyENormT T (fun z => u ε z - reference.velocity z))
                    (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) ∧
                  (∀ s : ℝ, s < 1 / 2 →
                    Tendsto
                      (fun ε : ℝ => forceSobolevENormT 1 s (fun z => f ε z - g z))
                      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)))

/-- **`cor:closure` `eq:closure` in the paper's quantifier order,
`03-torus.tex:544-547`.**  The `E_T`-closure inclusion `R_{a,T} ⊆ S̄_{a,T}`. -/
def strongClosureStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ u : SpaceTimeField, RegularTrajectoryT ν a T u →
        ∀ r : ℝ≥0∞, 0 < r →
          ∃ u' : SpaceTimeField, SingularTrajectoryT ν a T u' ∧
            energyENormT T (fun z => u z - u' z) < r

/-! ## 5. `prop:projection` (`03-torus.tex:564-631`) -/

/-- **`prop:projection` — projection of extended singular data,
`paper/sections/03-torus.tex:564-572`, proof `:573-580`, remarks `:582-590`.**

`𝔅_{ν,T} = {(a,f)∈𝓧×𝓕 : T_max^ν(a,f) ≤ T}` is dense (for `s<1/2`) in the product
of any topology on `𝓧` with the relative `L^1_tH^s_x` topology on `𝓕`; its
projection onto `𝓧` is all of `𝓧`; the `a=0` subfamily projects to `{0}`.  The
quantifier order is `∀a∃f` (`:582-585`).  `Prop`-valued. -/
structure ProjectionAPI : Prop where
  /-- `03-torus.tex:568-570,573-577`, density in the product topology.  A basic
  product neighborhood of `(a,g)` is `U×V` with `U` any `𝓧`-neighborhood of `a`
  and `V` an `L^1_tH^s_x` ball; since `a∈U` always, the paper keeps the same `a`
  and (by `prop:density`) picks `f∈V` with `T_max^ν(a,f)≤T`, i.e.
  `(a,f)∈𝔅_{ν,T}∩(U×V)`.  Rendered by keeping the initial datum fixed at `a`
  (its own point lies in every topology's neighborhood) and approximating only
  the force factor.

  Exact quantifier order: `∀ ν, 0<ν → ∀ T, 0<T → ∀ s, s<1/2 → ∀ a, a∈𝓧 →`
  `∀ g, g∈𝓕 → ∀ r, 0<r → ∃ f`.

  Non-vacuity: the produced pair `(a,f)` lies in `extendedBreakdownSetT ν T`
  (so `a∈𝓧`, `f∈𝓕`, `T_max≤T`) and the force distance is the registered
  `forceSobolevENormT`, strictly below `r`. -/
  extendedProductDensity :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 1 / 2 →
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ g : SpaceTimeField, g ∈ forceClassT →
            ∀ r : ℝ≥0∞, 0 < r →
              ∃ f : SpaceTimeField,
                (a, f) ∈ extendedBreakdownSetT ν T ∧
                  forceSobolevENormT 1 s (fun z => f z - g z) < r

  /-- `03-torus.tex:570,577-578`, "its projection onto `𝓧` is all of `𝓧`", the
  `∀a∃f` statement (`:582-585`): the image of `𝔅_{ν,T}` under `Prod.fst` is
  exactly `𝓧 = initialClassT`.  `⊆` is by construction (`𝔅 ⊆ 𝓧×𝓕`); `⊇` is the
  content — applying `prop:density` with any fixed `g` and radius gives at least
  one singular force over each `a`.

  Exact quantifier order: `∀ ν, 0<ν → ∀ T, 0<T →` set equality.

  Non-vacuity: the `⊇` inclusion of the image equality asserts, for every
  `a∈𝓧`, existence of `f` with `(a,f)∈𝔅_{ν,T}` — the genuine `∀a∃f`, not a
  vacuous image. -/
  projectionOntoInitialData :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT

  /-- `03-torus.tex:571-572,579`, "the family obtained while requiring `a=0`
  projects instead to the singleton `{0}`": the image under `Prod.fst` of the
  `a=0` subfamily of `𝔅_{ν,T}` equals `{0}`.  `⊆` is the constraint; `⊇`
  requires a singular force over `a=0` (`0∈𝓧`, `prop:density` at `a=0`).

  Exact quantifier order: `∀ ν, 0<ν → ∀ T, 0<T →` set equality.

  Non-vacuity: the `⊇` direction forces the `a=0` subfamily nonempty (a real
  singular force over `0`), so the projection is the nonempty singleton `{0}`,
  not the empty set. -/
  zeroInitialProjection :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst ''
          {p : SpatialField × SpaceTimeField |
            p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
        {(fun _ => 0 : SpatialField)}

/-- **`prop:projection` in the paper's quantifier order, `03-torus.tex:566-572`.**
Density of `𝔅_{ν,T}` in the product topology (force factor, initial datum kept)
together with the full projection onto `𝓧`. -/
def projectionStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
    (∀ s : ℝ, s < 1 / 2 →
      ∀ a : SpatialField, a ∈ initialClassT →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ r : ℝ≥0∞, 0 < r →
            ∃ f : SpaceTimeField,
              (a, f) ∈ extendedBreakdownSetT ν T ∧
                forceSobolevENormT 1 s (fun z => f z - g z) < r) ∧
    Prod.fst '' (extendedBreakdownSetT ν T) = initialClassT

end BlowupDensity.T19.DraftA
