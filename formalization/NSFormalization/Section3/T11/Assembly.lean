import NSFormalization.Section3.T11.ExistenceInputH3
import NSFormalization.Section3.T11.ClassicalRegularity
import NSFormalization.Section3.T11.PairingBound

/-!
# T11 / U17 — the four public periodic local-theory APIs, assembled

`research/T11/Spec.lean` and `research/T11/probes/api_on_canonical.lean` fix
five structures over the canonical T10/T11 vocabulary.  This module states four
of them (`PeriodicLocalRegularity` is already in
`Section3/T11/LocalTheory.lean`) and supplies a term for each, drawing every
field from a named theorem of the units:

| structure | field | source |
|---|---|---|
| `PeriodicLocalTheoryAPI` | `horizon`, `solution` | §1 below, from `ExistenceInputH3.exists_periodicLocalSolution_unconditional` (U9e) |
| | `regularity` | `ClassicalRegularity.regularity_of_solution` (U6b) |
| | `velocity_unique`, `pressure_unique`, `horizon_le_lifespan` | `Uniqueness` (U5) |
| | `exists_maximal` | `ExistenceInputH3.exists_maximal_unconditional` (U15 + U9e) |
| | `maximal_unique` | `Maximal.maximal_unique` (U15) |
| `PeriodicContinuationH3API` | `restart`, `restartBeyond`, `extendsBeyond`, `lifespanInfiniteOfLocallyFinite` | `ExistenceInputH3` (U9e re-instantiating U10/U13/U14/U16) |
| | `higherOrderBound` | `PairingBound.torusHigherOrderBound` (U12) |
| `PeriodicMeanReductionAPI` | `mean_formula`, `mean_derivative` | `MeanIdentity` (U7) |
| | `transformed_solution` | `ClassicalRegularity.transformed_solution` (U6/U6b) |
| | `transformed_classes`, `transformed_mean_zero`, `translation_preserves_sobolev` | `GalileanClasses` (U3) |
| `PeriodicViscosityRescalingAPI` | `scaled_classes`, `inverse_identities` | `Rescaling` (U4) |
| | `to_unit`, `from_unit` | `ClassicalRegularity` (U6/U6b) |

## The one narrowing: `H³` instead of `H¹` restart balls

`research/T11/LEAD_AMENDMENTS.md` amendment 2 and `research/T11/H1_GAP.md`.
The specification's `PeriodicContinuationAPI.restart` and `.restartBeyond`
quantify over an `H¹` ball of data.  The Picard machinery of this tree runs in
the two-space pair `H³ × H²`, so the horizon it produces is uniform over an
`H³` ball only; uniformity over an `H¹` ball is the subcritical Fujita–Kato
local theory, which is nowhere in the tree.  Accordingly:

* `PeriodicContinuationH3API` is the specification structure with the two `H¹`
  balls replaced by `H³` balls and **nothing else changed**; it is proved
  outright (`periodicContinuationH3API`).
* `PeriodicRestartH1` and `PeriodicRestartBeyondH1` are the manuscript's two
  fields kept **verbatim** as named predicates.  They are documented, not
  proved, and no theorem below claims them — exactly the treatment Section 4
  gave `ManuscriptHorizonLowerBoundH1` (`Contracts/V2/LocalTheory.lean:193`).
* `periodicContinuationAPI_of_h1` derives the specification's
  `PeriodicContinuationAPI` from those two named predicates together with the
  three proved ball-free fields, exhibiting exactly what is missing and nothing
  more.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators

/-! ## 1. The selected local horizon and solution

`Restart.periodicLocalHorizonOfInput` and its companions are parametrized by
the named `H¹` input `PeriodicQuantitativeLocalInput'`, which is open.  The same
selection is performed here from lane 338's unconditional existence theorem, so
the resulting horizon and solution carry no hypothesis. -/

/-- The jointly selected horizon and classical solution at admissible
parameters, chosen once by `Classical.choice`. -/
noncomputable def periodicLocalChoiceU (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT) :
    Σ δ : ℝ, ClassicalSolutionT ν a f δ := by
  let hex := exists_periodicLocalSolution_unconditional ν hν a ha f hf
  exact ⟨Classical.choose hex, Classical.choose (Classical.choose_spec hex).2⟩

/-- The selected common local horizon.  Its value is `1` away from the
admissible input class; those values are never consumed by the dependent
`solution` field. -/
noncomputable def periodicLocalHorizon (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) : ℝ := by
  classical
  exact if h : 0 < ν ∧ a ∈ initialClassT ∧ f ∈ forceClassT then
      (periodicLocalChoiceU ν h.1 a h.2.1 f h.2.2).1
    else 1

theorem periodicLocalHorizon_eq {ν : ℝ} (hν : 0 < ν) {a : SpatialField}
    (ha : a ∈ initialClassT) {f : SpaceTimeField} (hf : f ∈ forceClassT) :
    periodicLocalHorizon ν a f = (periodicLocalChoiceU ν hν a ha f hf).1 := by
  classical
  unfold periodicLocalHorizon
  split
  · rfl
  · rename_i h
    exact False.elim (h ⟨hν, ha, hf⟩)

/-- The selected classical solution, transported to the public horizon. -/
noncomputable def periodicLocalSolution (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT) :
    ClassicalSolutionT ν a f (periodicLocalHorizon ν a f) := by
  rw [periodicLocalHorizon_eq hν ha hf]
  exact (periodicLocalChoiceU ν hν a ha f hf).2

/-- The selected horizon is positive at admissible parameters. -/
theorem periodicLocalHorizon_pos {ν : ℝ} (hν : 0 < ν) {a : SpatialField}
    (ha : a ∈ initialClassT) {f : SpaceTimeField} (hf : f ∈ forceClassT) :
    0 < periodicLocalHorizon ν a f :=
  (periodicLocalSolution ν hν a ha f hf).horizon_pos

/-! ## 2. `PeriodicLocalTheoryAPI` -/

/-- `02-preliminaries.tex:32-34,105-109,116-118` and
`appendix-a-local-theory.tex:60-77,117-125`: periodic local existence,
uniqueness, and maximal gluing.  This structure is `Type`-valued because it
carries the selected horizon as data.  Stated verbatim from
`research/T11/Spec.lean:571-670`. -/
structure PeriodicLocalTheoryAPI : Type where
  /-- `02-preliminaries.tex:105-109` and `appendix-a-local-theory.tex:60-70`:
  the selected common local horizon.  Exact argument order: `ν`, `a`, `f`. -/
  horizon : ℝ → SpatialField → SpaceTimeField → ℝ
  /-- `02-preliminaries.tex:105-109`: local existence for exactly
  `∀ν, 0<ν → ∀a∈initialClassT, ∀f∈forceClassT`. -/
  solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ClassicalSolutionT ν a f (horizon ν a f)
  /-- `02-preliminaries.tex:116-118` and `appendix-a-local-theory.tex:65-77`:
  all three regularity clauses hold for the selected solution on that same
  horizon. -/
  regularity : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f (horizon ν a f)
        (solution ν hν a ha f hf)
  /-- `02-preliminaries.tex:105-109` and `appendix-a-local-theory.tex:117-124`:
  velocity uniqueness on the common interval. -/
  velocity_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x)
  /-- `02-preliminaries.tex:28,84-88,105-109`: the zero-mean gauge upgrades
  pressure uniqueness to literal equality. -/
  pressure_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x)
  /-- `02-preliminaries.tex:32-34`: the selected local horizon lies below the
  concrete supremal lifespan. -/
  horizon_le_lifespan : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f
  /-- `02-preliminaries.tex:32-34,105-109` and
  `appendix-a-local-theory.tex:123-125`: local solutions glue to a maximal
  velocity and normalized pressure. -/
  exists_maximal : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p
  /-- `02-preliminaries.tex:105-109` and
  `appendix-a-local-theory.tex:117-125`: maximal pairs agree at every
  presingular time. -/
  maximal_unique : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u₁ p₁ →
          IsMaximalPeriodicSolution ν a f u₂ p₂ →
            ∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal t < maximalLifespanT ν a f →
                ∀ x : Space,
                  u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x)

/-- **The eight-field periodic local theory, proved.**  No field is a named
input and no field is a placeholder proposition. -/
noncomputable def periodicLocalTheoryAPI : PeriodicLocalTheoryAPI where
  horizon := periodicLocalHorizon
  solution := periodicLocalSolution
  regularity := regularity_of_solution periodicLocalHorizon periodicLocalSolution
  velocity_unique := velocity_unique
  pressure_unique := pressure_unique
  horizon_le_lifespan := horizon_le_lifespan periodicLocalSolution
  exists_maximal := exists_maximal_unconditional
  maximal_unique := maximal_unique

/-! ## 3. Continuation: the manuscript structure, its `H³` narrowing, and the
two named `H¹` predicates -/

/-- `02-preliminaries.tex:105-114` and `appendix-a-local-theory.tex:127-156`:
the manuscript-strength periodic continuation package, retaining the `H¹`
restart ball.  Stated verbatim from `research/T11/Spec.lean:677-766`.  Three of
its five fields are proved below; the two ball-carrying ones are open
(`research/T11/H1_GAP.md`). -/
structure PeriodicContinuationAPI : Prop where
  /-- `appendix-a-local-theory.tex:146-151`: for one fixed force and compact
  restart window, one positive duration works for every restart time and every
  admissible datum in a finite `H¹` ball. -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
  /-- `appendix-a-local-theory.tex:127-147`: a finite squared-`H²` integral and
  Grönwall bound every integer Sobolev order uniformly below `S`. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M
  /-- `appendix-a-local-theory.tex:146-153`: a uniform `H¹` trajectory bound
  supplies one fixed positive restart margin and an exactly patched
  solution. -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x))
  /-- `02-preliminaries.tex:109-114` eq:criterion and
  `appendix-a-local-theory.tex:127-156`: finite squared-`H²` integral implies
  concrete extension beyond the real endpoint `S`. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p
  /-- `02-preliminaries.tex:109-114`, `appendix-a-local-theory.tex:124-155`
  and `03-torus.tex:490-502`: local criterion finiteness at every finite
  endpoint at or below a maximal lifespan forces global lifespan. -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤

/-- **The registered narrowing.**  `PeriodicContinuationAPI` with the `H¹`
balls of `restart` and `restartBeyond` replaced by `H³` balls; every other
token, quantifier and hypothesis is unchanged, and the three remaining fields
are the specification's verbatim.  Lead amendment 2. -/
structure PeriodicContinuationH3API : Prop where
  /-- `appendix-a-local-theory.tex:146-151` with the datum ball at order three:
  `periodicSobolevENorm 3 a' ≤ K` in place of `periodicSobolevENorm 1 a' ≤ K`. -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 3 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w
  /-- `appendix-a-local-theory.tex:127-147`, verbatim: this field carries no
  ball at all. -/
  higherOrderBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                ∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M
  /-- `appendix-a-local-theory.tex:146-153` with the trajectory bound at order
  three: `periodicSobolevENorm 3 (u (t, ·)) ≤ K`. -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 3 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x))
  /-- `02-preliminaries.tex:109-114` eq:criterion, verbatim: no ball. -/
  extendsBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p
  /-- `03-torus.tex:490-502`, verbatim: no ball. -/
  lifespanInfiniteOfLocallyFinite : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p →
            (∀ S : ℝ, 0 < S →
              ENNReal.ofReal S ≤ maximalLifespanT ν a f →
                squaredHTwoIntegralT S u ≠ ⊤) →
              maximalLifespanT ν a f = ⊤

/-- **The manuscript's `H¹` restart sentence; NOT proved here; open.**  This is
`PeriodicContinuationAPI.restart` verbatim, kept as a named predicate exactly as
Section 4 kept `ManuscriptHorizonLowerBoundH1`
(`verification/Contracts/V2/LocalTheory.lean:193`).  Its only difference from
the proved `PeriodicContinuationH3API.restart` is the Sobolev order of the
datum ball, `1` instead of `3`; that downgrade is the subcritical Fujita–Kato
local theory and does not follow from anything in this tree
(`research/T11/H1_GAP.md` §2). -/
def PeriodicRestartH1 : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w

/-- **The manuscript's `H¹` endpoint-restart sentence; NOT proved here; open.**
This is `PeriodicContinuationAPI.restartBeyond` verbatim.  Its only difference
from the proved `PeriodicContinuationH3API.restartBeyond` is the Sobolev order
of the uniform trajectory bound, `1` instead of `3`.  It is derivable from
`PeriodicRestartH1` by lane 332's argument, and is named separately so that a
consumer can see precisely which of the two manuscript sentences it needs
(`research/T11/H1_GAP.md` §1, gaps G2 and G3). -/
def PeriodicRestartBeyondH1 : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x))

/-- **The `H³`-narrowed continuation package, proved.**  Every field comes from
lane 338 (`restart`, `restartBeyond`, `extendsBeyond`,
`lifespanInfiniteOfLocallyFinite`) or lane 336 (`higherOrderBound`); no
hypothesis remains. -/
theorem periodicContinuationH3API : PeriodicContinuationH3API where
  restart := restartH3
  higherOrderBound := torusHigherOrderBound
  restartBeyond := restartBeyondH3
  extendsBeyond := extendsBeyondH3 torusHigherOrderBound
  lifespanInfiniteOfLocallyFinite :=
    lifespanInfiniteOfLocallyFiniteH3 torusHigherOrderBound

/-- **Exactly what the manuscript's continuation package still needs.**  The
specification's `PeriodicContinuationAPI` follows from the two named `H¹`
predicates and nothing else: its other three fields are the ball-free ones,
already proved unconditionally.  This theorem is the honest statement of the
gap, not a proof of it. -/
theorem periodicContinuationAPI_of_h1 (h₁ : PeriodicRestartH1)
    (h₂ : PeriodicRestartBeyondH1) : PeriodicContinuationAPI where
  restart := h₁
  higherOrderBound := torusHigherOrderBound
  restartBeyond := h₂
  extendsBeyond := extendsBeyondH3 torusHigherOrderBound
  lifespanInfiniteOfLocallyFinite :=
    lifespanInfiniteOfLocallyFiniteH3 torusHigherOrderBound

/-! ## 4. `PeriodicMeanReductionAPI` -/

/-- `appendix-a-local-theory.tex:89-106` and `03-torus.tex:395-403`: the exact
periodic mean identities and Galilean reduction.  Stated verbatim from
`research/T11/Spec.lean:811-894`. -/
structure PeriodicMeanReductionAPI : Prop where
  /-- `appendix-a-local-theory.tex:89-93`: the solution mean equals the known
  initial-plus-force mean. -/
  mean_formula : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t
  /-- `appendix-a-local-theory.tex:92-98`: `m'(t)=meanT (f(t,·))` at interior
  times. -/
  mean_derivative : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t
  /-- `appendix-a-local-theory.tex:95-106`: the displayed data-defined Galilean
  fields solve the mean-free equation on the same horizon and retain all stated
  regularity. -/
  transformed_solution : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT ν (meanZeroPartT a) (galileanForceT a f) T,
            v.velocity = galileanVelocityT a f w.velocity ∧
            v.pressure = galileanPressureT a f w.pressure ∧
            PeriodicLocalRegularity ν (meanZeroPartT a)
              (galileanForceT a f) T v
  /-- `appendix-a-local-theory.tex:89-104`: the explicit centered datum and
  data-defined transformed force stay in the manuscript input classes. -/
  transformed_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (_w : ClassicalSolutionT ν a f T),
          meanZeroPartT a ∈ initialClassT ∧
            galileanForceT a f ∈ forceClassT
  /-- `appendix-a-local-theory.tex:97-103`: the centered datum, transformed
  velocity, and transformed force have zero normalized torus mean. -/
  transformed_mean_zero : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          meanT (meanZeroPartT a) = 0 ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanVelocityT a f w.velocity (t, x)) = 0) ∧
            (∀ t ∈ Ico (0 : ℝ) T,
              meanT (fun x ↦ galileanForceT a f (t, x)) = 0)
  /-- `appendix-a-local-theory.tex:102-103`: spatial translations preserve
  every periodic Sobolev norm. -/
  translation_preserves_sobolev : ∀ (s : ℝ) (z : SpatialField),
    IsPeriodicSpatial z → ∀ y : Space,
      periodicSobolevENorm s (fun x ↦ z (x + y)) =
        periodicSobolevENorm s z

/-- **The six-field Galilean mean reduction, proved.** -/
theorem periodicMeanReductionAPI : PeriodicMeanReductionAPI where
  mean_formula := mean_formula
  mean_derivative := mean_derivative
  transformed_solution := transformed_solution
  transformed_classes := transformed_classes
  transformed_mean_zero := transformed_mean_zero
  translation_preserves_sobolev := translation_preserves_sobolev

/-! ## 5. `PeriodicViscosityRescalingAPI` -/

/-- `appendix-a-local-theory.tex:79-87`: equivalence of positive viscosity and
unit viscosity, including class preservation and inverse formulas.  Stated
verbatim from `research/T11/Spec.lean:933-990`. -/
structure PeriodicViscosityRescalingAPI : Prop where
  /-- `appendix-a-local-theory.tex:79-87`: positive-viscosity rescaling
  preserves the stated smooth periodic initial and force classes. -/
  scaled_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT
  /-- `appendix-a-local-theory.tex:86-87`: inverse formulas restore velocity,
  pressure, and force. -/
  inverse_identities : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f
  /-- `appendix-a-local-theory.tex:79-87`: every viscosity-`ν` solution
  rescales to a viscosity-one solution on horizon `νT` with preserved
  regularity. -/
  to_unit : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v
  /-- `appendix-a-local-theory.tex:86-87`: undoing the unit-viscosity change
  restores `ν`, the original data, horizon `T`, and normalized pressure. -/
  from_unit : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ),
          ∀ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            ∃ w : ClassicalSolutionT ν a f T,
              w.velocity = restoreViscosityVelocityT ν v.velocity ∧
              w.pressure = restoreViscosityPressureT ν v.pressure ∧
              PeriodicLocalRegularity ν a f T w

/-- **The four-field positive-viscosity rescaling, proved.** -/
theorem periodicViscosityRescalingAPI : PeriodicViscosityRescalingAPI where
  scaled_classes := scaled_classes
  inverse_identities := inverse_identities
  to_unit := to_unit
  from_unit := from_unit

/-! ## 6. Non-vacuity of the assembled package -/

/-- The assembled local theory is not vacuous: a nonzero constant solenoidal
periodic datum and a nonzero smooth force with compact support in positive time
are admissible, the selected horizon at those arguments is positive, and the
selected solution really starts at the datum.  The force is the bump profile of
`research/T11/probes/maximal_closes.lean`, which is now unconditional. -/
theorem periodicLocalTheoryAPI_nonvacuous :
    ∃ (a : SpatialField) (f : SpaceTimeField) (ha : a ∈ initialClassT)
      (hf : f ∈ forceClassT),
      a 0 ≠ 0 ∧ f (2, 0) ≠ 0 ∧
      0 < periodicLocalTheoryAPI.horizon 1 a f ∧
      (periodicLocalTheoryAPI.solution 1 one_pos a ha f hf).velocity (0, 0) ≠ 0 := by
  let profile : ContDiffBump (2 : ℝ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let c : Space := coordinateVector 0
  let a : SpatialField := fun _ ↦ c
  let f : SpaceTimeField := fun z ↦ profile z.1 • c
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Space ↦ x 0) h
    simp [c, coordinateVector] at h0
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [a, spatialDivergence, spatialDerivative]
  have hsupport : tsupport (profile : ℝ → ℝ) ⊆ Ioi 0 := by
    rw [profile.tsupport_eq]
    intro t ht
    have habs : |t - 2| ≤ 1 / 2 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, profile] using ht
    have := (abs_le.mp habs).1
    change 0 < t
    linarith
  have hf : f ∈ forceClassT :=
    memForceT_time_smul profile.contDiff profile.hasCompactSupport hsupport
      contDiff_const (fun _ _ ↦ rfl)
  have hf2 : f (2, 0) ≠ 0 := by
    have hp : profile 2 = 1 := profile.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_self]
      exact profile.rIn_pos.le)
    simpa only [f, hp, one_smul] using hc
  refine ⟨a, f, ha, hf, ?_, hf2, periodicLocalHorizon_pos one_pos ha hf, ?_⟩
  · simpa [a] using hc
  · show (periodicLocalSolution 1 one_pos a ha f hf).velocity (0, 0) ≠ 0
    rw [(periodicLocalSolution 1 one_pos a ha f hf).initial]
    simpa [a] using hc

end NSFormalization.Section3.T11
