import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.D01.HomogeneousWitness

/-!
# A04 unit F1: the forcing hypotheses are free from `MemForceR`

`research/A04/COMPARISON.md` §4 unit **F1**.  The A04 draft
(`research/A04/Spec.lean`) states two forcing predicates that
`ContinuationAPI.highContinuationIntegral`, `.higherOrderBound`,
`.extendsBeyond`, `.lifespanInfiniteOfLocallyFinite` (the `L¹_t H^m` clause) and
`.restartBeyond` (the bounded-into-`H¹` clause) consume:

* `MemL1Hm f := ∀ m : ℕ, forceSobolevENormL1 (m:ℝ) f ≠ ⊤` (`Spec.lean:268`), and
* `BoundedIntoHOne I K f := ∀ t ∈ I, sobolevENorm 1 (f(t,·)) ≤ K` (`Spec.lean:286`).

Both docstrings mark themselves "redundant, deliberately" (`REVIEW.md`
finding 5): they are listed as separate hypotheses so the contract displays the
manuscript's own hypothesis rather than the ambient `F_R` class, but a consumer
holding `MemForceR f` gets them for free.  This module discharges that debt.

* `memL1Hm_of_memForceR` — the `MemLp G 1 forceTimeMeasure` clause of
  `MemForceR` (`SolutionClass.lean:91`, `Data.lean:544`) **is** `MemL1Hm`: the
  order-`m` datum path witnesses the infimum `forceSobolevENorm 1 (m:ℝ) f` and
  bounds it by `eLpNorm G 1 forceTimeMeasure < ⊤`.
* `exists_boundedIntoHOne_of_memForceR` — the `ContDiffOn ℝ ∞ G futureTimes`
  clause of `MemForceR` restricted to a compact time interval gives a finite
  `H¹` sup bound, i.e. `IsCompact.exists_bound_of_continuousOn` on the order-`1`
  datum path.  (The equality of that bound with the velocity's `K`, which
  `restartBeyond` also needs, is *not* free and is not claimed here — only the
  existence of some finite `K`, exactly as COMPARISON.md §4 F1 phrases it.)

## Restated objects

`NSFormalization` is an upstream Lake package of `verification` and cannot import
`Contracts.*`.  The A04 draft `def`s `sobolevNormAt`, `MemL1Hm`,
`BoundedIntoHOne`, together with the `Data.lean` norms they rest on
(`bochnerDatumENorm`, `forceSobolevENorm`, `forceSobolevENormL1`), are therefore
restated **verbatim** below, each with its source line.  `sobolevENorm`,
`IsSobolevDatum`, `sobolevENorm_le_of_isSobolevDatum` and `isSobolevDatum_unique`
are lane 020/D01's verbatim restatements in `Section4/D01/{SmoothDatum,ForceClass}`;
`MemForceR`, `IsSobolevPath`, `ClassicalSolutionR` and `forceTimeMeasure` are
lane 032/A02's in `Section4/A02/SolutionClass`.  The A02 and D01 copies of
`MemForceR`, `IsSobolevPath`, `IsSobolevDatum`, `futureTimes` and
`forceTimeMeasure` are pairwise equal by `rfl` (checked); this module opens the
A02 copy for the class vocabulary and the D01 copy for the norm vocabulary, and
they interoperate definitionally.

Each restated `def` is field-for-field definitionally equal to its
`Contracts.V1.Data` / `research/A04/Spec.lean` original, so the conformance file
`research/A04/axioms_f1n1.lean` discharges the spec-vocabulary statements by
`exact` on the theorems below.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02
  (SpaceTimeField SpatialField SpaceTimeScalar MemForceR IsSobolevPath ClassicalSolutionR
    forceTimeMeasure)
open NSFormalization.Section4.D01
  (sobolevENorm sobolevENorm_le_of_isSobolevDatum isSobolevDatum_unique IsSobolevDatum)

/-! ## 0. The A04 draft `def`s, restated verbatim -/

/-- `research/A04/Spec.lean:183` `sobolevNormAt`: `‖u(t)‖_{H^s}` as a **real**
number, the `.toReal` of `Data.sobolevENorm` on the time-`t` slice. -/
def sobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (sobolevENorm s (fun x : Space => u (t, x))).toReal

/-- `verification/Contracts/V1/Data.lean:205` `bochnerDatumENorm`, restated
verbatim: the `L^q(0,∞;H^s)` Bochner norm of a datum path.

There is already an in-package verbatim copy,
`NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm`
(`Section4/D01/HomogeneousWitness.lean:620`); `bochnerDatumENorm_eq_homogeneous`
below records that the two agree by `rfl`.  It is restated here rather than
opened because `HomogeneousWitness` is imported anyway for that bridge, but the
`def` is kept local so the `forceSobolevENorm` restatement reads token-for-token
against `Data.lean` in one place. -/
def bochnerDatumENorm (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  eLpNorm G q forceTimeMeasure

/-- The A04 copy of `bochnerDatumENorm` and the in-package D01 copy agree
(finding 1, `REVIEW_F1N1.md`): both are `eLpNorm G q forceTimeMeasure`. -/
theorem bochnerDatumENorm_eq_homogeneous :
    @bochnerDatumENorm = @NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm := rfl

/-- `verification/Contracts/V1/Data.lean:225` `forceSobolevENorm`, restated
verbatim: `‖f‖_{L^q(0,∞;H^s)}`, the infimum of the Bochner norm over measurable
order-`s` datum paths of `f`, `⊤` when none exists. -/
def forceSobolevENorm (q : ℝ≥0∞) (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ⨅ G : {G : ℝ → RealVectorSobolev s //
      IsSobolevPath s f G ∧ AEStronglyMeasurable G forceTimeMeasure},
    bochnerDatumENorm q s G.1

/-- `verification/Contracts/V1/Data.lean:231` `forceSobolevENormL1`, restated
verbatim: the `q = 1` case, `‖f‖_{L¹_tH^s_x}`. -/
abbrev forceSobolevENormL1 (s : ℝ) (f : SpaceTimeField) : ℝ≥0∞ :=
  forceSobolevENorm 1 s f

/-- `research/A04/Spec.lean:268` `MemL1Hm`: `‖f‖_{L¹_tH^m_x} < ∞` at every
integer order — the `L¹_t H^m` forcing the continuation proof integrates. -/
def MemL1Hm (f : SpaceTimeField) : Prop :=
  ∀ m : ℕ, forceSobolevENormL1 (m : ℝ) f ≠ ⊤

/-- `research/A04/Spec.lean:286` `BoundedIntoHOne`: `f` is bounded into `H¹` on
the time set `I` by `K`, the bounded local `H¹` forcing hypothesis of the
restart. -/
def BoundedIntoHOne (I : Set ℝ) (K : ℝ≥0∞) (f : SpaceTimeField) : Prop :=
  ∀ t ∈ I, sobolevENorm 1 (fun x : Space => f (t, x)) ≤ K

/-! ## 1. Datum bookkeeping -/

/-- The manuscript norm of a slice equals the enorm of any of its data: the
order-`s` datum is unique (`D01.isSobolevDatum_unique`), so the singleton
infimum defining `sobolevENorm` collapses to `‖A‖ₑ`.  This is the vector case of
`A03.sobolevENorm_eq`, reproved here from `D01` alone to keep the F1/N1 closure
small. -/
theorem sobolevENorm_eq {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) : sobolevENorm s z = ‖A‖ₑ := by
  refine le_antisymm (sobolevENorm_le_of_isSobolevDatum hA) (le_iInf ?_)
  rintro ⟨B, hB⟩
  rw [isSobolevDatum_unique hA hB]

/-! ## 2. F1a: `MemForceR f → MemL1Hm f` -/

/-- **F1a.**  A force in `F_R` has finite `L¹_t H^m` norm at every integer order.
The `MemLp G 1 forceTimeMeasure` clause of `MemForceR` (`SolutionClass.lean:91`,
`Data.lean:544`) provides, at order `m`, a strongly measurable datum path `G`
with `eLpNorm G 1 forceTimeMeasure < ⊤`; that path is an element of the infimum
index set of `forceSobolevENorm 1 (m:ℝ) f`, so the infimum is `≤` a finite value
and hence `≠ ⊤`. -/
theorem memL1Hm_of_memForceR {f : SpaceTimeField} (hf : MemForceR f) : MemL1Hm f := by
  intro m
  obtain ⟨G, hpath, _hc, h1, _h2⟩ := hf.2 m
  have hle : forceSobolevENorm 1 (m : ℝ) f ≤ eLpNorm G 1 forceTimeMeasure :=
    iInf_le (fun G : {G : ℝ → RealVectorSobolev (m : ℝ) //
        IsSobolevPath (m : ℝ) f G ∧ AEStronglyMeasurable G forceTimeMeasure} =>
        bochnerDatumENorm 1 (m : ℝ) G.1) ⟨G, hpath, h1.1⟩
  exact ne_top_of_le_ne_top h1.2.ne hle

/-! ## 3. F1b: `MemForceR f → ∃ K ≠ ⊤, BoundedIntoHOne (Icc 0 b) K f` -/

/-- **F1b.**  A force in `F_R` is bounded into `H¹` on every compact time
interval `[0,b]`.  The order-`1` datum path `G` of `MemForceR` is `ContDiffOn ℝ ∞
G futureTimes` (`SolutionClass.lean:90`, `Data.lean:544`), hence `ContinuousOn`
on `[0,b] ⊆ [0,∞)`; `IsCompact.exists_bound_of_continuousOn` gives a real bound
`C` on `‖G t‖`, and `sobolevENorm 1 (f(t,·)) ≤ ‖G t‖ₑ ≤ ENNReal.ofReal C =: K`.

Only the *existence* of a finite `K` is claimed, as `research/A04/COMPARISON.md`
§4 F1 states; matching it to the velocity's `K` — which `restartBeyond` also
needs — is not free from `MemForceR` and is left to the consumer. -/
theorem exists_boundedIntoHOne_of_memForceR {f : SpaceTimeField} (hf : MemForceR f) (b : ℝ) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ BoundedIntoHOne (Icc 0 b) K f := by
  obtain ⟨G, hpath, hc, _, _⟩ := hf.2 1
  have hcont : ContinuousOn G (Icc (0 : ℝ) b) :=
    hc.continuousOn.mono Set.Icc_subset_Ici_self
  obtain ⟨C, hC⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  have hdat : IsSobolevDatum ((1 : ℕ) : ℝ) (fun x : Space => f (t, x)) (G t) := hpath t ht.1
  have hbound : sobolevENorm ((1 : ℕ) : ℝ) (fun x : Space => f (t, x)) ≤ ENNReal.ofReal C := by
    refine (sobolevENorm_le_of_isSobolevDatum hdat).trans ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC t ht)
  simpa only [Nat.cast_one] using hbound

end NSFormalization.Section4.A04
