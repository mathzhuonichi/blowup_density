import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.D01.HomogeneousWitness
import NSFormalization.Paper3.AngularRealVectorBochner

/-!
# B01 units 1–2: the compact-force Bochner approximation

This module discharges the two `B01` obligations that Proposition 4.6
(`prop:Renergy`, `paper/sections/04-whole-space.tex:218-229`) actually consumes on the
inhomogeneous completed force space, at the level `R46` uses them:

* **Unit 1** (`research/B01/COMPARISON.md:145`), `sobolevPath_of_compact`: the output of the
  source density theorem is a genuine `IsSobolevPath`, is `AEStronglyMeasurable`, and lies in
  `F_c`.  This is packaging around `Paper3.angularRealVectorSlice_pairing` (`ARVB:54`),
  `Paper3.memLp_angularRealVectorSlice` (`ARVB:64`) and the D01 lemma
  `memForceCompact_of_smooth_support`.
* **Unit 2** (`research/B01/COMPARISON.md:146`), `approxCompact`: the field
  `∀ q, 1 ≤ q → q ≠ ⊤ → ∀ s, CompletedDense q s forceClassCompact` of
  `research/B01/Spec.lean:312`, proved by `Paper3.exists_angular_real_vector_positive_physical_approx`
  (`ARVB:120`) applied to `hb.toLp b`, unit 1, and the `ε`/`ENNReal.toReal_lt_toReal` bookkeeping.

## Restated `Contracts.V1.Data` predicates

`formalization/` is an upstream Lake package of `verification/` and cannot import
`Contracts.*`.  `MemBochnerDatum`, `bochnerDatumENorm`, `CompletedDenseVia`, `CompletedDense`
and `forceClassCompact` below are therefore restated **token-for-token** from
`Contracts/V1/Data.lean:212,205,732,743,563` (with the local `SpaceTimeField := VelocityField`
abbreviation of `Data.lean:104`, mirroring `Section4/D01/HomogeneousWitness.lean:614`), exactly
as `Section4/D01/ForceClass.lean` restates `IsSobolevPath`/`MemForceCompact`/`forceTimeMeasure`
and `Section4/D01/SmoothDatum.lean` restates `IsSobolevDatum`.  `bochnerSpace` is restated from
`research/B01/Spec.lean:158` — the manuscript completion object, which has **no**
`Contracts.V1.Data` declaration.  Each predicate is definitionally equal to its contract
counterpart; the conformance file `research/B01/axioms_u123.lean` discharges the spec fields by
these theorems through that defeq.

`bochnerDatumENorm` (`Data.lean:205`) already has a verbatim local copy at
`Section4/D01/HomogeneousWitness.lean:620` (namespace `NSFormalization.Section4.D01.Homogeneous`),
which is the canonical one.  Opening that namespace here would make `forceTimeMeasure` and
`bochnerDatumENorm` ambiguous with the `ForceClass`/local copies, so this module keeps its own
one-line copy and records the definitional agreement with the `bochnerDatumENorm_eq_homogeneous`
`rfl` bridge below (unit 10 will hoist the shared vocabulary into one module).

Everything reused from `Section4/D01` (namespace `NSFormalization.Section4.D01`):
`IsSobolevPath`, `IsSobolevDatum`, `MemForceCompact`, `forceTimeMeasure`,
`memForceCompact_of_smooth_support`.  Everything reused from `Paper3`:
`RealVectorSobolev`, `angularRealVectorSlice`, `angularRealVectorSlice_pairing`,
`memLp_angularRealVectorSlice`, `exists_angular_real_vector_positive_physical_approx`.
-/

noncomputable section

namespace NSFormalization.Section4.B01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal SchwartzMap

/-! ## 0. Restated completion vocabulary of `Contracts.V1.Data` -/

/-- `Contracts.V1.Data.SpaceTimeField` (`Data.lean:104`), restated (same as
`Section4/D01/HomogeneousWitness.lean:614`) so the definitions below stay token-for-token with
the contract. -/
abbrev SpaceTimeField := VelocityField

/-- `Contracts.V1.Data.MemBochnerDatum` (`Data.lean:212`), restated: membership of a datum path
in the Bochner space `L^q(0,∞;H^s(R³))`. -/
def MemBochnerDatum (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : Prop :=
  MemLp G q forceTimeMeasure

/-- `Contracts.V1.Data.bochnerDatumENorm` (`Data.lean:205`), restated: the `L^q(0,∞;H^s)` norm
of a datum path.  A verbatim copy of the canonical `Section4/D01/HomogeneousWitness.lean:620`
`NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm`; see the module docstring and the
`bochnerDatumENorm_eq_homogeneous` bridge below. -/
def bochnerDatumENorm (q : ℝ≥0∞) (s : ℝ) (G : ℝ → RealVectorSobolev s) : ℝ≥0∞ :=
  eLpNorm G q forceTimeMeasure

/-- Drift bridge: this module's `bochnerDatumENorm` is the canonical
`D01.Homogeneous.bochnerDatumENorm` (`Data.lean:205`), on the nose. -/
theorem bochnerDatumENorm_eq_homogeneous :
    @bochnerDatumENorm = @NSFormalization.Section4.D01.Homogeneous.bochnerDatumENorm := rfl

/-- `Contracts.V1.Data.CompletedDenseVia` (`Data.lean:732`), restated. -/
def CompletedDenseVia (q : ℝ≥0∞) (s : ℝ)
    (path : SpaceTimeField → (ℝ → RealVectorSobolev s) → Prop)
    (S : Set SpaceTimeField) : Prop :=
  ∀ b : ℝ → RealVectorSobolev s, MemBochnerDatum q s b →
    ∀ r : ℝ≥0∞, 0 < r →
      ∃ f ∈ S, ∃ D : ℝ → RealVectorSobolev s,
        path f D ∧ AEStronglyMeasurable D forceTimeMeasure ∧
          bochnerDatumENorm q s (D - b) < r

/-- `Contracts.V1.Data.CompletedDense` (`Data.lean:743`), restated: density of `S` in the full
Bochner space `L^q(0,∞;H^s(R³))`. -/
abbrev CompletedDense (q : ℝ≥0∞) (s : ℝ) (S : Set SpaceTimeField) : Prop :=
  CompletedDenseVia q s (IsSobolevPath s) S

/-- `Contracts.V1.Data.forceClassCompact` (`Data.lean:563`), restated: the set `F_c`. -/
def forceClassCompact : Set SpaceTimeField := {f | MemForceCompact f}

/-- `research/B01/Spec.lean:158`, restated: the bundled Bochner space `L^q(0,∞;H^s(R³;R³))`.
This is the manuscript completion object; it has no `Contracts.V1.Data` declaration. -/
abbrev bochnerSpace (q : ℝ≥0∞) (s : ℝ) := Lp (RealVectorSobolev s) q forceTimeMeasure

/-! ## 1. Unit 1: the datum path of a compact smooth force -/

/-- **Unit 1, `IsSobolevPath` half.**  The normalized angular datum path
`angularRealVectorSlice s f hf hc` of the components of a spacetime field `F` is the order-`s`
Sobolev path of `F` itself, whenever `f i` are exactly the components of `F`.  This is
`Paper3.angularRealVectorSlice_pairing` (`ARVB:54`), which matches `Data.IsSobolevDatum`
(`Data.lean:160`) verbatim, at every nonnegative time. -/
theorem isSobolevPath_angularRealVectorSlice (s : ℝ) (F : VelocityField)
    (f : Fin 3 → ℝ × Space → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hc : ∀ i, HasCompactSupport (f i)) (hFf : ∀ z i, (F z).ofLp i = f i z) :
    IsSobolevPath s F (angularRealVectorSlice s f hf hc) := by
  intro t _ht i ψ
  rw [angularRealVectorSlice_pairing s f hf hc t i ψ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hFf (t, x) i]

/-- **Unit 1, `AEStronglyMeasurable` half.**  `Paper3.memLp_angularRealVectorSlice` (`ARVB:64`)
gives `MemLp` at every exponent; strong measurability is its first component. -/
theorem aestronglyMeasurable_angularRealVectorSlice (s : ℝ) (f : Fin 3 → ℝ × Space → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i)) :
    AEStronglyMeasurable (angularRealVectorSlice s f hf hc) forceTimeMeasure :=
  (memLp_angularRealVectorSlice s f hf hc 1).aestronglyMeasurable

/-! ## 2. Norm bookkeeping for unit 2 -/

/-- The datum-path Bochner norm of the difference of two `L^q` paths equals the `Lp` norm of the
difference of their classes, and is finite.  Pure a.e.-class bookkeeping
(`MemLp.coeFn_toLp`, `Lp.coeFn_sub`, `eLpNorm_congr_ae`, `Lp.norm_def`, `Lp.eLpNorm_ne_top`);
`research/B01/COMPARISON.md:146` step (ii). -/
theorem bochnerDatumENorm_toLp_sub {q : ℝ≥0∞} {s : ℝ} {b D : ℝ → RealVectorSobolev s}
    (hb : MemLp b q forceTimeMeasure) (hD : MemLp D q forceTimeMeasure) :
    bochnerDatumENorm q s (D - b) ≠ ⊤ ∧
      (bochnerDatumENorm q s (D - b)).toReal = ‖hD.toLp D - hb.toLp b‖ := by
  have hae : (⇑(hD.toLp D - hb.toLp b)) =ᵐ[forceTimeMeasure] (D - b) := by
    filter_upwards [Lp.coeFn_sub (hD.toLp D) (hb.toLp b), hD.coeFn_toLp, hb.coeFn_toLp]
      with t h1 h2 h3
    simp only [Pi.sub_apply, h1, h2, h3]
  have heq : bochnerDatumENorm q s (D - b)
      = eLpNorm (⇑(hD.toLp D - hb.toLp b)) q forceTimeMeasure :=
    (eLpNorm_congr_ae hae).symm
  refine ⟨by rw [heq]; exact Lp.eLpNorm_ne_top _, ?_⟩
  rw [heq, ← Lp.norm_def]

/-! ## 3. Unit 2: compact forces are dense in the completed Bochner space -/

/-- **Unit 2, `approxCompact`** (`research/B01/Spec.lean:312`).  Smooth compactly supported
forces on `R³ × (0,∞)` are dense in each completed Bochner space `L^q(0,∞;H^s(R³;R³))`, for
every `q ∈ [1,∞)` and every real `s`.  `Paper3.exists_angular_real_vector_positive_physical_approx`
(`ARVB:120`) supplies the approximant; unit 1 turns its output into the datum path
`R46` consumes. -/
theorem approxCompact (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hq2 : q ≠ ⊤) (s : ℝ) :
    CompletedDense q s forceClassCompact := by
  have : Fact (1 ≤ q) := ⟨hq1⟩
  intro b hb r hr
  have hb' : MemLp b q forceTimeMeasure := hb
  obtain ⟨ε, hεpos, hεr⟩ : ∃ ε : ℝ, 0 < ε ∧ (r ≠ ⊤ → ε ≤ r.toReal) := by
    by_cases hrtop : r = ⊤
    · exact ⟨1, one_pos, fun h => absurd hrtop h⟩
    · exact ⟨min 1 r.toReal, lt_min one_pos (ENNReal.toReal_pos hr.ne' hrtop),
        fun _ => min_le_right _ _⟩
  obtain ⟨F, hF, hFc, hFs, f, hf, hc, hFi, he⟩ :=
    exists_angular_real_vector_positive_physical_approx s q hq2 (hb'.toLp b) hεpos
  have hmem : MemLp (angularRealVectorSlice s f hf hc) q forceTimeMeasure :=
    memLp_angularRealVectorSlice s f hf hc q
  refine ⟨F, ?_, angularRealVectorSlice s f hf hc, ?_, ?_, ?_⟩
  · exact memForceCompact_of_smooth_support hF hFc (fun z hz => hFs hz)
  · exact isSobolevPath_angularRealVectorSlice s F f hf hc hFi
  · exact aestronglyMeasurable_angularRealVectorSlice s f hf hc
  · obtain ⟨hMne, hMtoReal⟩ := bochnerDatumENorm_toLp_sub hb' hmem
    have hMtoReal_lt :
        (bochnerDatumENorm q s (angularRealVectorSlice s f hf hc - b)).toReal < ε := by
      rw [hMtoReal, norm_sub_rev]; exact he
    by_cases hrtop : r = ⊤
    · rw [hrtop]; exact lt_top_iff_ne_top.mpr hMne
    · rw [← ENNReal.toReal_lt_toReal hMne hrtop]
      exact lt_of_lt_of_le hMtoReal_lt (hεr hrtop)

end NSFormalization.Section4.B01
