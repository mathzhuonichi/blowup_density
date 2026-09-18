import NSFormalization.Section3.T12.MeanZeroCalculus
import NSFormalization.Section3.T13.TorusIdentity
import NSFormalization.Section3.T13.ConstantEndpoints

/-!
# T12 U1 — the Haar ↔ cube ↔ whole-space `L^p` transfer

`03-torus.tex:23-29,53-72,96-98`: the fundamental-domain calculation that moves
a Haar norm on the unit three-torus `T³` to a Lebesgue norm over the closed
fundamental cube `[0,1]³` (and, for fields supported inside the cube, to the
whole-space norm).  This is the measure-theoretic backbone of every critical
embedding in Section 3 (`research/T12/T12_SPLIT.md` U1, consumed by U4/U5).

## What is proved here

* `eLpNorm_torusLift_eq_restrict` — the actual all-`p` transfer, for **every**
  `p : ℝ≥0∞` including `p = 0` and `p = ⊤`, and for **any** normed target:
  `eLpNorm (torusLift v) p periodicTorusMeasure = eLpNorm v p (volume.restrict fundamentalCube)`.
  The whole family of exponents is closed by a single measure identity
  (`map_torusChart`) together with Mathlib's measurable-embedding change of
  variables `MeasurableEmbedding.eLpNorm_map_measure`, which internally covers
  the finite exponents by `∫⁻ ‖·‖ₑ^p.toReal` and the endpoint `p = ⊤` by
  `essSup`.  The periodicity hypothesis `_hv` is the paper's "unit-periodic `v`"
  interface: the identity in fact holds for every field, because both sides read
  `v` only on one fundamental copy, but the hypothesis is kept for statement
  fidelity and because U4/U5 supply it anyway.
* the smooth corollary `eLpNorm_torusLift_eq_restrict_smooth`, and the exact
  scalar / gradient-tensor forms (`gradientTensor v : Space → WithLp 2 (Fin 3 → Space)`).
* `eLpNorm_restrict_eq_of_support` / `…_tsupport` — a field supported inside the
  cube has the same cube-restricted and whole-space norm (scalar, vector and
  gradient-tensor carriers), in both the `Function.support` and the `tsupport`
  spellings.
* the API bridge `periodicLpENorm_eq_eLpNorm_torusLift` (definitional, `rfl`) and
  its combination `periodicLpENorm_eq_restrict` with the transfer.

The chart `torusChart` is the volume-preserving fundamental-domain map
`T³ → Space`, `z ↦ toSpace ((measurableEquivPiIoc 0 z).val)`, so that
`torusLift v = v ∘ torusChart` definitionally.  Its pushforward of Haar measure
is exactly `volume.restrict fundamentalCube`; this replaces the `p = 2` lintegral
route of `T15/HaarBridge.lean` by a single measure equality that closes all `p`.

No `sorry`, no `axiom`, no `native_decide`, no named goal input.  Every
declaration reduces to `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
namespace NSFormalization.Section3.T12
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NavierStokes.PeriodicIntegration (Coords toSpace)
open scoped ENNReal BigOperators

/-! ## §0  The API norm bridge -/

/-- `01-introduction.tex:104`: the API norm is definitionally the Haar norm of
the canonical lift. -/
theorem periodicLpENorm_eq_eLpNorm_torusLift {E : Type*} [NormedAddCommGroup E]
    (p : ℝ≥0∞) (v : Space → E) :
    periodicLpENorm p v = eLpNorm (torusLift v) p periodicTorusMeasure := rfl

/-! ## §1  The volume-preserving fundamental-domain chart

`torusChart` is `T³ → Space`, `z ↦ toSpace ((measurableEquivPiIoc 0 z).val)`, the
composite of Mathlib's measurable equivalence `measurableEquivPiIoc` (torus ≃ the
half-open box), the box inclusion `Subtype.val`, and the volume-preserving linear
chart `toSpace`.  It satisfies `torusLift v = v ∘ torusChart` by definition. -/
private def torusChart (z : PeriodicTorus) : Space :=
  toSpace ((UnitAddTorus.measurableEquivPiIoc (0 : Coords) z).val)

private theorem torusChart_comp {E : Type*} (v : Space → E) :
    torusLift v = v ∘ torusChart := rfl

/-- The half-open box `(0,1]³ ⊆ Coords` is measurable. -/
private theorem iocBox_measurable :
    MeasurableSet {x : Coords | ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} := by
  have h : {x : Coords | ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)}
      = Set.univ.pi (fun i => Ioc ((0 : Coords) i) ((0 : Coords) i + 1)) := by ext x; simp
  rw [h]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

/-- The chart is a measurable embedding: a composite of two measurable
equivalences and the box inclusion. -/
private theorem measurableEmbedding_torusChart : MeasurableEmbedding torusChart := by
  have he_equiv : MeasurableEmbedding (⇑(UnitAddTorus.measurableEquivPiIoc (0 : Coords))) :=
    (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurableEmbedding
  have he_val : MeasurableEmbedding
      (Subtype.val : {x : Coords // ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} → Coords) :=
    MeasurableEmbedding.subtype_coe iocBox_measurable
  have he_toSpace : MeasurableEmbedding (toSpace : Coords → Space) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding
  exact he_toSpace.comp (he_val.comp he_equiv)

/-- The heart of the transfer: the chart pushes normalized Haar measure on `T³`
forward to Lebesgue measure restricted to the fundamental cube.  This one measure
identity closes every exponent `p` at once. -/
private theorem map_torusChart :
    Measure.map torusChart periodicTorusMeasure = volume.restrict fundamentalCube := by
  have hg1 : Measurable (⇑(UnitAddTorus.measurableEquivPiIoc (0 : Coords))) :=
    (UnitAddTorus.measurableEquivPiIoc (0 : Coords)).measurable
  have hg2 : Measurable
      (Subtype.val : {x : Coords // ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} → Coords) :=
    measurable_subtype_coe
  have hg3 : Measurable (toSpace : Coords → Space) :=
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurable
  have hmp : MeasurePreserving (toSpace : Coords → Space) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  have hchart : torusChart
      = (toSpace : Coords → Space) ∘
        ((Subtype.val : {x : Coords // ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} → Coords)
          ∘ ⇑(UnitAddTorus.measurableEquivPiIoc (0 : Coords))) := rfl
  have h1 : Measure.map (⇑(UnitAddTorus.measurableEquivPiIoc (0 : Coords))) periodicTorusMeasure
      = Measure.comap Subtype.val volume :=
    (UnitAddTorus.measurePreserving_equivPiIoc (0 : Coords)).map_eq
  have h2 : Measure.map
        (Subtype.val : {x : Coords // ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} → Coords)
        (Measure.comap Subtype.val volume)
      = volume.restrict {x : Coords | ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)} :=
    map_comap_subtype_coe iocBox_measurable volume
  have hpi : {x : Coords | ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)}
      = Set.univ.pi (fun i => Ioc ((0 : Coords) i) ((0 : Coords) i + 1)) := by ext x; simp
  have hone : (fun i => (0 : Coords) i + 1) = (1 : Coords) := by funext i; simp
  have hae : {x : Coords | ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)}
      =ᵐ[volume] Icc (0 : Coords) 1 := by
    rw [hpi]
    have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 3 => (volume : Measure ℝ))
      (f := (0 : Coords)) (g := fun i => (0 : Coords) i + 1)
    rw [hone] at h
    exact h
  have h3 : Measure.map (toSpace : Coords → Space)
        (volume.restrict {x : Coords | ∀ i, x i ∈ Ioc ((0 : Coords) i) ((0 : Coords) i + 1)})
      = volume.restrict fundamentalCube := by
    rw [Measure.restrict_congr_set hae,
      show (Icc (0 : Coords) 1) = (toSpace : Coords → Space) ⁻¹' fundamentalCube from
        toSpace_preimage_fundamentalCube.symm,
      ← Measure.restrict_map hg3 measurableSet_fundamentalCube, hmp.map_eq]
  rw [hchart, ← Measure.map_map hg3 (hg2.comp hg1), ← Measure.map_map hg2 hg1, h1, h2, h3]

/-! ## §2  The all-`p` Haar/cube transfer for periodic fields -/

/-- `03-torus.tex:23-29,96-98`: for a unit-periodic field `v` and **every**
exponent `p` (including `p = 0` and `p = ⊤`), the Haar `L^p` norm of the
canonical torus lift equals the Lebesgue `L^p` norm over the fundamental cube.

The identity holds for an arbitrary normed target and, in fact, for every field,
so the periodicity hypothesis `_hv` is unused in the proof; it is retained for
statement fidelity with the article's "unit-periodic `v`" and for the downstream
interface (U4/U5). -/
theorem eLpNorm_torusLift_eq_restrict {E : Type*} [NormedAddCommGroup E]
    (v : Space → E) (_hv : IsPeriodicSpatial v) (p : ℝ≥0∞) :
    eLpNorm (torusLift v) p periodicTorusMeasure
      = eLpNorm v p (volume.restrict fundamentalCube) := by
  rw [torusChart_comp v, ← measurableEmbedding_torusChart.eLpNorm_map_measure, map_torusChart]

/-- The smooth-field corollary: for `SmoothPeriodicT v` the transfer is
unconditional (smoothness discharges the interface). -/
theorem eLpNorm_torusLift_eq_restrict_smooth (v : SpatialField) (hv : SmoothPeriodicT v)
    (p : ℝ≥0∞) :
    eLpNorm (torusLift v) p periodicTorusMeasure
      = eLpNorm v p (volume.restrict fundamentalCube) :=
  eLpNorm_torusLift_eq_restrict v hv.2 p

/-- Scalar specialization of the transfer (`E = ℝ`), the form consumed at `p = 3`
by U4's `velocityCriticalL3`. -/
theorem eLpNorm_torusLift_eq_restrict_scalar (z : Space → ℝ) (hz : IsPeriodicSpatial z)
    (p : ℝ≥0∞) :
    eLpNorm (torusLift z) p periodicTorusMeasure
      = eLpNorm z p (volume.restrict fundamentalCube) :=
  eLpNorm_torusLift_eq_restrict z hz p

/-- Gradient-tensor specialization of the transfer, with the exact
`GradientL6` carrier `gradientTensor v : Space → WithLp 2 (Fin 3 → Space)`; the
form consumed at `p = 6` by U5's `gradientLSix`. -/
theorem eLpNorm_torusLift_eq_restrict_gradientTensor (v : SpatialField)
    (hv : IsPeriodicSpatial (gradientTensor v)) (p : ℝ≥0∞) :
    eLpNorm (torusLift (gradientTensor v)) p periodicTorusMeasure
      = eLpNorm (gradientTensor v) p (volume.restrict fundamentalCube) :=
  eLpNorm_torusLift_eq_restrict (gradientTensor v) hv p

/-- The API norm bridged all the way to the cube-restricted Lebesgue norm, for a
periodic field: `periodicLpENorm p v = eLpNorm v p (volume.restrict fundamentalCube)`. -/
theorem periodicLpENorm_eq_restrict {E : Type*} [NormedAddCommGroup E]
    (v : Space → E) (hv : IsPeriodicSpatial v) (p : ℝ≥0∞) :
    periodicLpENorm p v = eLpNorm v p (volume.restrict fundamentalCube) := by
  rw [periodicLpENorm_eq_eLpNorm_torusLift, eLpNorm_torusLift_eq_restrict v hv p]

/-- Gradient-tensor form of the API-to-cube bridge, consumed by U5. -/
theorem periodicLpENorm_eq_restrict_gradientTensor (v : SpatialField)
    (hv : IsPeriodicSpatial (gradientTensor v)) (p : ℝ≥0∞) :
    periodicLpENorm p (gradientTensor v)
      = eLpNorm (gradientTensor v) p (volume.restrict fundamentalCube) :=
  periodicLpENorm_eq_restrict (gradientTensor v) hv p

/-! ## §3  The supported-in-cube transfer to the whole space -/

/-- A field whose `Function.support` sits in the open cube has equal cube-restricted
and whole-space norms. -/
theorem eLpNorm_restrict_eq_of_support {E : Type*} [NormedAddCommGroup E]
    (w : Space → E) (hw : Function.support w ⊆ interior fundamentalCube)
    (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume := by
  apply MeasureTheory.eLpNorm_restrict_eq_of_support_subset
  exact hw.trans interior_subset

/-- The gradient-tensor carrier `WithLp 2 (Fin 3 → Space)` of the support transfer. -/
theorem eLpNorm_restrict_eq_of_support_vector
    (w : Space → WithLp 2 (Fin 3 → Space))
    (hw : Function.support w ⊆ interior fundamentalCube) (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume :=
  eLpNorm_restrict_eq_of_support w hw p

/-- `tsupport` spelling of the support transfer (`tsupport w ⊆ interior fundamentalCube`),
the form the localization argument produces. -/
theorem eLpNorm_restrict_eq_of_tsupport {E : Type*} [NormedAddCommGroup E]
    (w : Space → E) (hw : tsupport w ⊆ interior fundamentalCube)
    (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume :=
  eLpNorm_restrict_eq_of_support w ((subset_tsupport w).trans hw) p

/-- Gradient-tensor carrier of the `tsupport` support transfer. -/
theorem eLpNorm_restrict_eq_of_tsupport_vector
    (w : Space → WithLp 2 (Fin 3 → Space))
    (hw : tsupport w ⊆ interior fundamentalCube) (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume :=
  eLpNorm_restrict_eq_of_tsupport w hw p

end NSFormalization.Section3.T12
