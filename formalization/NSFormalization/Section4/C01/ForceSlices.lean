import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.D01.DatumToJets
import NavierStokes.R3.LpNormTools

/-!
# C01 unit U2 — the force class transported to physical time slices

`research/C01/COMPARISON.md` unit table row **U2**: from `MemForceR f` produce, for
every future time `t ≥ 0`, `MemLp (slice f t) 2 volume`, and the continuity of
`t ↦ ‖f(t)‖₂` on the closed half line `[0,∞)`.  This is exactly the spec field
`forceTimeRegularity` of `research/C01/Spec.lean`'s `EnergyAbsorptionAPI`
(`research/C01/Spec.lean:326-329`).  Interval integrability of `s ↦ ‖f(s)‖₂` and
of `s ↦ ‖f(s)‖₂²` on each `[0,t]` is, as that field's docstring records, a
consequence of the continuity conjunct (a function continuous on `Ici 0` is
continuous, hence interval integrable, on every compact `[0,t]`), so it is not a
separate obligation and is not proved here.

## What is reused

`MemForceR f` (`verification/Contracts/V1/Data.lean:544`, restated verbatim as
`NSFormalization.Section4.A02.MemForceR` in `Section4/A02/SolutionClass.lean`)
provides, at datum order `m = 0`, a datum path `G : ℝ → RealVectorSobolev 0`
with `IsSobolevPath 0 f G` — an `IsSobolevDatum 0 (slice f t) (G t)` at every
`t ≥ 0` — and `ContDiffOn ℝ ∞ G futureTimes`, `futureTimes = Ici 0`, so `G` is
in particular **continuous on the closed half line `Ici 0`, including `t = 0`**;
together with `ContDiffOn ℝ ∞ f futureDomain`, `futureDomain = Ici 0 ×ˢ univ`.

The datum ⇒ `L²`-slice transport and the slice continuity both go through the
lane-020/D01 machinery of `Section4/D01/DatumToJets.lean`, **not** through
`Section4/A02/Energy.lean`'s order-0 re-derivation (which lane 040's dedupe
removes):

* `D01.contDiff_slice` (`DatumToJets.lean:366`): the slice of a field smooth on
  the closed-at-zero slab is smooth on all of `R³`, `t = 0` included.
* `D01.memLp_of_isSobolevDatum` (`:267`): a smooth field with an order-`m`
  angular datum is in `L²`.
* `D01.jetOfDatum` (`:196`) / `D01.jetOfDatum_ae` (`:202`): the reconstruction of
  the order-`j` jet as an `Lp` element, a.e. equal to `iteratedFDeriv ℝ j z`.  At
  `m = j = 0` this is the `L²` realization of the slice itself, and it is a
  **composition of continuous linear maps** (`PiLp.continuous_apply`, the subtype
  inclusion `RealSobolevHilbert 0 → FourierData`, `(cyclesToAngular 0).symm`,
  `sobolevOrderLowering`, `physicalJetLp`).  Hence `A ↦ ‖jetOfDatum 0 0 _ A‖` is
  continuous, and `lpNorm_two_eq_sqrt_l2Sq` with `norm_iteratedFDeriv_zero`
  identifies `l2Norm (slice f s)` with `‖jetOfDatum 0 0 _ (G s)‖` at each
  `s ≥ 0`.  Composing with the continuity of `G` on `Ici 0` gives the continuity
  conjunct **on all of `Ici 0`** — the endpoint `t = 0` is covered because `G` is
  continuous there (`futureTimes = Ici 0`).

`D01`'s lemmas want `ContDiff ℝ ∞` of the slice where an order-0 argument would
need only `Continuous`; `ContDiffOn ℝ ∞ f futureDomain` supplies it through
`D01.contDiff_slice`.  `D01`'s `IsSobolevDatum` is definitionally
`A02.IsSobolevDatum` (both restate `Data.lean:160`), so `MemForceR`'s datum moves
across by `exact`.  Nothing here uses the `L¹`/`L²` finiteness of the datum path
over `positiveTimeMeasure`; that is `MemForceR`'s global content on `(0,∞)`,
whereas `forceTimeRegularity` is the purely local slicewise statement.
-/

noncomputable section

namespace NSFormalization.Section4.C01

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open NSFormalization.Source.FourierPhysicalJets
open NSFormalization.Section4.A02
open NSFormalization.Section4.D01
  (contDiff_slice memLp_of_isSobolevDatum jetOfDatum jetOfDatum_ae loweredComponent)
open scoped ContDiff

/-! ## 0. The spec's time-slice quantities, restated token-for-token

Copied verbatim from `research/C01/Spec.lean`: `slice` (`:167`), `l2Sq`
(`:172`) and `l2Norm` (`:177`).  `SpaceTimeField` and `SpatialField` are the
`NSFormalization.Section4.A02` (`SolutionClass.lean`) restatements of
`Data.lean:99,104`. -/

/-- `research/C01/Spec.lean:167`.  The spatial slice `z(t) = z(t,·)`. -/
def slice (z : SpaceTimeField) (t : ℝ) : SpatialField := fun x => z (t, x)

/-- `research/C01/Spec.lean:172`.  The squared `L²(R³)` norm `∫|z|²`. -/
def l2Sq (z : SpatialField) : ℝ := ∫ x : Space, ‖z x‖ ^ 2

/-- `research/C01/Spec.lean:177`.  `‖z‖₂ = √(∫|z|²)`. -/
def l2Norm (z : SpatialField) : ℝ := Real.sqrt (l2Sq z)

/-! ## 1. The order-zero D01 realization is a continuous function of the datum -/

/-- The order-zero jet reconstruction `D01.jetOfDatum 0 0 _` is a continuous
function of its datum, being a composition of the continuous linear maps
`PiLp.continuous_apply`, `continuous_subtype_val`, `(cyclesToAngular 0).symm`,
`sobolevOrderLowering` and `physicalJetLp 0`. -/
theorem continuous_jetOfDatum_zero :
    Continuous (fun A : RealVectorSobolev ((0 : ℕ) : ℝ) =>
      jetOfDatum 0 0 (le_refl 0) A) := by
  have hi : ∀ i : Fin 3,
      Continuous (fun A : RealVectorSobolev ((0 : ℕ) : ℝ) =>
        loweredComponent 0 0 (le_refl 0) A i) := by
    intro i
    have hp : Continuous (fun A : RealVectorSobolev ((0 : ℕ) : ℝ) => A i) :=
      PiLp.continuous_apply (p := 2)
        (β := fun _ : Fin 3 => RealSobolevHilbert ((0 : ℕ) : ℝ)) i
    exact ((sobolevOrderLowering ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) (by norm_num)).continuous).comp
      (((cyclesToAngular ((0 : ℕ) : ℝ)).symm.continuous).comp
        (continuous_subtype_val.comp hp))
  exact (physicalJetLp 0).continuous.comp (continuous_pi hi)

/-- At order zero, the physical `L²` norm of a smooth field with a datum `A` is
the norm of its D01 reconstruction `jetOfDatum 0 0 _ A`.  This is the identity
that turns the continuity of the datum path into continuity of `t ↦ ‖f(t)‖₂`. -/
theorem l2Norm_eq_norm_jetOfDatum {z : SpatialField} {A : RealVectorSobolev ((0 : ℕ) : ℝ)}
    (hz : ContDiff ℝ ∞ z) (h : IsSobolevDatum ((0 : ℕ) : ℝ) z A) :
    l2Norm z = ‖jetOfDatum 0 0 (le_refl 0) A‖ := by
  have hmem : MemLp z 2 volume := memLp_of_isSobolevDatum hz h
  have h1 : l2Norm z = (eLpNorm z 2 volume).toReal := by
    show Real.sqrt (NavierStokesR3.Comparison.l2Sq z) = (eLpNorm z 2 volume).toReal
    rw [← NavierStokesR3.LpNormTools.lpNorm_two_eq_sqrt_l2Sq hmem]
    rfl
  have h2 : (eLpNorm z 2 volume).toReal
      = (eLpNorm (iteratedFDeriv ℝ 0 z) 2 volume).toReal := by
    congr 1
    exact eLpNorm_congr_norm_ae
      (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero.symm)
  have h3 : (eLpNorm (iteratedFDeriv ℝ 0 z) 2 volume).toReal
      = ‖jetOfDatum 0 0 (le_refl 0) A‖ := by
    rw [Lp.norm_def]
    congr 1
    exact (eLpNorm_congr_ae (jetOfDatum_ae (le_refl 0) hz h)).symm
  rw [h1, h2, h3]

/-- The spatial slice of `f` at a future time is smooth on all of `R³`, from the
physical smoothness `ContDiffOn ℝ ∞ f futureDomain` (`futureDomain = Ici 0 ×ˢ univ`)
via `D01.contDiff_slice` on the horizon `[0, t+1)`. -/
theorem contDiff_slice_future {f : SpaceTimeField}
    (hf_smooth : ContDiffOn ℝ ∞ f futureDomain) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun x : Space => f (t, x)) := by
  have hmono : ContDiffOn ℝ ∞ f (Ico (0 : ℝ) (t + 1) ×ˢ (univ : Set Space)) := by
    refine hf_smooth.mono ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨hs.1, hx⟩
  exact contDiff_slice hmono ⟨ht, by linarith⟩

/-! ## 2. Unit U2 -/

/-- **C01 unit U2 / spec field `forceTimeRegularity`** (`research/C01/Spec.lean:326-329`;
paper `paper/sections/02-preliminaries.tex:17-19` eq:Rclasses, slicewise form of
`paper/sections/04-whole-space.tex:119` eq:RL2).

From `MemForceR f`: every future spatial slice is square integrable, and
`t ↦ ‖f(t)‖₂` is continuous on the closed half line `[0,∞)` (continuity holds on
all of `Ici 0`, endpoint `t = 0` included, because the `m = 0` datum path of
`MemForceR` is `ContDiffOn` on `futureTimes = Ici 0`).

The `m = 0` witness of `MemForceR` has datum order the cast `((0 : ℕ) : ℝ)`; the
whole proof is carried at that nat-cast order, matching the nat-indexed D01
lemmas, so no `((0 : ℕ) : ℝ) = 0` transport is needed. -/
theorem forceTimeRegularity :
    ∀ f : SpaceTimeField, MemForceR f →
      (∀ t : ℝ, 0 ≤ t → MemLp (slice f t) 2 volume) ∧
        ContinuousOn (fun s => l2Norm (slice f s)) (Ici (0 : ℝ)) := by
  intro f hf
  obtain ⟨hf_smooth, hforce⟩ := hf
  obtain ⟨G, hpath, hGsmooth, _, _⟩ := hforce 0
  have hGcont : ContinuousOn G (Ici (0 : ℝ)) := hGsmooth.continuousOn
  refine ⟨?_, ?_⟩
  · -- square integrability of each future slice
    intro t ht
    exact memLp_of_isSobolevDatum (contDiff_slice_future hf_smooth ht) (hpath t ht)
  · -- continuity of `s ↦ ‖f(s)‖₂` on the closed half line
    have hnorm : Continuous (fun A : RealVectorSobolev ((0 : ℕ) : ℝ) =>
        ‖jetOfDatum 0 0 (le_refl 0) A‖) :=
      continuous_norm.comp continuous_jetOfDatum_zero
    have hcomp : ContinuousOn (fun s => ‖jetOfDatum 0 0 (le_refl 0) (G s)‖) (Ici (0 : ℝ)) :=
      hnorm.comp_continuousOn hGcont
    refine hcomp.congr (fun t ht => ?_)
    have h0 : (0 : ℝ) ≤ t := ht
    exact l2Norm_eq_norm_jetOfDatum (contDiff_slice_future hf_smooth h0) (hpath t h0)

end NSFormalization.Section4.C01
