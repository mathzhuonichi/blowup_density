import NSFormalization.Section4.A01.CarrierBridge

/-!
# C1b (order 0): the datum path is continuous (row `C1b-c8-0`)

Row **C1b-c8-0** of `research/A01/C1B_SPLIT.md`.  Lane 119
(`Section4/A01/CarrierBridge.lean`) proved that every ordinary `L²` field
`U : EulerMeanSolenoidal.L2` carries the D01 order-0 angular Sobolev datum
`orderZeroDatum (Lp.memLp U)` (`isSobolevDatum_zero_ordinaryL2`).  This module
shows that datum depends **continuously** on `U`, which is the order-0 half of
the `∀ m, ∃ G, ContinuousOn G ∧ IsSobolevDatum m (velocity t) (G t)` obligation
`c8` (`verification/Contracts/V1/Data.lean:643`).

## Route (no new analysis)

`orderZeroDatum hz` (`D01/OrderZeroDatum.lean:96`) is a composition of maps each
of which is already a continuous linear map or continuous linear equiv in the
tree.  Reading the definition from the inside out, for `hz = Lp.memLp u`:

* `componentLp (Lp.memLp u) i` (`D01/OrderZeroDatum.lean:72`) is the `L²` class of
  the real `i`-th component.  It is **not** written as a map of `u`, but it agrees
  a.e. with `fun x => ((u x i : ℝ) : ℂ)`, hence equals, as an `Lp` element, the
  continuous linear map
  `(Complex.ofRealCLM.comp (EuclideanSpace.proj i)).compLpL 2 volume` applied to
  `u` (`componentLp_eq_compLpL`; `ContinuousLinearMap.compLpL`,
  `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:817`).
* `𝓕` is `fourierCLM ℂ (Lp ℂ 2 volume) : Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume`
  (`fourierCLM`, `Mathlib/Analysis/Fourier/Notation.lean:167`; the same instance
  `D01/SmoothDatum.lean:114` uses), restricted to `ℝ`.
* `realProjectionTo 0 : SobolevHilbert 0 →L[ℝ] RealSobolevHilbert 0`
  (`Paper3/RealPositiveDensity.lean:31`).
* `WithLp.toLp 2` is `(PiLp.continuousLinearEquiv 2 ℝ _).symm` on the nose
  (`Mathlib/Analysis/Normed/Lp/PiLp.lean:1150`, `= toLp p` by `rfl`).
* `cyclesToAngularRealVector 0 : RealVectorSobolev 0 ≃L[ℝ] RealVectorSobolev 0`
  (`Paper3/AngularRealVectorBochner.lean:15`).

`orderZeroDatumCLM` bundles these into a single continuous linear map, and
`orderZeroDatum_memLp_eq` proves `orderZeroDatum (Lp.memLp u) = orderZeroDatumCLM u`
for every `u` (by rewriting the only non-defeq step, `componentLp_eq_compLpL`, and
`rfl` on the rest).  Continuity of the datum path then transports through that
equation.  No norm identity is used (none is available; `OrderZeroDatum.lean:40-53`).

## What is proved

* `componentLp_eq_compLpL` — the componentwise `L²` seed as a `compLpL`.
* `orderZeroDatumCLM` / `orderZeroDatum_memLp_eq` — the explicit CLM form.
* `continuous_orderZeroDatum` — row `C1b-c8-0` verbatim: for any continuous
  `U : X → EulerMeanSolenoidal.L2`, `fun t => orderZeroDatum (Lp.memLp (U t))` is
  continuous.
* `datumPath` / `continuousOn_datumPath` — the `ContinuousOn (Ico 0 T)` form for a
  bundled path `U : C(Icc 0 T, EulerMeanSolenoidal.L2)` as
  `Source.OrdinaryForcedLocal.exists_local` (`Source/OrdinaryForcedLocal.lean:32`)
  produces it.
* `datumPath_isSobolevDatum` — the `m = 0` case of the shape of
  `ClassicalSolutionR.sobolev` (`Data.lean:643`): given the B1 a.e. hand-off
  `velocity t =ᵐ ⇑(U t)` on `Ico 0 T` (row `C1b-rep`), the datum path is continuous
  on `Ico 0 T` and realizes the velocity slice at every `t ∈ Ico 0 T`.

## Scope

Order 0 only.  The order-`m ≥ 1` continuity (row `C1b-c8-m`) needs the vector
order-`m` Plancherel isometry, which is absent from the tree; the `∀ m` on one
horizon `T` is additionally gated by A3.  See `research/A01/C1B_SPLIT.md`.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev cyclesToAngularRealVector realProjectionTo)
open NSFormalization.Source.RealSobolev (RealSobolevHilbert)
open NavierStokes.ProblemStatement (Space)
open FourierTransform

/-- The `i`-th real-component-to-`L²ℂ` map, as a continuous linear map of the
ordinary `L²` field: real projection onto coordinate `i`, then inclusion `ℝ ↪ ℂ`,
lifted to `Lp` by `ContinuousLinearMap.compLpL`. -/
def componentCLM (i : Fin 3) :
    EulerMeanSolenoidal.L2 →L[ℝ] Lp ℂ 2 (volume : Measure Space) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).compLpL 2 volume

/-- The order-0 `L²` component seed `componentLp` is exactly `componentCLM` applied
to the field.  `componentLp` is defined by `MemLp.toLp` on a proof, not as a map of
`u`; both sides agree a.e. with `x ↦ ((u x i : ℝ) : ℂ)`, so they are equal as `Lp`
elements. -/
theorem componentLp_eq_compLpL (u : EulerMeanSolenoidal.L2) (i : Fin 3) :
    componentLp (Lp.memLp u) i = componentCLM i u := by
  apply Lp.ext
  filter_upwards [componentLp_ae (Lp.memLp u) i,
    ContinuousLinearMap.coeFn_compLpL (Complex.ofRealCLM.comp (EuclideanSpace.proj i)) u]
    with x h1 h2
  simp only [componentCLM]
  rw [h1, h2]
  rfl

/-- **The explicit CLM form of the order-0 datum.**  The order-0 angular
real-vector Sobolev datum of a square-integrable field, assembled from the
continuous linear factors of `orderZeroDatum`: componentwise `L²` inclusion,
Fourier transform, real projection, `PiLp` assembly, and the angular-convention
transport `cyclesToAngularRealVector 0`. -/
def orderZeroDatumCLM : EulerMeanSolenoidal.L2 →L[ℝ] RealVectorSobolev (0:ℝ) :=
  (cyclesToAngularRealVector (0:ℝ)).toContinuousLinearMap.comp <|
    (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin 3 => RealSobolevHilbert (0:ℝ))).symm.toContinuousLinearMap.comp <|
      ContinuousLinearMap.pi fun i =>
        (realProjectionTo (0:ℝ)).comp <|
          ((fourierCLM ℂ (Lp ℂ 2 (volume : Measure Space))).restrictScalars ℝ).comp
            (componentCLM i)

/-- `orderZeroDatum (Lp.memLp u)` is `orderZeroDatumCLM u`: the only non-`rfl` step
is `componentLp_eq_compLpL`; every other factor of `orderZeroDatum`
(`fourierCLM`/`restrictScalars`/`realProjectionTo`/`WithLp.toLp`/
`cyclesToAngularRealVector`) matches its bundled counterpart definitionally. -/
theorem orderZeroDatum_memLp_eq (u : EulerMeanSolenoidal.L2) :
    orderZeroDatum (Lp.memLp u) = orderZeroDatumCLM u := by
  have key : (fun i => realProjectionTo (0:ℝ) (𝓕 (componentLp (Lp.memLp u) i)))
      = (fun i => realProjectionTo (0:ℝ) (𝓕 (componentCLM i u))) := by
    funext i; rw [componentLp_eq_compLpL u i]
  unfold orderZeroDatum
  rw [key]
  rfl

/-- **Row C1b-c8-0.**  The order-0 datum of a continuously-varying ordinary `L²`
field varies continuously. -/
theorem continuous_orderZeroDatum {X : Type*} [TopologicalSpace X]
    (U : X → EulerMeanSolenoidal.L2) (hU : Continuous U) :
    Continuous (fun t => orderZeroDatum (Lp.memLp (U t))) := by
  have h : (fun t => orderZeroDatum (Lp.memLp (U t))) = fun t => orderZeroDatumCLM (U t) := by
    funext t; exact orderZeroDatum_memLp_eq (U t)
  rw [h]
  exact orderZeroDatumCLM.continuous.comp hU

/-- The order-0 datum path of a bundled continuous `L²` path
`U : C(Icc 0 T, EulerMeanSolenoidal.L2)` (the shape `exists_local` produces),
extended by `0` off `Icc 0 T` so that it is total (`ℝ → RealVectorSobolev 0`). -/
def datumPath {T : ℝ} (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2)) :
    ℝ → RealVectorSobolev (0:ℝ) :=
  fun t => if h : t ∈ Set.Icc (0:ℝ) T then orderZeroDatumCLM (U ⟨t, h⟩) else 0

/-- **Row C1b-c8-0, `ContinuousOn` form.**  The datum path is continuous on
`Ico 0 T`. -/
theorem continuousOn_datumPath {T : ℝ} (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2)) :
    ContinuousOn (datumPath U) (Set.Ico (0:ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hEq : (Set.Ico (0:ℝ) T).domRestrict (datumPath U)
      = fun x => orderZeroDatumCLM (U (Set.inclusion Set.Ico_subset_Icc_self x)) := by
    funext x
    simp only [Set.domRestrict_apply, datumPath, dite_eq_left (Set.Ico_subset_Icc_self x.2)]
  rw [hEq]
  exact orderZeroDatumCLM.continuous.comp (U.continuous.comp (continuous_inclusion _))

/-- **The `m = 0` case of the shape of `ClassicalSolutionR.sobolev`
(`verification/Contracts/V1/Data.lean:643`).**  Given the forced-local path
`U : C(Icc 0 T, EulerMeanSolenoidal.L2)` and a spacetime velocity `v` whose slice
agrees a.e. with `⇑(U t)` on `Ico 0 T` (the B1 hand-off, row `C1b-rep`), the datum
path `datumPath U` is continuous on `Ico 0 T` and is an order-0 Sobolev datum of
the velocity slice at every interior time.  Combines lane 119's
`isSobolevDatum_zero_ordinaryL2` with `IsSobolevDatum.congr_field`. -/
theorem datumPath_isSobolevDatum {T : ℝ}
    (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2)) (v : ℝ × Space → Space)
    (hv : ∀ t (ht : t ∈ Set.Ico (0:ℝ) T),
      (fun x => v (t, x)) =ᵐ[volume] ⇑(U ⟨t, Set.Ico_subset_Icc_self ht⟩)) :
    ContinuousOn (datumPath U) (Set.Ico (0:ℝ) T) ∧
      ∀ t ∈ Set.Ico (0:ℝ) T, IsSobolevDatum 0 (fun x => v (t, x)) (datumPath U t) := by
  refine ⟨continuousOn_datumPath U, fun t ht => ?_⟩
  have hmem : t ∈ Set.Icc (0:ℝ) T := Set.Ico_subset_Icc_self ht
  have hdatum : datumPath U t = orderZeroDatum (Lp.memLp (U ⟨t, hmem⟩)) := by
    simp only [datumPath, dite_eq_left hmem]
    exact (orderZeroDatum_memLp_eq (U ⟨t, hmem⟩)).symm
  rw [hdatum]
  exact IsSobolevDatum.congr_field (isSobolevDatum_zero_ordinaryL2 (U ⟨t, hmem⟩)) (hv t ht).symm

end NSFormalization.Section4.A01
