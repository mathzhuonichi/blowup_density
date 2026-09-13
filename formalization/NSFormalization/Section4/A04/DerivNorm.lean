import NSFormalization.Section4.A04.Continuity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A04 unit D1: the time derivative of the squared datum norm

`research/A04/COMPARISON.md` §4 unit **D1**.  The three differential fields of
the A04 draft — `energyIdentityHigh`, `regularizedNormDerivative`,
`highContinuationIntegral` (`research/A04/Spec.lean:424-510`) — measure the
solution on `sobolevNormAt (m:ℝ) w.velocity`, whose square must be shown
differentiable in time before any energy estimate can be stated.  The
differentiability input is the hypothesis `HasSmoothSobolevPath T u`
(`Spec.lean:247`, `REVIEW.md` finding 4): a datum path `G : ℝ → RealVectorSobolev m`
that is `C^∞` in time on `Ico 0 T` and represents `u`'s slices there.
`ClassicalSolutionR.sobolev` alone gives only a `ContinuousOn` path, which is why
the hypothesis is needed and is A01's obligation to produce.

This module turns that hypothesis into the inner-product derivative on the D01
datum carrier — pure Hilbert-space calculus once the path is given:

* `hasDerivAt_datumNormSq` — the row's literal statement: from `HasDerivAt G G' t`
  in the Hilbert space `RealVectorSobolev s`,
  `HasDerivAt (fun r => ‖G r‖^2) (2 * ⟪G t, G'⟫) t`.  A named specialisation of
  Mathlib's `HasDerivAt.norm_sq`.
* `hasDerivAt_datumPath` — the `C^∞`-in-time path is differentiable on the open
  interval `Ioo 0 T`, so `HasDerivAt G (deriv G t) t` there (`G' = deriv G`).
* `exists_hasDerivAt_sobolevNormAt_sq` — the payoff in the shape
  `energyIdentityHigh`'s LHS expects: from `HasSmoothSobolevPath T u`, at every
  integer order `m` there is a datum path `G` with `sobolevNormAt (m:ℝ) u r = ‖G r‖`
  on `Ico 0 T` and, on `Ioo 0 T`,
  `HasDerivAt (fun r => sobolevNormAt (m:ℝ) u r ^ 2) (2 * ⟪G t, deriv G t⟫) t`.
  The transport from `‖G r‖^2` to `sobolevNormAt (m:ℝ) u r ^ 2` is
  `sobolevNormAt_eq` (lane 039, `Continuity.lean`) fed through
  `HasDerivAt.congr_of_eventuallyEq` on the neighbourhood `Ioo 0 T`.

## The inner product on the datum carrier

`RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)`
(`Paper3/RealVectorPositiveDensity.lean:15`), i.e. `PiLp 2` over three copies of
`RealSobolevHilbert s = ↥(realSubspace s)`, a closed real submodule of the
weighted Fourier model `FourierData = Lp ℂ 2` (`Source/RealSobolev.lean:118,121`).
The carrier is genuinely a real Hilbert space, but before lane 053 Mathlib
registered the real inner product only through the `Submodule` view of the
closed subspace, not through the `ClosedSubmodule` sort directly, so
`Inner ℝ (RealVectorSobolev s)` was not found by instance search out of the box.
Lane 053 supplies the missing instance `Paper3.realSobolevInnerProductSpace`
(`Paper3/RealPositiveDensity.lean`, next to `realSobolevNormedAddCommGroup` and
`realSobolevNormedSpace`), as `inferInstanceAs` on `(realSubspace s).toSubmodule`
— the very `Submodule` those two instances are built from — so the inner
product's induced norm and `NormedSpace` are *defeq* to the ones `sobolevNormAt`
and `sobolevNormAt_eq` already use, with no diamond (checked:
`InnerProductSpace.toNormedSpace = realSobolevNormedSpace s` by `rfl`, and
`norm_eq_sqrt_re_inner` closes `‖x‖ = Real.sqrt ⟪x, x⟫` on the vector carrier).
`PiLp.innerProductSpace` then lifts it to `RealVectorSobolev s` automatically,
which is why nothing about the inner product needs to be declared in this leaf.

## Restated objects

Only `HasSmoothSobolevPath` is new here and is restated verbatim in §0 from
`research/A04/Spec.lean:247` with its source line — it is on no local module yet.
`sobolevNormAt` and its identification `sobolevNormAt_eq` are lane 039's, imported
from `Section4/A04/{Forcing,Continuity}`; `IsSobolevDatum` is lane 020/D01's;
`SpaceTimeField` is lane 032/A02's; `RealVectorSobolev` is Paper3's.  Nothing is
copied.
-/

noncomputable section

open Set
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff RealInnerProductSpace

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.D01 (IsSobolevDatum)

/-! ## 0. The A04 draft `def`, restated verbatim -/

/-- `research/A04/Spec.lean:247` `HasSmoothSobolevPath`, restated token-for-token:
"for every integer order the field has an order-`m` datum at every time of
`[0,T)` and that datum path is `C^∞` in time there".  This is A01's
`sobolev_smooth` clause (`REVIEW.md` finding 4); `Ico 0 T` is `UniqueDiffOn` so
the derivative at `t = 0` is the one-sided one and no negative-time extension is
differentiated. -/
def HasSmoothSobolevPath (T : ℝ) (u : SpaceTimeField) : Prop :=
  ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    (∀ t ∈ Ico (0 : ℝ) T,
        IsSobolevDatum (m : ℝ) (fun x : Space => u (t, x)) (G t)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)

/-! ## 1. The derivative of the squared norm on the Hilbert carrier -/

/-- **D1 core.**  The literal statement of the unit: on the real Hilbert space
`RealVectorSobolev s`, if the datum path `G` has derivative `G'` at `t`, then the
squared norm has derivative `2⟪G t, G'⟫` there.  A named specialisation of
`HasDerivAt.norm_sq` (`Mathlib/Analysis/InnerProductSpace/Calculus.lean`), the
same template as `EulerOrdinarySobolev.ordinaryWord_hasDerivWithinAt … .norm_sq`
(`Source/OrdinaryViscousStability.lean:88`). -/
theorem hasDerivAt_datumNormSq {s : ℝ} {G : ℝ → RealVectorSobolev s}
    {G' : RealVectorSobolev s} {t : ℝ} (hG : HasDerivAt G G' t) :
    HasDerivAt (fun r => ‖G r‖ ^ 2) (2 * ⟪G t, G'⟫) t :=
  hG.norm_sq

/-- A `C^∞`-in-time datum path on `Ico 0 T` is differentiable at every interior
time, with derivative `deriv G t`: `ContDiffOn.differentiableOn` on the closed
interval, upgraded to `HasDerivAt` on the open one because `Ico 0 T` is a
neighbourhood of every `t ∈ Ioo 0 T` (`Ico_mem_nhds`). -/
theorem hasDerivAt_datumPath {s T : ℝ} {G : ℝ → RealVectorSobolev s}
    (hGc : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt G (deriv G t) t :=
  ((hGc.differentiableOn (by simp) t (Ioo_subset_Ico_self ht)).differentiableAt
    (Ico_mem_nhds ht.1 ht.2)).hasDerivAt

/-- **D1 core, from the path regularity.**  Combining the two lemmas above: for a
`C^∞`-in-time datum path `G` on `Ico 0 T`, the squared norm has derivative
`2⟪G t, deriv G t⟫` at every interior time (`G'` is the derivative of the path). -/
theorem hasDerivAt_datumNormSq_of_contDiffOn {s T : ℝ} {G : ℝ → RealVectorSobolev s}
    (hGc : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => ‖G r‖ ^ 2) (2 * ⟪G t, deriv G t⟫) t :=
  hasDerivAt_datumNormSq (hasDerivAt_datumPath hGc ht)

/-! ## 2. D1 payoff: the derivative of `sobolevNormAt (m:ℝ) u · ^ 2` -/

/-- **D1.**  From `HasSmoothSobolevPath T u`, at every integer order `m` there is
a datum path `G` such that

* `sobolevNormAt (m:ℝ) u r = ‖G r‖` on `Ico 0 T` (the identification of the
  fail-safe `.toReal` norm with the honest datum norm, `sobolevNormAt_eq`), and
* on `Ioo 0 T`,
  `HasDerivAt (fun r => sobolevNormAt (m:ℝ) u r ^ 2) (2 * ⟪G t, deriv G t⟫) t`.

The second conjunct is `hasDerivAt_datumNormSq_of_contDiffOn` transported from
`‖G ·‖^2` to `sobolevNormAt (m:ℝ) u · ^ 2` through `HasDerivAt.congr_of_eventuallyEq`:
the two functions agree on the neighbourhood `Ioo 0 T ⊆ Ico 0 T` by
`sobolevNormAt_eq`.  This is the exact left-hand side
`energyIdentityHigh` (`Spec.lean:429`) needs: `∃ d, HasDerivAt (fun r =>
sobolevNormAt (m:ℝ) w.velocity r ^ 2) d t`, with `d = 2⟪G t, deriv G t⟫`
identified so that unit **G1** can bound it. -/
theorem exists_hasDerivAt_sobolevNormAt_sq
    {T : ℝ} {u : SpaceTimeField} (h : HasSmoothSobolevPath T u) (m : ℕ) :
    ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      (∀ r ∈ Ico (0 : ℝ) T, sobolevNormAt (m : ℝ) u r = ‖G r‖) ∧
        ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun r => sobolevNormAt (m : ℝ) u r ^ 2)
            (2 * ⟪G t, deriv G t⟫) t := by
  obtain ⟨G, hGd, hGc⟩ := h m
  refine ⟨G, ?_, ?_⟩
  · intro r hr
    exact sobolevNormAt_eq (hGd r hr)
  · intro t ht
    refine (hasDerivAt_datumNormSq_of_contDiffOn hGc ht).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    rw [sobolevNormAt_eq (hGd r (Ioo_subset_Ico_self hr))]

end NSFormalization.Section4.A04
