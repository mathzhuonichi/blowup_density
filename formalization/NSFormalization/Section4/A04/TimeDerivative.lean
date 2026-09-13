import NSFormalization.Section4.A04.Continuity
import NSFormalization.Section4.D01.DatumToJets
import NSFormalization.Section4.A03.ScalarTameProduct
import NSFormalization.Section4.A03.VectorTameProduct
import NSFormalization.Paper3.AngularTameProduct
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# A04 unit G1, sub-lemma SL1 / unit D2: `deriv G t` is the datum of `∂ₜu(t,·)`

`research/A04/G1_SPLIT.md` sub-lemma **SL1** (= unit **D2**).  The energy identity
eq:Rhigh (`Spec.lean` `energyIdentityHigh`) measures the solution through the D1
datum path `G` and its time derivative `deriv G t`.  D2 is the identification of
that abstract Hilbert-space derivative with the **datum of the physical time
derivative** `∂ₜu(t,·)`:

* every slice `r ↦ u(r,x)` is differentiable in time at every interior `t`
  (existence), and
* `deriv G t` is the order-`m` angular Sobolev datum of `x ↦ ∂ₜu(t,x)`
  (identification).

**This closes SL1 with no A01 clause and no dominated convergence.**  An earlier
split entry rated D2 an **L** lemma blocked on an unowned A01 `C^∞_{t,x}` clause
(the difference-quotient route needs a limit inside the Schwartz pairing).
`REVIEW_G1.md` finding 2 shows that route is unnecessary: the *bounded
representative* `Paper3.angularBoundedRepresentative s hs`
(`AngularTameProduct.lean:141`, a CLM `Lp ℂ 2 →L[ℝ] BoundedContinuousFunction`,
`2 ≤ s`) turns the Hilbert-space derivative into a **pointwise** derivative for
free via `HasFDerivAt.comp_hasDerivAt`, and `A03.representative_ae` +
`Continuous.ae_eq_iff_eq` pin that representative to the physical field.  The
imaginary part is the derivative of the constant `0` (`HasDerivAt.unique`), and
`Paper3.angularRealization_boundedRepresentative` converts back to
`IsSobolevDatum`.  The regularity actually used — each slice continuous and in
`L²` — is a **field of `ClassicalSolutionR`** (`velocity_smooth` + `sobolev`),
already on `erenup/integration`, through `D01.contDiff_slice` and
`D01.memLp_of_isSobolevDatum`.

## Contents

* `evalRep`, `hasDerivAt_rep`, `representative_eq` — the scalar bounded-representative
  plumbing.
* `d2_scalar` — D2 for a scalar spacetime field: existence of the pointwise time
  derivative and the scalar datum identification.  (`REVIEW_G1.md` finding 2's
  compiled proof, lifted verbatim.)
* `timeDeriv_isSobolevDatum` — **SL1/D2, the vector statement**, the deliverable:
  componentwise (`A03.isSobolevDatum_iff`), with the existence conjunct coming
  directly from the joint time–space smoothness `velocity_smooth` and the
  identification from `d2_scalar` per component, glued by
  `HasDerivAt.deriv` and the `PiLp` projection CLM.

The datum-side derivative field is written `fun x => deriv (fun r => u(r,x)) t`;
its `i`-th component equals `deriv (fun r => u(r,x) i) t` because the vector slice
is differentiable, which is how the componentwise scalar data reassemble.  This
is the manuscript's `∂ₜu(t,·)` (`= temporalDerivative w.velocity t x`, since
`HasDerivAt` pins `fderiv (fun s => u(s,x)) t 1 = deriv (fun s => u(s,x)) t`).

## Reuse

`angularBoundedRepresentative`, `angularRealization_boundedRepresentative` are
Paper3's; `representative_ae`, `locallyIntegrable_ofReal`, `IsScalarSobolevDatum`,
`isSobolevDatum_iff`, `IsSobolevDatum.component` are A03's; `contDiff_slice`,
`memLp_of_isSobolevDatum`, `IsSobolevDatum` are D01's; `ClassicalSolutionR`,
`SpaceTimeField` are A02's; `RealVectorSobolev` is Paper3's.  Nothing is copied.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal Topology

namespace NSFormalization.Section4.A04

open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NSFormalization.Section4.D01 (IsSobolevDatum contDiff_slice memLp_of_isSobolevDatum)
open NSFormalization.Section4.A03
  (IsScalarSobolevDatum representative_ae locallyIntegrable_ofReal isSobolevDatum_iff
   IsSobolevDatum.component)

/-! ## 1. The scalar bounded-representative plumbing -/

/-- Evaluation of the bounded continuous representative of an order-`s` scalar
datum at a point `x`, as a continuous linear map `RealSobolevHilbert s →L[ℝ] ℂ`:
`angularBoundedRepresentative` (needs `2 ≤ s`) into `BoundedContinuousFunction`,
then `BoundedContinuousFunction.evalCLM ℝ x`. -/
def evalRep (s : ℝ) (hs : 2 ≤ s) (x : Space) : RealSobolevHilbert s →L[ℝ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp
    ((angularBoundedRepresentative s hs).comp (RealSobolevHilbert s).subtypeL)

/-- The pointwise representative is a continuous-linear image of the datum, so a
Hilbert-space time derivative of the datum path transports to a pointwise time
derivative of the representative at every `x` (`HasFDerivAt.comp_hasDerivAt`). -/
theorem hasDerivAt_rep (s : ℝ) (hs : 2 ≤ s) {G : ℝ → RealSobolevHilbert s}
    {G' : RealSobolevHilbert s} {t : ℝ} (h : HasDerivAt G G' t) (x : Space) :
    HasDerivAt (fun r => angularBoundedRepresentative s hs ((G r : FourierData)) x)
      (angularBoundedRepresentative s hs ((G' : FourierData)) x) t :=
  (evalRep s hs x).hasFDerivAt.comp_hasDerivAt t h

/-- The bounded continuous representative of an order-`s` scalar datum (`2 ≤ s`)
**is** the physical field pointwise, when the field is continuous and `L²`:
`representative_ae` gives a.e. equality of two continuous functions, upgraded to
equality by `Continuous.ae_eq_iff_eq`. -/
theorem representative_eq {s : ℝ} (hs : 2 ≤ s) {a : Space → ℝ}
    (hcont : Continuous a) (hmem : MemLp a 2 volume)
    {A : RealSobolevHilbert s} (hA : IsScalarSobolevDatum s a A) (x : Space) :
    angularBoundedRepresentative s hs (A : FourierData) x = ((a x : ℝ) : ℂ) :=
  congrFun (((map_continuous (angularBoundedRepresentative s hs (A : FourierData))).ae_eq_iff_eq
    volume (Complex.continuous_ofReal.comp hcont)).mp
      (representative_ae hs (locallyIntegrable_ofReal hmem) hA)) x

/-! ## 2. D2 for a scalar spacetime field -/

/-- **SL1/D2, scalar case.**  For a scalar spacetime field `u` whose slices are
continuous and `L²` on `Ico 0 T` and represented there by a datum path `G` that
is differentiable at an interior time `t` (`HasDerivAt G G' t`):

* every slice `r ↦ u(r,x)` is differentiable at `t` (existence), and
* `G'` is the order-`s` scalar datum of `x ↦ ∂ₜu(t,x) = deriv (fun r => u(r,x)) t`.

The derivative is real because its imaginary part is the derivative of the
constant `0`. -/
theorem d2_scalar {s : ℝ} (hs : 2 ≤ s) {T : ℝ} {u : ℝ × Space → ℝ}
    (hu : ∀ r ∈ Ico (0 : ℝ) T, Continuous fun x : Space => u (r, x))
    (hmem : ∀ r ∈ Ico (0 : ℝ) T, MemLp (fun x : Space => u (r, x)) 2 volume)
    {G : ℝ → RealSobolevHilbert s}
    (hG : ∀ r ∈ Ico (0 : ℝ) T, IsScalarSobolevDatum s (fun x => u (r, x)) (G r))
    {G' : RealSobolevHilbert s} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (h : HasDerivAt G G' t) :
    (∀ x : Space, HasDerivAt (fun r => u (r, x))
        (angularBoundedRepresentative s hs (G' : FourierData) x).re t) ∧
      IsScalarSobolevDatum s (fun x => deriv (fun r => u (r, x)) t) G' := by
  have hnb : Ico (0 : ℝ) T ∈ 𝓝 t := Ico_mem_nhds ht.1 ht.2
  have hd : ∀ x : Space, HasDerivAt (fun r => ((u (r, x) : ℝ) : ℂ))
      (angularBoundedRepresentative s hs (G' : FourierData) x) t := by
    intro x
    refine (hasDerivAt_rep s hs h x).congr_of_eventuallyEq ?_
    filter_upwards [hnb] with r hr
    exact (representative_eq hs (hu r hr) (hmem r hr) (hG r hr) x).symm
  have him : ∀ x : Space, (angularBoundedRepresentative s hs (G' : FourierData) x).im = 0 := by
    intro x
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hd x)
    simp only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] at h1
    exact ((hasDerivAt_const t (0 : ℝ)).unique h1).symm
  have hre : ∀ x : Space,
      (((angularBoundedRepresentative s hs (G' : FourierData) x).re : ℝ) : ℂ)
        = angularBoundedRepresentative s hs (G' : FourierData) x := by
    intro x; exact Complex.ext (by simp) (by simp [him x])
  have hreal : ∀ x : Space, HasDerivAt (fun r => u (r, x))
      (angularBoundedRepresentative s hs (G' : FourierData) x).re t := by
    intro x
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd x)
    simpa [Function.comp_def] using h1
  refine ⟨hreal, ?_⟩
  intro ψ
  rw [angularRealization_boundedRepresentative s hs (G' : FourierData) ψ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ψ x * angularBoundedRepresentative s hs (G' : FourierData) x
      = ψ x * (((deriv (fun r => u (r, x)) t : ℝ) : ℂ))
  rw [(hreal x).deriv, hre x]

/-! ## 3. SL1/D2, the vector statement (the deliverable) -/

/-- **SL1 / unit D2.**  On a forced viscous classical solution `w`, for `2 ≤ m` and
a `C^∞`-in-time datum path `G` representing the velocity slices on `Ico 0 T`
(the `HasSmoothSobolevPath` hypothesis of the energy fields), at every interior
time `t`:

* the pointwise time derivative `∂ₜu(t,x)` exists for every `x`
  (`HasDerivAt (fun r => w.velocity (r,x)) (deriv (fun r => w.velocity (r,x)) t) t`,
  from the joint smoothness `velocity_smooth`); and
* `deriv G t` is the order-`m` datum of the physical time-derivative field
  `x ↦ ∂ₜu(t,x)` (`IsSobolevDatum (m:ℝ) (fun x => deriv (fun r => w.velocity (r,x)) t)
  (deriv G t)`).

The identification is componentwise (`isSobolevDatum_iff`): the `i`-th component
of `deriv G t` is the derivative of the `i`-th datum-path component (`PiLp`
projection CLM), which `d2_scalar` identifies with the datum of the `i`-th slice's
time derivative; that scalar derivative is the `i`-th component of the vector time
derivative because the vector slice is differentiable (`HasDerivAt.deriv`). -/
theorem timeDeriv_isSobolevDatum
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {m : ℕ} (hm : 2 ≤ m)
    {G : ℝ → RealVectorSobolev (m : ℝ)}
    (hGd : ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => w.velocity (t, x)) (G t))
    (hGc : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (∀ x : Space, HasDerivAt (fun r => w.velocity (r, x))
        (deriv (fun r => w.velocity (r, x)) t) t) ∧
      IsSobolevDatum (m : ℝ)
        (fun x => deriv (fun r => w.velocity (r, x)) t) (deriv G t) := by
  have hsR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  -- (1) existence: the velocity is smooth in time on `Ico 0 T`, hence differentiable at `t`
  have hvelx : ∀ x : Space, HasDerivAt (fun r => w.velocity (r, x))
      (deriv (fun r => w.velocity (r, x)) t) t := by
    intro x
    have hmap : ContDiffOn ℝ ∞ (fun r : ℝ => ((r, x) : ℝ × Space)) (Ico (0 : ℝ) T) :=
      (contDiff_id.prodMk contDiff_const).contDiffOn
    have hsub : (Ico (0 : ℝ) T) ⊆
        (fun r : ℝ => ((r, x) : ℝ × Space)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
      fun r hr => ⟨hr, mem_univ x⟩
    have hcd : ContDiffOn ℝ ∞ (fun r => w.velocity (r, x)) (Ico (0 : ℝ) T) :=
      w.velocity_smooth.comp hmap hsub
    exact ((hcd.differentiableOn (by simp) t (Ioo_subset_Ico_self ht)).differentiableAt
      (Ico_mem_nhds ht.1 ht.2)).hasDerivAt
  refine ⟨hvelx, ?_⟩
  -- (2) datum identification, componentwise
  have hGderiv : HasDerivAt G (deriv G t) t :=
    ((hGc.differentiableOn (by simp) t (Ioo_subset_Ico_self ht)).differentiableAt
      (Ico_mem_nhds ht.1 ht.2)).hasDerivAt
  have hGi : ∀ i : Fin 3, HasDerivAt (fun r => (G r) i) ((deriv G t) i) t := fun i =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => RealSobolevHilbert (m : ℝ)) i).hasFDerivAt.comp_hasDerivAt
      t hGderiv
  have hconti : ∀ (i : Fin 3), ∀ r ∈ Ico (0 : ℝ) T,
      Continuous fun x : Space => w.velocity (r, x) i := fun i r hr =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp
      (contDiff_slice w.velocity_smooth hr).continuous
  have hmemi : ∀ (i : Fin 3), ∀ r ∈ Ico (0 : ℝ) T,
      MemLp (fun x : Space => w.velocity (r, x) i) 2 volume := fun i r hr =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).comp_memLp'
      (memLp_of_isSobolevDatum (contDiff_slice w.velocity_smooth hr) (hGd r hr))
  have hGdi : ∀ (i : Fin 3), ∀ r ∈ Ico (0 : ℝ) T,
      IsScalarSobolevDatum (m : ℝ) (fun x => w.velocity (r, x) i) ((G r) i) := fun i r hr =>
    IsSobolevDatum.component (hGd r hr) i
  refine (isSobolevDatum_iff (m : ℝ) _ (deriv G t)).mpr (fun i => ?_)
  have hveli : ∀ x : Space, HasDerivAt (fun r => w.velocity (r, x) i)
      ((deriv (fun r => w.velocity (r, x)) t) i) t := fun x =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt t (hvelx x)
  have hsc := (d2_scalar (u := fun z : ℝ × Space => w.velocity z i) hsR (hconti i) (hmemi i)
    (hGdi i) ht (hGi i)).2
  have hfield : (fun x : Space => (deriv (fun r => w.velocity (r, x)) t) i)
      = (fun x : Space => deriv (fun r => w.velocity (r, x) i) t) :=
    funext fun x => ((hveli x).deriv).symm
  rw [hfield]
  exact hsc

end NSFormalization.Section4.A04
