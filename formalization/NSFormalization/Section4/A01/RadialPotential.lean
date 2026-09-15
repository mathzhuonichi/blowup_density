import Euler.CompactParameterIntegral
import NavierStokes.ProblemStatement
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# A01 · unit P1: the radial pressure potential differentiates back to its gradient

`paper/sections/02-preliminaries.tex:96-100`.  The manuscript's two-line
argument: if a spatial field `G` has a symmetric Jacobian (`∂_jG_k = ∂_kG_j`,
which is `02-preliminaries.tex:94`, the consequence of `Ĝ ∥ ξ`), then the scalar
radial potential `p(x) = ∫₀¹ G(rx)·x dr` recovers `G` as its gradient:
`∂_j p = ∫₀¹ ∂_r [r G_j(rx)] dr = G_j(x)`.

This discharges the pointwise gradient identity that is the core of the
`ManuscriptLocalRegularity.pressure_potential` field of the A01 contract
(`research/A01/Spec.lean:227`, `PressureGaugeEquivOn`) and simultaneously D01's
unit L9(b).

## What is proved

* `hasFDerivAt_radialPotential` — `∇(∫₀¹ ⟨G(r·), ·⟩ dr) = G` at every point,
  as `HasFDerivAt ... (innerSL ℝ (G x)) x`, for `G` with a symmetric Jacobian
  and `ContDiff ℝ ∞ G`.
* `pressureGradient_pressurePotential` — the spacetime corollary: for the
  manuscript's radial potential `pressurePotential G'` of a spacetime field
  whose slice `G' (t, ·) = G`, the (upstream) `pressureGradient` of that
  potential equals `G` at time `t`.
* `inner_fderiv_symm` — the algebraic core: a symmetric Jacobian makes the
  bilinear form `⟪DG(z) v, w⟫` symmetric in `v, w`.

## Hypothesis note

The differentiation-under-the-integral step reuses the *proven* compact
parameter-integral machinery `EulerCompactParameterIntegral.integral_hasFDerivAt`
(`vendor/NavierStokesAndEuler/Euler/CompactParameterIntegral.lean`).  That lemma
is **stated** at `ContDiff ℝ ∞`, so we assume `ContDiff ℝ ∞ G` in addition to
`HasSymmetricJacobian G`.

`ContDiff ℝ ∞` is a *convenience, not a requirement*: the whole proof — the
vendor lemma included — uses only `hsmooth.continuous`, `hsmooth.differentiable`
and `Continuous (fderiv ℝ G)`, all of which hold at `ContDiff ℝ 1 G`
(equivalently `Differentiable ℝ G ∧ Continuous (fderiv ℝ G)`), so the minimal
mathematical hypothesis is `ContDiff ℝ 1 G` (lane-101 reviewer transcribed the
vendor proof verbatim with `∞ → 1`, 22 lines, and it compiles).  We keep the
statement at `∞` deliberately: forking a vendor lemma to save one derivative
order is not worth it, the intended consumer supplies `∞` (`G = ∇p` and
`ClassicalSolutionR.pressure_smooth` is `ContDiffOn ℝ ∞`, `research/A01/Spec.lean:117`),
and the manuscript's own hypothesis is `H^∞` (`02-preliminaries.tex:91`).  A C¹
variant would be a vendor-side change; see `research/A01/ATTEMPTS_P1.md` bullet 1.

`hG.1` (`Differentiable ℝ G`) is *not load-bearing in this proof* — every
differentiability fact comes from `hsmooth`, and `inner_fderiv_symm` discards
`hG.1`.  It is kept because it is part of the `Spec.lean` predicate for the
reason `research/A01/REVIEW.md` H2 gives (without it `IsLerayComplement` ceases
to be single-valued); fidelity to the spec beats minimality here.

`inner_fderiv_symm`'s symmetric-Jacobian hypothesis is spelled differently from
the curl-free condition of `Section4/D01/Longitudinal.lean:65,174` (there:
`partialDeriv i Z.field x j = partialDeriv j Z.field x i` on a `SmoothL2Field`,
landing in Fourier space).  Different carrier and conclusion, not a duplication;
a one-line bridge lemma will eventually connect D01's SL5 output to this
potential (flagged for the `IsLerayComplement` / P3 lane).

## Restated definitions

`NSFormalization` is a dependency of the `Contracts` library and cannot import
it, so the two objects this unit needs are restated verbatim here; the
`verification/Bindings` `rfl` bridge is a later lane.

* `pressurePotential` is `verification/Contracts/V1/Data.lean:596`.
* `HasSymmetricJacobian` is `research/A01/Spec.lean:119` (contract draft
  `BlowupDensity.A01.Draft.HasSymmetricJacobian`).
-/

noncomputable section
namespace NSFormalization.Section4.A01.RadialPotential

open NavierStokes.ProblemStatement
open Set MeasureTheory
open scoped ContDiff RealInnerProductSpace

/-- `Data.lean:99` `SpatialField`. -/
abbrev SpatialField := Space → Space
/-- `Data.lean` `SpaceTimeField` (= `VelocityField`). -/
abbrev SpaceTimeField := VelocityField
/-- `Data.lean` `SpaceTimeScalar` (= `PressureField`). -/
abbrev SpaceTimeScalar := PressureField

/-- `verification/Contracts/V1/Data.lean:596` `pressurePotential`: the
manuscript's explicit radial potential `p(x,t) = ∫₀¹ G(rx,t)·x dr`
(`02-preliminaries.tex:96-100`). -/
def pressurePotential (G : SpaceTimeField) : SpaceTimeScalar :=
  fun z => ∫ r in (0:ℝ)..1, (inner ℝ (G (z.1, r • z.2)) z.2 : ℝ)

/-- `research/A01/Spec.lean:119` `HasSymmetricJacobian`: `G` is differentiable
and its spatial Jacobian is symmetric, `∂_iG_j = ∂_jG_i` (`02-preliminaries.tex:94`,
the consequence of `Ĝ ∥ ξ`). -/
def HasSymmetricJacobian (G : SpatialField) : Prop :=
  Differentiable ℝ G ∧
    ∀ x : Space, ∀ i j : Fin 3,
      (fderiv ℝ G x (coordinateVector i)) j = (fderiv ℝ G x (coordinateVector j)) i

/-- A symmetric Jacobian gives a symmetric bilinear form:
`⟪DG(z) v, w⟫ = ⟪DG(z) w, v⟫`.  This is the algebraic content of
`02-preliminaries.tex:94` that turns `⟪DG(rx) v, x⟫` into `r ⟪DG(rx) x, v⟫`
inside the radial computation. -/
theorem inner_fderiv_symm {G : SpatialField} (hG : HasSymmetricJacobian G) (z v w : Space) :
    (inner ℝ (fderiv ℝ G z v) w : ℝ) = inner ℝ (fderiv ℝ G z w) v := by
  obtain ⟨-, hsym⟩ := hG
  have hsym' := hsym z
  have expand : ∀ (u : Space),
      u = u 0 • coordinateVector 0 + u 1 • coordinateVector 1 + u 2 • coordinateVector 2 := by
    intro u; ext i; fin_cases i <;> simp [coordinateVector]
  have basis_inner : ∀ (u : Space) (j : Fin 3),
      (inner ℝ u (coordinateVector j) : ℝ) = u j := by
    intro u j
    rw [coordinateVector, EuclideanSpace.inner_single_right]; simp
  rw [expand v, expand w]
  simp only [map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  simp only [basis_inner]
  rw [hsym' 1 0, hsym' 2 0, hsym' 2 1]
  ring

/-- **`∇(radial potential) = G`** (`02-preliminaries.tex:96-100`).  For a spatial
field `G` with a symmetric Jacobian that is smooth, the scalar potential
`y ↦ ∫₀¹ ⟨G(ry), y⟩ dr` has Fréchet derivative `v ↦ ⟨G x, v⟩` at every point `x`,
i.e. its gradient is `G`.

The manuscript's proof, formalised: differentiate under the integral
(`EulerCompactParameterIntegral.integral_hasFDerivAt`), compute the slice
derivative `⟨DG(rx)(rv), x⟩ + ⟨G(rx), v⟩`, use the symmetric Jacobian
(`inner_fderiv_symm`) to rewrite it as `∂_r ⟨r G(rx), v⟩`, and apply the
fundamental theorem of calculus to `r ↦ r ⟨G(rx), v⟩` on `[0,1]`. -/
theorem hasFDerivAt_radialPotential {G : SpatialField} (hG : HasSymmetricJacobian G)
    (hsmooth : ContDiff ℝ ∞ G) (x : Space) :
    HasFDerivAt (fun y => ∫ r in (0:ℝ)..1, (inner ℝ (G (r • y)) y : ℝ))
      (innerSL ℝ (G x)) x := by
  have hF : ContDiff ℝ ∞ (fun p : Space × ℝ => (inner ℝ (G (p.2 • p.1)) p.1 : ℝ)) :=
    (hsmooth.comp (contDiff_snd.smul contDiff_fst)).inner ℝ contDiff_fst
  have hderiv := EulerCompactParameterIntegral.integral_hasFDerivAt (0:ℝ) 1 (by norm_num)
    (fun p : Space × ℝ => (inner ℝ (G (p.2 • p.1)) p.1 : ℝ)) hF x
  have hii : IntervalIntegrable
      (fun t => EulerCompactParameterIntegral.parameterDerivative
        (fun p : Space × ℝ => (inner ℝ (G (p.2 • p.1)) p.1 : ℝ)) (x, t)) volume 0 1 :=
    ((EulerCompactParameterIntegral.parameterDerivative_contDiff _ hF).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  have hInt_eq :
      (∫ t in (0:ℝ)..1, EulerCompactParameterIntegral.parameterDerivative
        (fun p : Space × ℝ => (inner ℝ (G (p.2 • p.1)) p.1 : ℝ)) (x, t))
      = innerSL ℝ (G x) := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.intervalIntegral_apply hii v, innerSL_apply_apply]
    -- the parameter derivative is the Fréchet derivative of the time slice
    have hpeq : ∀ t : ℝ,
        EulerCompactParameterIntegral.parameterDerivative
          (fun p : Space × ℝ => (inner ℝ (G (p.2 • p.1)) p.1 : ℝ)) (x, t)
        = fderiv ℝ (fun y : Space => (inner ℝ (G (t • y)) y : ℝ)) x := by
      intro t
      have hin : HasFDerivAt (fun y : Space => (y, t))
          (ContinuousLinearMap.inl ℝ Space ℝ) x :=
        (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
      exact (((hF.differentiable (by simp)) (x, t)).hasFDerivAt.comp x hin).fderiv.symm
    -- the slice derivative, via the product rule and the symmetric Jacobian
    have key : ∀ t : ℝ,
        fderiv ℝ (fun y : Space => (inner ℝ (G (t • y)) y : ℝ)) x v
        = inner ℝ (G (t • x)) v + t * inner ℝ (fderiv ℝ G (t • x) x) v := by
      intro t
      have hcomp : HasFDerivAt (fun y : Space => G (t • y))
          ((fderiv ℝ G (t • x)).comp (t • ContinuousLinearMap.id ℝ Space)) x :=
        ((hsmooth.differentiable (by simp)) (t • x)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).const_smul t)
      have hf1 : DifferentiableAt ℝ (fun y : Space => G (t • y)) x := hcomp.differentiableAt
      have hchain : fderiv ℝ (fun y : Space => G (t • y)) x v = t • fderiv ℝ G (t • x) v := by
        rw [hcomp.fderiv]; simp
      rw [fderiv_inner_apply (𝕜 := ℝ) hf1 differentiableAt_fun_id v, hchain, fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      rw [real_inner_smul_left, inner_fderiv_symm hG (t • x) v x]
    simp only [hpeq, key]
    -- FTC on `r ↦ r ⟨G(rx), v⟩`: `∫₀¹ ∂_r[r ⟨G(rx),v⟩] dr = ⟨G x, v⟩`
    have hderivψ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s * (inner ℝ (G (s • x)) v : ℝ))
        (inner ℝ (G (t • x)) v + t * inner ℝ (fderiv ℝ G (t • x) x) v) t := by
      intro t
      have hscale : HasDerivAt (fun s : ℝ => s • x) x t := by
        simpa using (hasDerivAt_id t).smul_const x
      have hGcomp : HasDerivAt (fun s : ℝ => G (s • x)) (fderiv ℝ G (t • x) x) t :=
        ((hsmooth.differentiable (by simp)) (t • x)).hasFDerivAt.comp_hasDerivAt t hscale
      have hginner : HasDerivAt (fun s : ℝ => (inner ℝ (G (s • x)) v : ℝ))
          (inner ℝ (fderiv ℝ G (t • x) x) v) t := by
        simpa using hGcomp.inner (𝕜 := ℝ) (hasDerivAt_const t v)
      have hmul : HasDerivAt (fun s : ℝ => s * (inner ℝ (G (s • x)) v : ℝ))
          (1 * inner ℝ (G (t • x)) v + t * inner ℝ (fderiv ℝ G (t • x) x) v) t :=
        (hasDerivAt_id t).mul hginner
      simpa using hmul
    have hcont : Continuous (fun t : ℝ =>
        inner ℝ (G (t • x)) v + t * inner ℝ (fderiv ℝ G (t • x) x) v) := by
      have hGc : Continuous (fun t : ℝ => G (t • x)) :=
        hsmooth.continuous.comp (continuous_id.smul continuous_const)
      have hdc : Continuous (fun t : ℝ => fderiv ℝ G (t • x)) :=
        (hsmooth.fderiv_right (m := ∞) (by simp)).continuous.comp
          (continuous_id.smul continuous_const)
      have h1 : Continuous (fun t : ℝ => (inner ℝ (G (t • x)) v : ℝ)) :=
        hGc.inner continuous_const
      have h2 : Continuous (fun t : ℝ => (inner ℝ (fderiv ℝ G (t • x) x) v : ℝ)) :=
        (hdc.clm_apply continuous_const).inner continuous_const
      exact h1.add (continuous_id.mul h2)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderivψ t) (hcont.intervalIntegrable 0 1)
    simpa using hFTC
  rw [hInt_eq] at hderiv
  exact hderiv

/-- **The spacetime corollary of eq:Rpressure's gauge (A01 m4 / D01 L9(b)).**
At a fixed time slice where `G' (t, ·) = G`, the upstream `pressureGradient`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:71`) of the
manuscript's radial potential `pressurePotential G'` recovers `G`.  This is the
pointwise statement whose gauge-equivalence packaging is the contract field
`ManuscriptLocalRegularity.pressure_potential`. -/
theorem pressureGradient_pressurePotential {G : SpatialField} {G' : SpaceTimeField} {t : ℝ}
    (hG : HasSymmetricJacobian G) (hsmooth : ContDiff ℝ ∞ G)
    (hslice : ∀ y : Space, G' (t, y) = G y) (x : Space) :
    pressureGradient (pressurePotential G') t x = G x := by
  have hpt : (fun y : Space => pressurePotential G' (t, y))
      = fun y : Space => ∫ r in (0:ℝ)..1, (inner ℝ (G (r • y)) y : ℝ) := by
    funext y
    simp only [pressurePotential]
    apply intervalIntegral.integral_congr
    intro r _
    simp only [hslice]
  have hfd : fderiv ℝ (fun y : Space => pressurePotential G' (t, y)) x
      = innerSL ℝ (G x) := by
    rw [hpt]; exact (hasFDerivAt_radialPotential hG hsmooth x).fderiv
  simp only [pressureGradient, hfd, innerSL_apply_apply]
  have hcoord : ∀ i : Fin 3, (inner ℝ (G x) (coordinateVector i) : ℝ) = (G x) i := by
    intro i
    rw [coordinateVector, EuclideanSpace.inner_single_right]; simp
  simp only [hcoord]
  rw [Fin.sum_univ_three]
  ext j
  fin_cases j <;> simp [coordinateVector]

end NSFormalization.Section4.A01.RadialPotential
