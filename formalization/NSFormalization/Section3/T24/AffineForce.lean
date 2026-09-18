import NSFormalization.Section3.T24.AffineBasics
import NavierStokes.ResidualRegularity
import NavierStokes.R3.ProblemStatement

/-!
# T24a / Ua4 — the `force_smooth` and `force_support` fields of `AffineVariationAPI`

`prop:affine` ② (`paper/sections/03-torus.tex:681-683`): for every admissible
perturbation `b` the corrected force

`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`  (`affineForce`, lane 392
`AffineBasics.lean`)

is smooth on **all** of spacetime and lies in `C_c^∞(ℝ³×(0,∞))` — the correction
extends smoothly by zero across the singular time `t = 1`, even though the packet
velocity `U` is only known to be smooth on `preSingularDomain = [0,1) × ℝ³`.

The statement is carried over **raw packet fields** `U F` (the reconciliation rule
"`formalization/` cannot import `Contracts.*`", `research/T24/T24_SPLIT.md:§0`):
the packet clauses consumed are exactly

* `velocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain`  (smoothness only),
* `force_smooth   : ContDiff ℝ ∞ F`                        (smoothness only),
* `force_support  : CompactPositiveTimeSupport F`          (support only),

passed as explicit hypotheses, exactly the pattern of `AffineMomentum.lean`
(lane 398) and `AffineDivergence.lean` (lane 402).  In addition the two cylinder
parameter hypotheses `0 < τ₀` and `τ₁ < 1` of `affineVariationStatement`
(`research/T24/Spec.lean:1117`, the `window` field `:1019`) are carried
**explicitly**, exactly as lane 403 `AffineSpeed.lean` does: `AffineAdmissible`
constrains `b` relative to the supplied cylinder but does not assert that the
cylinder's time window sits inside `(0,1)`, and without that the correction terms
are genuinely undefined/nonsmooth where `U` is (`t ≥ 1`).  `force_smooth` uses
both; `force_support` uses only `0 < τ₀`.

## Route (the two-open-set gluing)

`tsupport b ⊆ affineCylinder c r τ₀ τ₁ = Ioo τ₀ τ₁ ×ˢ ball c r`, so with
`0 < τ₀` and `τ₁ < 1` the support of the whole correction sits inside the **open**
slab `Ioo 0 1 ×ˢ univ ⊆ preSingularDomain`.  Two open sets then cover spacetime:

* `Ioo 0 1 ×ˢ univ`, where `U` is smooth (`ContDiffOn.mono`) and every correction
  term is a product/`clm_apply` of smooth things — the vendored
  `NavierStokes.ResidualRegularity` regularity helpers
  (`contDiffOn_temporalDerivative`, `contDiffOn_spatialDerivative`,
  `contDiffOn_spatialLaplacian`) supply exactly these;
* `(tsupport b)ᶜ`, where `b` vanishes on a neighbourhood of every point, so every
  correction term vanishes (the vendored locality helpers
  `temporalDerivative_congr`, `spatialDerivative_congr`, `spatialLaplacian_congr`)
  and `affineForce ν U F b = F` pointwise, which is globally smooth.

`contDiff_iff_contDiffAt` then glues.  For the support clause the same vanishing
gives `tsupport (affineForce ν U F b) ⊆ tsupport F ∪ tsupport b`, a union of two
compact sets both inside `positiveTimeDomain`.

All operators are the registered ones (`NavierStokes.ProblemStatement:55-79`,
`NavierStokesR3.ProblemStatement:66`), definitionally the `Contracts.V1` tokens.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set
open NavierStokes.ProblemStatement
open scoped ContDiff

/-! ## Geometry of the cylinder -/

/-- With `0 < τ₀` and `τ₁ < 1` the affine cylinder sits inside the open
presingular slab `Ioo 0 1 ×ˢ univ`, where the packet velocity is smooth. -/
theorem affineCylinder_subset_interior {c : Space} {r τ₀ τ₁ : ℝ}
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1) :
    affineCylinder c r τ₀ τ₁ ⊆ Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space) := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact ⟨⟨hτ₀.trans ht.1, ht.2.trans hτ₁⟩, mem_univ _⟩

/-- With `0 < τ₀` the affine cylinder sits in strictly positive time. -/
theorem affineCylinder_subset_positiveTimeDomain {c : Space} {r τ₀ τ₁ : ℝ}
    (hτ₀ : 0 < τ₀) :
    affineCylinder c r τ₀ τ₁ ⊆ NavierStokesR3.ProblemStatement.positiveTimeDomain := by
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact ⟨hτ₀.trans ht.1, mem_univ _⟩

/-! ## Vanishing of the correction off the support of `b` -/

/-- Off `tsupport b` the perturbation vanishes on a whole neighbourhood, so every
one of the five correction terms of `affineForce` vanishes and the corrected force
is the original force.  No smoothness of `U` is used. -/
theorem affineForce_eq_of_notMem_tsupport {ν : ℝ} {U F b : VelocityField}
    {z : SpaceTime} (hz : z ∉ tsupport b) :
    affineForce ν U F b z = F z := by
  have hb0 : b =ᶠ[nhds z] (fun _ : SpaceTime => (0 : Space)) := by
    filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hz] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have hT : temporalDerivative b z.1 z.2 = 0 := by
    rw [NavierStokes.ResidualRegularity.temporalDerivative_congr hb0]
    simp [temporalDerivative]
  have hD : spatialDerivative b z.1 z.2 = 0 := by
    rw [NavierStokes.ResidualRegularity.spatialDerivative_congr hb0]
    simp [spatialDerivative]
  have hL : spatialLaplacian b z.1 z.2 = 0 := by
    rw [NavierStokes.ResidualRegularity.spatialLaplacian_congr hb0]
    simp [spatialLaplacian, spatialDerivative]
  have hbz : b z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [affineForce, crossAdvection, hT, hD, hL, hbz]

/-! ## Interior smoothness of the corrected force -/

/-- On the open presingular slab every term of `affineForce` is smooth: `F` is
globally smooth, `b` is globally smooth, and `U` is smooth there. -/
theorem contDiffOn_affineForce_interior {ν : ℝ} {U F b : VelocityField}
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hforce_smooth : ContDiff ℝ ∞ F) (hb_smooth : ContDiff ℝ ∞ b) :
    ContDiffOn ℝ ∞ (affineForce ν U F b) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) := by
  have hVopen : IsOpen (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space) ⊆ preSingularDomain := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact ⟨⟨ht.1.le, ht.2⟩, mem_univ _⟩
  have hU : ContDiffOn ℝ ∞ U (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    hvelocity_smooth.mono hsub
  have hbV : ContDiffOn ℝ ∞ b (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    hb_smooth.contDiffOn
  have hF : ContDiffOn ℝ ∞ F (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    hforce_smooth.contDiffOn
  have hT : ContDiffOn ℝ ∞ (fun z : SpaceTime => temporalDerivative b z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative hVopen hbV
  have hL : ContDiffOn ℝ ∞ (fun z : SpaceTime => ν • spatialLaplacian b z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    (NavierStokes.ResidualRegularity.contDiffOn_spatialLaplacian hVopen hbV).const_smul ν
  have hDb : ContDiffOn ℝ ∞ (fun z : SpaceTime => spatialDerivative b z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    NavierStokes.ResidualRegularity.contDiffOn_spatialDerivative hVopen hbV
  have hDU : ContDiffOn ℝ ∞ (fun z : SpaceTime => spatialDerivative U z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) :=
    NavierStokes.ResidualRegularity.contDiffOn_spatialDerivative hVopen hU
  have hA1 : ContDiffOn ℝ ∞ (fun z : SpaceTime => crossAdvection U b z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) := hDb.clm_apply hU
  have hA2 : ContDiffOn ℝ ∞ (fun z : SpaceTime => crossAdvection b U z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) := hDU.clm_apply hbV
  have hA3 : ContDiffOn ℝ ∞ (fun z : SpaceTime => crossAdvection b b z.1 z.2)
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)) := hDb.clm_apply hbV
  exact ((((hF.add hT).sub hL).add hA1).add hA2).add hA3

/-! ## Ua4 target 1: the `force_smooth` field, over raw packet fields -/

/-- `03-torus.tex:681-683`, `research/T24/Spec.lean:1025`
(`AffineVariationAPI.force_smooth`): for every admissible `b` the corrected force
`affineForce ν U F b` is smooth on all of spacetime.

Raw-field form: the packet clauses consumed are `velocity_smooth` and
`force_smooth`; the cylinder hypotheses `0 < τ₀` and `τ₁ < 1` are the parameter
hypotheses of `affineVariationStatement` and are carried explicitly (as in lane
403), because `AffineAdmissible` does not by itself place the cylinder inside
`(0,1)`.  No support clause on `F` and no pressure information are used. -/
theorem force_smooth {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hforce_smooth : ContDiff ℝ ∞ F) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ContDiff ℝ ∞ (affineForce ν U F b) := by
  intro b hb
  obtain ⟨hb_smooth, -, hb_supp, -⟩ := hb
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set Space)
  · exact (contDiffOn_affineForce_interior hvelocity_smooth hforce_smooth
      hb_smooth).contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hz)
  · have hznot : z ∉ tsupport b := fun hmem =>
      hz (affineCylinder_subset_interior hτ₀ hτ₁ (hb_supp hmem))
    refine hforce_smooth.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hznot] with w hw
    exact affineForce_eq_of_notMem_tsupport hw

/-! ## Ua4 target 2: the `force_support` field, over raw packet fields -/

/-- The corrected force is carried by the union of the original force's support
and the perturbation's support.  No smoothness hypothesis is needed. -/
theorem tsupport_affineForce_subset {ν : ℝ} {U F b : VelocityField} :
    tsupport (affineForce ν U F b) ⊆ tsupport F ∪ tsupport b := by
  refine closure_minimal ?_ ((isClosed_tsupport F).union (isClosed_tsupport b))
  intro z hz
  by_contra hmem
  rw [Set.mem_union, not_or] at hmem
  refine hz ?_
  rw [affineForce_eq_of_notMem_tsupport hmem.2,
    image_eq_zero_of_notMem_tsupport hmem.1]

/-- `03-torus.tex:681-683`, `research/T24/Spec.lean:1032`
(`AffineVariationAPI.force_support`): for every admissible `b` the corrected force
has compact spacetime support contained in strictly positive time, i.e.
`F̃ ∈ C_c^∞(ℝ³×(0,∞))` once combined with `force_smooth`.

Raw-field form: the only packet clause consumed is `force_support`, and the only
cylinder hypothesis is `0 < τ₀` (`τ₁ < 1` is *not* needed here — the support
statement never looks at `U`). -/
theorem force_support {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport F) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport
        (affineForce ν U F b) := by
  intro b hb
  obtain ⟨-, hb_cs, hb_supp, -⟩ := hb
  have hsub : tsupport (affineForce ν U F b) ⊆ tsupport F ∪ tsupport b :=
    tsupport_affineForce_subset
  have hcF : IsCompact (tsupport F) := hforce_support.1
  have hcb : IsCompact (tsupport b) := hb_cs
  refine ⟨hcF.union hcb |>.of_isClosed_subset (isClosed_tsupport _) hsub, ?_⟩
  refine hsub.trans (union_subset hforce_support.2 ?_)
  exact hb_supp.trans (affineCylinder_subset_positiveTimeDomain hτ₀)

end NSFormalization.Section3.T24
