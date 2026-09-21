import NSFormalization.Section3.T24.AffineBasics
import NSFormalization.Section3.T24.AffineForce
import NavierStokes.ResidualCalculus

/-!
# T24a / Ua8 — the `nonisolated` field of `AffineVariationAPI` (`prop:affine` ⑤)

`prop:affine`, `paper/sections/03-torus.tex:692-696`: the affine family is not
isolated.  For a fixed nonzero admissible perturbation `b` and the rescaled family
`λ ↦ (Ũ_{λb}, F̃_{λb})`, the velocity difference is

`Ũ_{λb} − U = λ b`

and the force difference is

`F̃_{λb} − F = λ L_U b + λ² (b·∇)b`,  `L_U b = ∂ₜb − νΔb + (U·∇)b + (b·∇)U`,

so on the fixed compact set `tsupport b`, where all coefficients and all of their
derivatives are bounded, the `C^m` seminorm of the force difference is at most
`C_m|λ| + C_m' λ²` and that of the velocity difference is `C_m'' |λ|`; both tend
to `0` as `λ → 0`.

The seminorm is `affineCkSeminorm` (lane 392, `AffineBasics.lean:50`), the
`ℝ≥0∞`-valued `∑_{k ≤ m} ⨆_{z ∈ K} ‖D^k f(z)‖ₑ` — token-identical to
`research/T24/Spec.lean:998` `ckSeminormE`.  The extended codomain matters: a real
`sSup` would take its junk value on an unbounded range and make the limit vacuous,
whereas the `ℝ≥0∞` `⨆` never does, so the finiteness lemma
`affineCkSeminorm_lt_top` below carries real content.

The statement is carried over **raw packet fields** `U F` (the reconciliation rule
"`formalization/` cannot import `Contracts.*`", `research/T24/T24_SPLIT.md:§0`):
the only packet clause consumed is `velocity_smooth`
(`ContDiffOn ℝ ∞ U preSingularDomain`), and the two cylinder hypotheses `0 < τ₀`,
`τ₁ < 1` of `affineVariationStatement` are carried explicitly exactly as lanes
403/414 do (`AffineAdmissible` does not by itself place the cylinder inside
`(0,1)`).  The packet's `force_smooth` is **not** needed: the ambient force `F`
cancels in the difference, and the `λ`-coefficient is recovered as
`affineForce ν U 0 b`, whose global smoothness is lane 414's `force_smooth`
applied at the zero force.

## Route

* §1 the three algebraic facts about `affineCkSeminorm` that the bound needs:
  exact homogeneity under a constant scalar, subadditivity, and finiteness on a
  compact set for a globally smooth field.
* §2 the scaling identity `F̃_{λb} − F = λ·(F̃_b − F) + (λ²−λ)·(b·∇)b`, which is
  the paper's `λ L_U b + λ²(b·∇)b` rearranged so that **both** coefficient fields
  are globally smooth: `F̃_b − F = affineForce ν U 0 b` (lane 414) and
  `(b·∇)b = advection b` (vendored `contDiffOn_advection`).  `L_U b` alone is
  *not* globally smooth — `U` is only known to be smooth on `preSingularDomain` —
  so this rearrangement, not the paper's literal splitting, is what lets the
  subadditivity of §1 apply.
* §3 the two limits, by `ENNReal.Tendsto.mul_const` and a squeeze between `0` and
  `‖λ‖ₑ·C_m + ‖λ²−λ‖ₑ·C_m'`.

The scalar linearity of the operators is the vendored `NavierStokes.ResidualCalculus`
(`spatialDerivative_const_smul`, `spatialLaplacian_const_smul`) and the global
smoothness of `(b·∇)b` the vendored `NavierStokes.ResidualRegularity`
(`contDiffOn_advection`), reused rather than reproved.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set Filter Topology
open NavierStokes.ProblemStatement
open NavierStokes.ResidualCalculus
open scoped ContDiff ENNReal BigOperators

/-! ## §1 Algebra of the fixed-support `C^m` seminorm -/

/-- A constant factors out of a set-indexed `ℝ≥0∞` supremum, including when the
set is empty (both sides are then `0`). -/
theorem enn_mul_biSup (a : ℝ≥0∞) (K : Set SpaceTime) (g : SpaceTime → ℝ≥0∞) :
    a * (⨆ z ∈ K, g z) = ⨆ z ∈ K, a * g z := by
  rw [ENNReal.mul_iSup]
  exact iSup_congr fun z => ENNReal.mul_iSup _ _

/-- `affineCkSeminorm` is exactly homogeneous: every iterated derivative of
`c • f` is `c •` the corresponding derivative of `f`. -/
theorem affineCkSeminorm_const_smul {K : Set SpaceTime} {m : ℕ} {f : VelocityField}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    affineCkSeminorm K m (fun z => c • f z) = ‖c‖ₑ * affineCkSeminorm K m f := by
  unfold affineCkSeminorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [enn_mul_biSup]
  refine iSup_congr fun z => iSup_congr fun _ => ?_
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by exact_mod_cast le_top)).contDiffAt,
    enorm_smul]

/-- `affineCkSeminorm` is subadditive on globally smooth fields. -/
theorem affineCkSeminorm_add_le {K : Set SpaceTime} {m : ℕ} {f g : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    affineCkSeminorm K m (fun z => f z + g z)
      ≤ affineCkSeminorm K m f + affineCkSeminorm K m g := by
  unfold affineCkSeminorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  refine iSup₂_le fun z hz => ?_
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine (enorm_add_le (iteratedFDeriv ℝ k f z) (iteratedFDeriv ℝ k g z)).trans
    (add_le_add ?_ ?_)
  · exact le_iSup₂ (f := fun z (_ : z ∈ K) => ‖iteratedFDeriv ℝ k f z‖ₑ) z hz
  · exact le_iSup₂ (f := fun z (_ : z ∈ K) => ‖iteratedFDeriv ℝ k g z‖ₑ) z hz

/-- A globally smooth field has finite `C^m` seminorm on every compact set: each
`z ↦ ‖D^k f(z)‖` is continuous, hence bounded on the compact `K`, so the `ℝ≥0∞`
supremum is below `ENNReal.ofReal` of that bound. -/
theorem affineCkSeminorm_lt_top {K : Set SpaceTime} {m : ℕ} {f : VelocityField}
    (hK : IsCompact K) (hf : ContDiff ℝ ∞ f) : affineCkSeminorm K m f < ⊤ := by
  unfold affineCkSeminorm
  refine ENNReal.sum_lt_top.mpr fun k _ => ?_
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)).continuousOn
  refine lt_of_le_of_lt (iSup₂_le fun z hz => ?_) (ENNReal.ofReal_lt_top (r := C))
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC z hz)

/-! ## §2 The scaling identity for the corrected force -/

/-- `(b·∇)b` is globally smooth as soon as `b` is; it is the registered
`advection b`. -/
theorem contDiff_crossAdvection_self {b : VelocityField} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun z : SpaceTime => crossAdvection b b z.1 z.2) := by
  rw [← contDiffOn_univ]
  exact NavierStokes.ResidualRegularity.contDiffOn_advection isOpen_univ hb.contDiffOn

/-- `03-torus.tex:692-694` rearranged: the force difference along the rescaled
family.  The paper's `λ L_U b + λ² (b·∇)b` is regrouped as
`λ (F̃_b − F) + (λ² − λ)(b·∇)b`, both of whose coefficient fields are globally
smooth (the first by lane 414's `force_smooth` at the zero force, the second by
`contDiff_crossAdvection_self`).  The ambient force `F` cancels, so no hypothesis
on `F` is used, and no hypothesis on `U` either. -/
theorem affineForce_smul_sub (ν : ℝ) (U F b : VelocityField) (hb : ContDiff ℝ ∞ b)
    (lam : ℝ) (z : SpaceTime) :
    affineForce ν U F (lam • b) z - F z
      = lam • affineForce ν U (fun _ => 0) b z
        + (lam ^ 2 - lam) • crossAdvection b b z.1 z.2 := by
  have hbd : ∀ (t : ℝ) (y : Space), DifferentiableAt ℝ (fun y' : Space => b (t, y')) y :=
    fun t y => ((hb.differentiable (by simp)).comp
      (differentiable_const t |>.prodMk differentiable_id)) y
  have hb2 : ∀ t : ℝ, ContDiff ℝ 2 (fun y : Space => b (t, y)) := fun t =>
    (hb.comp (contDiff_const.prodMk contDiff_id)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hbt : ∀ (t : ℝ) (x : Space), DifferentiableAt ℝ (fun s : ℝ => b (s, x)) t :=
    fun t x => ((hb.differentiable (by simp)).comp
      (differentiable_id.prodMk (differentiable_const x))) t
  have hsm : (lam • b : VelocityField) = fun w => lam • b w := rfl
  have hT : temporalDerivative (fun w : SpaceTime => lam • b w) z.1 z.2
      = lam • temporalDerivative b z.1 z.2 := by
    unfold temporalDerivative
    rw [fderiv_fun_const_smul (hbt z.1 z.2) lam]
    simp
  have hL : spatialLaplacian (fun w : SpaceTime => lam • b w) z.1 z.2
      = lam • spatialLaplacian b z.1 z.2 :=
    spatialLaplacian_const_smul b z.1 z.2 lam (hb2 z.1)
  have hA1 : crossAdvection U (fun w : SpaceTime => lam • b w) z.1 z.2
      = lam • crossAdvection U b z.1 z.2 := by
    unfold crossAdvection
    rw [spatialDerivative_const_smul b z.1 z.2 lam (hbd z.1 z.2)]
    simp
  have hA2 : crossAdvection (fun w : SpaceTime => lam • b w) U z.1 z.2
      = lam • crossAdvection b U z.1 z.2 := by
    unfold crossAdvection
    simp
  have hA3 : crossAdvection (fun w : SpaceTime => lam • b w)
        (fun w : SpaceTime => lam • b w) z.1 z.2
      = (lam * lam) • crossAdvection b b z.1 z.2 := by
    unfold crossAdvection
    rw [spatialDerivative_const_smul b z.1 z.2 lam (hbd z.1 z.2)]
    simp [smul_smul]
  rw [hsm]
  simp only [affineForce, hT, hL, hA1, hA2, hA3]
  module

/-- `03-torus.tex:692`: the velocity difference along the rescaled family is
exactly `λ b`. -/
theorem affineVelocity_smul_sub (U b : VelocityField) (lam : ℝ) :
    (fun z => affineVelocity U (lam • b) z - U z) = fun z => lam • b z := by
  funext z
  simp [affineVelocity]

/-! ## §3 Ua8 target: the `nonisolated` field, over raw packet fields -/

/-- `03-torus.tex:677,692-696`, `research/T24/Spec.lean:1104`
(`AffineVariationAPI.nonisolated`): for every admissible nonzero `b` and every
order `m`, the `C^m` seminorm on `tsupport b` of the velocity difference
`Ũ_{λb} − U` and of the force difference `F̃_{λb} − F` tend to `0` as `λ → 0`.

Raw-field form: the only packet clause consumed is `velocity_smooth`; the cylinder
hypotheses `0 < τ₀` and `τ₁ < 1` are the parameter hypotheses of
`affineVariationStatement` and are carried explicitly, as in lanes 403/414.  No
clause about `F` is used — the ambient force cancels in the difference. -/
theorem nonisolated {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 1)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 → ∀ m : ℕ,
      Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineVelocity U (lam • b) z - U z)) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineForce ν U F (lam • b) z - F z)) (𝓝 0) (𝓝 0) := by
  intro b hb _hbne m
  have hb_smooth : ContDiff ℝ ∞ b := hb.1
  have hK : IsCompact (tsupport b) := hb.2.1
  have htend0 : Tendsto (fun lam : ℝ => (‖lam‖ₑ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_enorm.tendsto (0 : ℝ))
  constructor
  · -- velocity half: the difference is exactly `λ b`, so the seminorm is `‖λ‖ₑ · ‖b‖_{C^m}`
    have hCb : affineCkSeminorm (tsupport b) m b < ⊤ :=
      affineCkSeminorm_lt_top hK hb_smooth
    have hvel : ∀ lam : ℝ, affineCkSeminorm (tsupport b) m
        (fun z => affineVelocity U (lam • b) z - U z)
          = ‖lam‖ₑ * affineCkSeminorm (tsupport b) m b := by
      intro lam
      rw [affineVelocity_smul_sub U b lam, affineCkSeminorm_const_smul hb_smooth]
    simp only [hvel]
    simpa using ENNReal.Tendsto.mul_const htend0 (Or.inr hCb.ne)
  · -- force half: `λ G + (λ²−λ) H` with `G`, `H` globally smooth
    have hGsmooth : ContDiff ℝ ∞ (affineForce ν U (fun _ => (0 : Space)) b) :=
      force_smooth c r τ₀ τ₁ hτ₀ hτ₁ hvelocity_smooth contDiff_const b hb
    have hHsmooth : ContDiff ℝ ∞ (fun z : SpaceTime => crossAdvection b b z.1 z.2) :=
      contDiff_crossAdvection_self hb_smooth
    have hA : affineCkSeminorm (tsupport b) m (affineForce ν U (fun _ => (0 : Space)) b) < ⊤ :=
      affineCkSeminorm_lt_top hK hGsmooth
    have hB : affineCkSeminorm (tsupport b) m
        (fun z : SpaceTime => crossAdvection b b z.1 z.2) < ⊤ :=
      affineCkSeminorm_lt_top hK hHsmooth
    have hbound : ∀ lam : ℝ, affineCkSeminorm (tsupport b) m
        (fun z => affineForce ν U F (lam • b) z - F z)
          ≤ ‖lam‖ₑ * affineCkSeminorm (tsupport b) m
              (affineForce ν U (fun _ => (0 : Space)) b)
            + ‖lam ^ 2 - lam‖ₑ * affineCkSeminorm (tsupport b) m
              (fun z : SpaceTime => crossAdvection b b z.1 z.2) := by
      intro lam
      have hfun : (fun z => affineForce ν U F (lam • b) z - F z)
          = fun z => lam • affineForce ν U (fun _ => (0 : Space)) b z
            + (lam ^ 2 - lam) • crossAdvection b b z.1 z.2 :=
        funext fun z => affineForce_smul_sub ν U F b hb_smooth lam z
      rw [hfun]
      refine (affineCkSeminorm_add_le (hGsmooth.const_smul lam)
        (hHsmooth.const_smul (lam ^ 2 - lam))).trans ?_
      rw [affineCkSeminorm_const_smul hGsmooth, affineCkSeminorm_const_smul hHsmooth]
    have h1 : Tendsto (fun lam : ℝ => ‖lam‖ₑ * affineCkSeminorm (tsupport b) m
        (affineForce ν U (fun _ => (0 : Space)) b)) (𝓝 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const htend0 (Or.inr hA.ne)
    have h2 : Tendsto (fun lam : ℝ => ‖lam ^ 2 - lam‖ₑ * affineCkSeminorm (tsupport b) m
        (fun z : SpaceTime => crossAdvection b b z.1 z.2)) (𝓝 0) (𝓝 0) := by
      have hc : Tendsto (fun lam : ℝ => (‖lam ^ 2 - lam‖ₑ : ℝ≥0∞)) (𝓝 0) (𝓝 0) := by
        have : Continuous fun lam : ℝ => (‖lam ^ 2 - lam‖ₑ : ℝ≥0∞) :=
          continuous_enorm.comp (by fun_prop)
        simpa using this.tendsto (0 : ℝ)
      simpa using ENNReal.Tendsto.mul_const hc (Or.inr hB.ne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hbound
    simpa using h1.add h2

end NSFormalization.Section3.T24
