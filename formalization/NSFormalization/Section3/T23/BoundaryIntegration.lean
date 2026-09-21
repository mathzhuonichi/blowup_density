import NSFormalization.Section3.T23.DomainSolution
import NSFormalization.Section3.T23.OpenSetIntegration

/-! The scalar boundary integration identity follows from zero boundary flux.
This removes the extra IBP premise on every bounded open domain, including the
regular-level domains used by the manuscript. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff

/-- The integral of a coordinate derivative vanishes for a C¹ scalar field
with zero boundary values on a bounded open subset of Euclidean space. -/
theorem integral_coordinateDerivative_eq_zero {Ω : Set Space}
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (f : Space → ℝ)
    (hf : ∀ x ∈ closure Ω, ContDiffAt ℝ 1 f x)
    (hz : ∀ x ∈ frontier Ω, f x = 0) (j : Fin 3) :
    (∫ x in Ω, fderiv ℝ f x (coordinateVector j)) = 0 := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  let U := e ⁻¹' Ω
  have hcl : closure U = e ⁻¹' closure Ω :=
    (e.toHomeomorph.preimage_closure Ω).symm
  have hfr : frontier U = e ⁻¹' frontier Ω :=
    (e.toHomeomorph.preimage_frontier Ω).symm
  have hu : IsOpen U := ho.preimage e.continuous
  have hub : Bornology.IsBounded U := by
    have h := e.symm.toContinuousLinearMap.lipschitzWith.isBounded_image hb
    apply h.subset
    intro x hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hfc : ∀ y ∈ closure U, ContDiffAt ℝ 1 (f ∘ e) y := by
    intro y hy
    exact (hf (e y) (by rwa [hcl] at hy)).comp y e.contDiff.contDiffAt
  have hzf : ∀ y ∈ frontier U, (f ∘ e) y = 0 := by
    intro y hy
    exact hz (e y) (by rwa [hfr] at hy)
  have hd (y : Fin 3 → ℝ) (hy : y ∈ U) :
      fderiv ℝ (f ∘ e) y (Pi.single j 1) = fderiv ℝ f (e y) (coordinateVector j) := by
    rw [(((hf (e y) (subset_closure hy)).differentiableAt one_ne_zero).hasFDerivAt.comp
      y e.hasFDerivAt).fderiv]
    rfl
  have H := integral_partial_open_eq_zero hu hub (f ∘ e) hfc hzf j
  rw [setIntegral_congr_fun hu.measurableSet hd] at H
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding (fun x => fderiv ℝ f x (coordinateVector j)) Ω]
  exact H

/-- Apply zero boundary flux to the scalar product `f * g`, then the product
rule. This is the divergence-form Stokes argument for the field `f g e_j`;
the supporting zero-flux lemma is proved by FTC and Fubini at the pinned Mathlib. -/
theorem ibp_of_isOpen_isBounded {Ω : Set Space}
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) : IBP Ω := by
  intro f g hf hg hz j
  have H := integral_coordinateDerivative_eq_zero ho hb (fun x => f x * g x)
    (fun x hx => (hf x hx).mul (hg x hx)) (fun x hx => by rw [hz x hx, zero_mul]) j
  have hcf : ContinuousOn f (closure Ω) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hcg : ContinuousOn g (closure Ω) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hdf : ContinuousOn (fderiv ℝ f) (closure Ω) := fun x hx =>
    ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hdg : ContinuousOn (fderiv ℝ g) (closure Ω) := fun x hx =>
    ((hg x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hi₁ : IntegrableOn (fun x => fderiv ℝ f x (coordinateVector j) * g x) Ω :=
    (((hdf.clm_apply continuousOn_const).mul hcg).integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hi₂ : IntegrableOn (fun x => f x * fderiv ℝ g x (coordinateVector j)) Ω :=
    ((hcf.mul (hdg.clm_apply continuousOn_const)).integrableOn_compact
      hb.isCompact_closure).mono_set subset_closure
  have hd (x : Space) (hx : x ∈ Ω) :
      fderiv ℝ (fun y => f y * g y) x (coordinateVector j) =
        fderiv ℝ f x (coordinateVector j) * g x + f x * fderiv ℝ g x (coordinateVector j) := by
    have hp : HasFDerivAt (fun y => f y * g y)
        (f x • fderiv ℝ g x + g x • fderiv ℝ f x) x :=
      ((hf x (subset_closure hx)).differentiableAt one_ne_zero).hasFDerivAt.mul
        ((hg x (subset_closure hx)).differentiableAt one_ne_zero).hasFDerivAt
    rw [hp.fderiv]
    simp [mul_comm, add_comm]
  rw [setIntegral_congr_fun ho.measurableSet hd, integral_add hi₁ hi₂] at H
  linarith

/-- Every domain in the manuscript's box-or-smooth class satisfies IBP. -/
theorem ibp_boundedDomain {Ω : Set Space} (hΩ : IsBoundedBoxOrSmoothDomain Ω) : IBP Ω :=
  ibp_of_isOpen_isBounded hΩ.1 hΩ.2.1

end NSFormalization.Section3.T23
