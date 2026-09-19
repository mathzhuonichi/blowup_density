import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Boundary flux cancellation on coordinate boxes. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open scoped ContDiff

/-- Either face of a nondegenerate coordinate box belongs to its frontier. -/
theorem box_face_mem_frontier (a b : Fin 3 → ℝ) (hab : ∀ i, a i < b i)
    (i : Fin 3) (c : ℝ) (hc : c = a i ∨ c = b i)
    (x : Fin 2 → ℝ) (hx : x ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
    i.insertNth c x ∈ frontier (Icc a b) := by
  rw [frontier, isClosed_Icc.closure_eq]
  refine ⟨?_, ?_⟩
  · constructor
    · rw [Fin.le_insertNth_iff]
      exact ⟨hc.elim (fun h => h ▸ le_rfl) (fun h => h ▸ (hab i).le), hx.1⟩
    · rw [Fin.insertNth_le_iff]
      exact ⟨hc.elim (fun h => h ▸ (hab i).le) (fun h => h ▸ le_rfl), hx.2⟩
  · rw [← pi_univ_Icc, interior_pi_set (finite_univ), show
        (fun j => interior (Icc (a j) (b j))) = (fun j => Ioo (a j) (b j)) from
        funext (fun _ => interior_Icc)]
    intro h
    have hi := h i (mem_univ i)
    simp only [Fin.insertNth_apply_same, mem_Ioo] at hi
    rcases hc with rfl | rfl
    · exact (lt_irrefl _ hi.1)
    · exact (lt_irrefl _ hi.2)

/-- A C¹ flux vanishing on the boundary has zero integral divergence on a box.
Only neighborhood smoothness at points of the closed box is required. -/
theorem box_integral_divergence_eq_zero (a b : Fin 3 → ℝ) (hab : ∀ i, a i < b i)
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 F x)
    (hzero : ∀ x ∈ frontier (Icc a b), F x = 0) :
    (∫ x in Icc a b, ∑ i : Fin 3, fderiv ℝ F x (Pi.single i 1) i) = 0 := by
  have hc : ContinuousOn F (Icc a b) := fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hd : ContinuousOn (fderiv ℝ F) (Icc a b) := fun x hx =>
    ((hF x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hi : IntegrableOn (fun x => ∑ i : Fin 3, fderiv ℝ F x (Pi.single i 1) i)
      (Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_finsetSum _ fun i _ =>
      (continuous_apply i).comp_continuousOn (hd.clm_apply continuousOn_const)
  rw [integral_divergence_of_hasFDerivAt_off_countable a b (fun i => (hab i).le)
    F (fderiv ℝ F) ∅ countable_empty hc ?_ hi]
  · apply Finset.sum_eq_zero
    intro i _
    have hz (c : ℝ) (hc : c = a i ∨ c = b i) :
        (∫ x in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth c x) i) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [hzero _ (box_face_mem_frontier a b hab i c hc x hx)]
      rfl
    rw [hz (b i) (Or.inr rfl), hz (a i) (Or.inl rfl), sub_self]
  · intro x hx
    apply ((hF x ?_).differentiableAt one_ne_zero).hasFDerivAt
    exact ⟨fun i => (hx.1 i (mem_univ i)).1.le,
      fun i => (hx.1 i (mem_univ i)).2.le⟩

/-- Integration by parts with a no-slip scalar factor, on a coordinate box. -/
theorem box_integral_mul_fderiv_eq_neg (a b : Fin 3 → ℝ) (hab : ∀ i, a i < b i)
    (f g : (Fin 3 → ℝ) → ℝ)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hg : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 g x)
    (hzero : ∀ x ∈ frontier (Icc a b), f x = 0) (j : Fin 3) :
    (∫ x in Icc a b, f x * fderiv ℝ g x (Pi.single j 1)) =
      -(∫ x in Icc a b, fderiv ℝ f x (Pi.single j 1) * g x) := by
  let F : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x => Pi.single j (f x * g x)
  have hF : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 F x := by
    intro x hx
    exact contDiffAt_pi.mpr fun i => by
      by_cases h : j = i
      · subst i
        simpa [F] using (hf x hx).mul (hg x hx)
      · simpa [F, Pi.single_eq_of_ne (Ne.symm h)] using
          (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : Fin 3 → ℝ => (0 : ℝ)) x)
  have hz := box_integral_divergence_eq_zero a b hab F hF (by
    intro x hx
    simp [F, hzero x hx])
  have hderiv (x : Fin 3 → ℝ) (hx : x ∈ Icc a b) :
      (∑ i : Fin 3, fderiv ℝ F x (Pi.single i 1) i) =
        fderiv ℝ f x (Pi.single j 1) * g x + f x * fderiv ℝ g x (Pi.single j 1) := by
    have hp := ((hf x hx).differentiableAt one_ne_zero).hasFDerivAt.mul
      ((hg x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hv : HasFDerivAt F
        ((ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) j).comp
          (f x • fderiv ℝ g x + g x • fderiv ℝ f x)) x := by
      exact (ContinuousLinearMap.single ℝ (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp x hp
    rw [hv.fderiv]
    rw [Finset.sum_eq_single j]
    · simp [ContinuousLinearMap.comp_apply, mul_comm, add_comm]
    · intro i _ hij
      simp [ContinuousLinearMap.comp_apply, Pi.single_eq_of_ne hij]
    · simp
  have hcf : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hcg : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hdf : ContinuousOn (fderiv ℝ f) (Icc a b) := fun x hx =>
    ((hf x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hdg : ContinuousOn (fderiv ℝ g) (Icc a b) := fun x hx =>
    ((hg x hx).continuousAt_fderiv (by norm_num)).continuousWithinAt
  have hi₁ : IntegrableOn (fun x => fderiv ℝ f x (Pi.single j 1) * g x) (Icc a b) :=
    ((hdf.clm_apply continuousOn_const).mul hcg).integrableOn_Icc
  have hi₂ : IntegrableOn (fun x => f x * fderiv ℝ g x (Pi.single j 1)) (Icc a b) :=
    (hcf.mul (hdg.clm_apply continuousOn_const)).integrableOn_Icc
  rw [setIntegral_congr_fun measurableSet_Icc hderiv, integral_add hi₁ hi₂] at hz
  linarith

end NSFormalization.Section3.T23
