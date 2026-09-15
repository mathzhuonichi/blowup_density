import NSFormalization.Section4.C01.EnergyDerivative

/-!
# Section 4 · C01 row E5 — the time derivative of enstrophy

The squared-gradient energy of a classical solution is differentiable at every interior
time.  Its derivative is first identified with the sum of the coordinate-derivative
pairings, by subtracting the vendor's order-zero word-energy identity from its order-one
identity, and is then rewritten as the negative Laplacian/time-derivative pairing by
ordinary integration by parts.

As in `EnergyDerivative.lean`, the analytic differentiation is performed on a translated
closed window `[0,S-c]`; the final theorem removes both the translation and the clamp near
an arbitrary time `t ∈ Ioo 0 T`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
  EulerOrdinarySobolev
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-! ## The order-one word bridges -/

/-- At `s = 1`, word energy is the order-zero energy plus the squared `L²` norms of the
three coordinate derivatives. -/
theorem wordEnergy_one (A : SmoothL2Field Space) :
    wordEnergy 1 A = wordEnergy 0 A +
      ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 := by
  have hsum : (∑ w : Fin 1 → Fin 3, ‖(wordField A w).toLp‖ ^ 2) =
      ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 := by
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _ (fun w => by rfl)
  rw [wordEnergy, wordEnergy]
  simp only [Nat.one_add, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsum]

/-- At `s = 1`, the pairing sum in `wordEnergy_hasDerivWithinAt` is the order-zero pairing
plus the three pairings of coordinate derivatives. -/
theorem wordInner_sum_one (X Y : SmoothL2Field Space) :
    (∑ n ∈ Finset.range (1 + 1), ∑ w : Fin n → Fin 3,
      @inner ℝ _ _ (wordField X w).toLp (wordField Y w).toLp) =
      @inner ℝ _ _ X.toLp Y.toLp +
        ∑ i : Fin 3, @inner ℝ _ _ (X.directionalField (axis i)).toLp
          (Y.directionalField (axis i)).toLp := by
  have hsum : (∑ w : Fin 1 → Fin 3,
      @inner ℝ _ _ (wordField X w).toLp (wordField Y w).toLp) =
      ∑ i : Fin 3, @inner ℝ _ _ (X.directionalField (axis i)).toLp
        (Y.directionalField (axis i)).toLp := by
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3)) _ _ (fun w => by rfl)
  simp only [Nat.one_add, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsum]
  simp [wordField_zero]

/-! ## Differentiation on a translated interior window -/

/-- **Row E5, first equality.**  On `[c,S] ⊂ (0,T)`, the shifted and clamped squared
gradient norm has derivative

`2 ∑ᵢ ⟪∂ᵢu(r+c,·), ∂ᵢ∂ₜu(r+c,·)⟫_{L²}`.

The proof applies `wordEnergy_hasDerivWithinAt` at orders one and zero to the same paths,
subtracts the resulting identities, and uses `wordEnergy_one` and
`wordInner_sum_one` to remove their common order-zero terms. -/
theorem enstrophyDerivative_hasDerivAt
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    HasDerivAt
      (fun ρ : ℝ => ∑ i : Fin 3,
        ‖((velocityField w hST
            ⟨(projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c,
              ⟨by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.1; linarith,
               by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.2;
                  linarith⟩⟩).directionalField (axis i)).toLp‖ ^ 2)
      (2 * ∑ i : Fin 3,
        @inner ℝ _ _ ((velocitySliceField w (Ioo_subset_Ico_self
              (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).directionalField (axis i)).toLp
          ((temporalSliceField w hf
              (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                ⟨by linarith [hr.1], by linarith [hr.2]⟩))).directionalField (axis i)).toLp)
      r := by
  have hT' : (0 : ℝ) ≤ S - c := sub_nonneg.mpr hcS
  let ιvel : Icc (0 : ℝ) (S - c) → Icc (0 : ℝ) S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hιvel : Continuous ιvel :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  let σ : Icc (0 : ℝ) (S - c) → Icc c S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hσ : Continuous σ :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  let A : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ => velocityField w hST (ιvel ρ)
  let B : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ =>
    temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST (σ ρ).2)
  have hA : ∀ n, Continuous (fun ρ => (A ρ).jetLp n) :=
    fun n => (velocityField_jetLp_continuous w hST n).comp hιvel
  have hB : ∀ n, Continuous (fun ρ => (B ρ).jetLp n) :=
    fun n => (temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ
  have hd : ∀ t (ht : t ∈ Ioo 0 (S - c)) x,
      HasDerivAt (fun ρ => (A (projIcc 0 (S - c) hT' ρ)).field x)
        ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t := by
    intro t ht x
    have htc : t + c ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.1, hc], by linarith [ht.2, hST]⟩
    have hbase := velocity_hasDerivAt_time w htc x
    have hshift : HasDerivAt (fun ρ : ℝ => ρ + c) 1 t := (hasDerivAt_id t).add_const c
    have hcomp := hbase.scomp t hshift
    rw [one_smul] at hcomp
    have h₁ : (fun ρ => w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x))
        =ᶠ[𝓝 t] ((fun ρ : ℝ => w.velocity (ρ, x)) ∘ (fun ρ : ℝ => ρ + c)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun ρ hρ => by
        show w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x) = w.velocity (ρ + c, x)
        rw [projIcc_of_mem hT' (Ioo_subset_Icc_self hρ)])
    exact hcomp.congr_of_eventuallyEq h₁
  change HasDerivAt
    (fun ρ : ℝ => ∑ i : Fin 3,
      ‖((A (projIcc (0 : ℝ) (S - c) hT' ρ)).directionalField (axis i)).toLp‖ ^ 2)
    (2 * ∑ i : Fin 3,
      @inner ℝ _ _
        ((A ⟨r, hr.1.le, hr.2.le⟩).directionalField (axis i)).toLp
        ((B ⟨r, hr.1.le, hr.2.le⟩).directionalField (axis i)).toLp)
    r
  have hOne := wordEnergy_hasDerivWithinAt (S - c) hT' A B hA hB hd 1
    ⟨r, hr.1.le, hr.2.le⟩
  have hZero := wordEnergy_hasDerivWithinAt (S - c) hT' A B hA hB hd 0
    ⟨r, hr.1.le, hr.2.le⟩
  have hdiff := (hOne.sub hZero).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  simp only [wordEnergy_one, wordInner_sum_one, Nat.zero_add, wordEnergy_zero,
    wordInner_sum_zero] at hdiff
  have hval :
      2 * (@inner ℝ _ _ (A ⟨r, hr.1.le, hr.2.le⟩).toLp
            (B ⟨r, hr.1.le, hr.2.le⟩).toLp +
            ∑ i : Fin 3, @inner ℝ _ _
              ((A ⟨r, hr.1.le, hr.2.le⟩).directionalField (axis i)).toLp
              ((B ⟨r, hr.1.le, hr.2.le⟩).directionalField (axis i)).toLp) -
          2 * @inner ℝ _ _ (A ⟨r, hr.1.le, hr.2.le⟩).toLp
            (B ⟨r, hr.1.le, hr.2.le⟩).toLp =
        2 * ∑ i : Fin 3, @inner ℝ _ _
          ((A ⟨r, hr.1.le, hr.2.le⟩).directionalField (axis i)).toLp
          ((B ⟨r, hr.1.le, hr.2.le⟩).directionalField (axis i)).toLp := by
    ring
  rw [hval] at hdiff
  refine hdiff.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro ρ
  change (∑ i : Fin 3,
      ‖((A (projIcc (0 : ℝ) (S - c) hT' ρ)).directionalField (axis i)).toLp‖ ^ 2) =
    (‖(A (projIcc (0 : ℝ) (S - c) hT' ρ)).toLp‖ ^ 2 +
      ∑ i : Fin 3,
        ‖((A (projIcc (0 : ℝ) (S - c) hT' ρ)).directionalField (axis i)).toLp‖ ^ 2) -
      ‖(A (projIcc (0 : ℝ) (S - c) hT' ρ)).toLp‖ ^ 2
  ring

/-! ## Integration by parts -/

/-- The carrier-B integration-by-parts identity behind the second equality in row E5:
the sum of the coordinate-derivative pairings is the negative pairing of the Laplacian
with the undifferentiated second field. -/
theorem directional_pairing_sum_eq_neg_laplacian (A B : SmoothL2Field Space) :
    (∑ i : Fin 3, @inner ℝ _ _ (A.directionalField (axis i)).toLp
      (B.directionalField (axis i)).toLp) =
      -(@inner ℝ _ _ (laplacianField A).toLp B.toLp) := by
  rw [laplacianField, toLp_sumField, sum_inner, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := field_directional_inner (A.directionalField (axis i)) B (axis i)
  linarith

/-- **Row E5, second equality.**  The derivative value from
`enstrophyDerivative_hasDerivAt` equals
`-2⟪Δu(t,·),∂ₜu(t,·)⟫_{L²}`. -/
theorem enstrophyDerivative_eq_neg_laplacian
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    2 * ∑ i : Fin 3,
        @inner ℝ _ _
          ((velocitySliceField w (Ioo_subset_Ico_self ht)).directionalField (axis i)).toLp
          ((temporalSliceField w hf ht).directionalField (axis i)).toLp =
      -2 * (@inner ℝ _ _
        (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        (temporalSliceField w hf ht).toLp) := by
  rw [directional_pairing_sum_eq_neg_laplacian]
  ring

/-- **Clamp-free row E5.**  At every `t ∈ Ioo 0 T`, the genuine squared-gradient energy
has derivative the negative Laplacian/time-derivative pairing. -/
theorem enstrophyDerivative_classical_unconditional
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s : ℝ => ∫ x, ∑ i : Fin 3,
        ‖fderiv ℝ (fun y : Space => w.velocity (s, y)) x (axis i)‖ ^ 2)
      (-2 * (@inner ℝ _ _
        (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        (temporalSliceField w hf ht).toLp))
      t := by
  have hc : 0 < t / 2 := by linarith [ht.1]
  have hcS : t / 2 ≤ (t + T) / 2 := by linarith [ht.2]
  have hST : (t + T) / 2 < T := by linarith [ht.2]
  have hr : t - t / 2 ∈ Ioo (0 : ℝ) ((t + T) / 2 - t / 2) := by
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  have hg := enstrophyDerivative_hasDerivAt w hf hc hcS hST hr
  have harith : (t - t / 2) + t / 2 = t := by ring
  have hunshift : HasDerivAt (fun s : ℝ => s - t / 2) 1 t :=
    (hasDerivAt_id t).sub_const (t / 2)
  have hcomp := hg.comp t hunshift
  rw [mul_one] at hcomp
  have hvel : velocitySliceField w (Ioo_subset_Ico_self
        (mem_Ioo_of_mem_Icc hc hST (show (t - t / 2) + t / 2 ∈ Icc (t / 2) ((t + T) / 2) from
          ⟨by linarith [hr.1], by linarith [hr.2]⟩)))
      = velocitySliceField w (Ioo_subset_Ico_self ht) :=
    field_ext (by simp only [velocitySliceField_field, harith])
  have htmp : temporalSliceField w hf
        (mem_Ioo_of_mem_Icc hc hST (show (t - t / 2) + t / 2 ∈ Icc (t / 2) ((t + T) / 2) from
          ⟨by linarith [hr.1], by linarith [hr.2]⟩))
      = temporalSliceField w hf ht :=
    field_ext (by simp only [temporalSliceField_field, harith])
  rw [hvel, htmp, enstrophyDerivative_eq_neg_laplacian w hf ht] at hcomp
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds
      (show t ∈ Ioo (t / 2) ((t + T) / 2) from
        ⟨by linarith [ht.1], by linarith [ht.2]⟩)] with s hs
  have hsS : s ∈ Icc (0 : ℝ) ((t + T) / 2) :=
    ⟨by linarith [hs.1, ht.1], hs.2.le⟩
  have hsSc : s - t / 2 ∈ Icc (0 : ℝ) ((t + T) / 2 - t / 2) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simp only [Function.comp]
  have hgrad : (∫ x, ∑ i : Fin 3,
      ‖fderiv ℝ (fun y : Space => w.velocity (s, y)) x (axis i)‖ ^ 2) =
      ∑ i : Fin 3,
        ‖((velocityField w hST ⟨s, hsS⟩).directionalField (axis i)).toLp‖ ^ 2 := by
    simpa only [velocityField_field] using
      (gradientSq_eq_sum (velocityField w hST ⟨s, hsS⟩)).symm
  rw [hgrad]
  refine congrArg (fun Z : SmoothL2Field Space =>
    ∑ i : Fin 3, ‖(Z.directionalField (axis i)).toLp‖ ^ 2) ?_
  refine congrArg (velocityField w hST) (Subtype.ext ?_)
  rw [projIcc_of_mem (sub_nonneg.mpr hcS) hsSc]
  show s = (s - t / 2) + t / 2
  ring

end NSFormalization.Section4.C01
