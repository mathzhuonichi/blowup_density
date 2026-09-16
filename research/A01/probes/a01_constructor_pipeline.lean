import NSFormalization.Section4.A01.CylinderWiring
import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.PressureRegularity
import NSFormalization.Section4.A04.ZeroSolution
import Euler.OrdinaryCauchyInterpolation
import Euler.SmoothL2Series

noncomputable section
namespace NSFormalization.Section4.A01.A01ConstructorPipeline
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerOrdinarySobolev EulerSmoothL2Series
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Produce lane 180's canonical pressure supply from the landed 192 → 190 →
194/195/197 pipeline. Only the all-order bound is an additional analytic input. -/
theorem pressure_pipeline {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : A02.SpaceTimeField)
    (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ velocity G : A02.SpaceTimeField,
      ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      (∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
        G (t, x) = pressureGradientOfVelocity ν f velocity (t, x)) ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t ∈ Ico (0 : ℝ) S, MemLp (fun x => G (t, x)) 2 volume ∧
        RadialPotential.HasSymmetricJacobian (fun x => G (t, x)) := by
  obtain ⟨U, _hU0, hpairs, hpaths⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ := exists_joint_smooth_representative hS U hpaths
  have hp : PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3 :=
    pressureSupply_of_pieces hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3
  obtain ⟨G, hid, hG, hspatial⟩ := hp
  exact ⟨velocity, G, hc3, hid, hG, hspatial⟩

#print axioms pressure_pipeline

/-- Directly feed `pressureSupply_of_pieces` to lane 180's local classical
constructor after lane 192 selects the same-carrier family and lane 190 selects
its smooth representative. -/
theorem local_constructor_pipeline {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : A02.SpaceTimeField)
    (hf : D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (velocity : A02.SpaceTimeField)
      (w : A02.ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S),
      w.velocity = velocity := by
  obtain ⟨U, _hU0, hpairs, hpaths⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨velocity, hslice, hc3⟩ := exists_joint_smooth_representative hS U hpaths
  obtain ⟨G, hG_int, hG_smooth, hG_slices⟩ :=
    pressureSupply_of_pieces hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3
  obtain ⟨u, hU, hdiv, _hinv, _hduh⟩ := hpairs q hq
  obtain ⟨w, hw, _hslice⟩ := carrierConstructor_of_localTheory hS u U hU hdiv f
    velocity hslice (hpaths 0) hc3 G hG_int ⟨hG_smooth, hG_slices⟩
  exact ⟨velocity, w, hw⟩

#print axioms local_constructor_pipeline

/-- A01 milestone: the complete landed constructor and both comparison rows
close from `hb`; the pressure argument is exactly `pressureSupply_of_pieces`. -/
theorem a01_constructor_pipeline {q : ℕ} (hq : 6 ≤ q)
    {f : A02.SpaceTimeField} (hf : D01.MemForceR f)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (a' : A02.SpatialField) (f' : A02.SpaceTimeField)
      (w : A02.ClassicalSolutionR ν a' f' S),
      ‖u‖ ≤ R q ∧
      (∀ t : Icc (0 : ℝ) S,
        A04.sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ D01.jetSobolevConst (q + 1) *
          A04.sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t) := by
  exact rows_from_constructor_full hq hf hν hS a ha R hb
    (fun U hpairs hpaths velocity hslice hc3 =>
      pressureSupply_of_pieces hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3)

#print axioms a01_constructor_pipeline

-- Reuse the established zero-bound proof, with no assumed bound.
private theorem canonical_zero_initial (q : ℕ) :
    ordinarySobolev q
      (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
      (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine (ordinarySobolev_norm_le_tensor
      (SmoothL2Field.zeroField : SmoothL2Field Space) q).trans ?_
    simp [tensorNorm, zeroField_jet]
  · exact norm_nonneg _

private theorem canonical_zero_force {S : ℝ} (q : ℕ) :
    sobolevPath
      (C01.forcePath (S := S) A04.memForceR_zero)
      (C01.forcePath_jetLp_continuous (S := S) A04.memForceR_zero) q = 0 := by
  apply ContinuousMap.ext
  intro t
  apply norm_eq_zero.mp
  apply le_antisymm
  · refine (ordinarySobolev_norm_le_tensor
      (C01.forcePath (S := S) A04.memForceR_zero t) q).trans ?_
    have hpath : C01.forcePath (S := S) A04.memForceR_zero t =
        (SmoothL2Field.zeroField : SmoothL2Field Space) := by
      unfold C01.forcePath C01.forceSliceField SmoothL2Field.zeroField
      rfl
    rw [hpath]
    simp [tensorNorm, zeroField_jet]
  · exact norm_nonneg _

/-- Genuine satisfiability: zero datum and zero force satisfy the all-order bound for every
nonnegative radius family, without assuming `hb`. -/
theorem zero_all_order_bound (ν S : ℝ) (hν : 0 < ν)
    (R : ℕ → ℝ) (hR : ∀ q, 0 ≤ R q) :
    ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (C01.forcePath (S := S) A04.memForceR_zero)
      (C01.forcePath_jetLp_continuous (S := S) A04.memForceR_zero) (R q) := by
  intro q hq T hT hTS u hu
  have hu0 := canonical_zero_initial (q + 1)
  have hf0 := canonical_zero_force (S := S) q
  rw [hu0, hf0] at hu
  have hz : ∀ t, (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) t =
      quadraticDuhamel 1 ν hν hT hTS
        (coefficients 1 hq 0) 0 0 t := by
    intro t
    simp [quadraticDuhamel, source_eq]
  have huz : u = 0 := by
    rcases hT.eq_or_lt with rfl | hTpos
    · apply ContinuousMap.ext
      intro t
      have ht : t.1 = 0 := le_antisymm t.2.2 t.2.1
      rw [hu t]
      simp [quadraticDuhamel, ht]
    · exact quadratic_mild_unique (q := q) hν hTpos
        (coefficients 1 hq 0) 0 u 0 hu hz
  rw [huz, norm_zero]
  exact hR q


example : ∃ velocity G : A02.SpaceTimeField,
    ContDiffOn ℝ ∞ velocity (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      G (t, x) = pressureGradientOfVelocity 1 0 velocity (t, x)) ∧
    ContDiffOn ℝ ∞ G (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) ∧
    ∀ t ∈ Ico (0 : ℝ) 1, MemLp (fun x => G (t, x)) 2 volume ∧
      RadialPotential.HasSymmetricJacobian (fun x => G (t, x)) := by
  exact pressure_pipeline (q := 6) (by norm_num) (by norm_num) (by norm_num)
    0 A04.memForceR_zero SmoothL2Field.zeroField
    (by intro x; simp [EulerSmoothLimit.divergence, SmoothL2Field.zeroField])
    (fun _ => 0) (zero_all_order_bound 1 1 (by norm_num) (fun _ => 0) (by simp))

end NSFormalization.Section4.A01.A01ConstructorPipeline
