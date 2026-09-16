import Tests.ContinuationV2
import NSFormalization.Section4.D01.SmoothDatum
import NavierStokes.SpatialCurl

/-!
Axiom and non-vacuity audit for `A04.continuation_v2`.

The force witness is the established compact spacetime bump used in
`research/R43/axioms_force_path.lean`.  The datum witness is the curl of the
compactly supported smooth potential
`x ↦ (b(x) x₀) e₂`; it is divergence free, belongs to every Sobolev
order, and its second curl component equals `-1` at the origin.  Thus both the
force and datum are genuinely nonzero.
-/

noncomputable section

namespace ContinuationV2ContractConformance

open Set Metric MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.SpatialCurl
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V2.Continuation
open scoped ContDiff ENNReal

/-! ## Axiom boundary -/

#print axioms BlowupDensity.Contracts.V2.Continuation.timeShift
#print axioms BlowupDensity.Contracts.V2.Continuation.squaredHTwoIntegral
#print axioms BlowupDensity.Contracts.V2.Continuation.SolvesBelow
#print axioms BlowupDensity.Contracts.V2.Continuation.MemL1Hm
#print axioms BlowupDensity.Contracts.V2.Continuation.IsMaximalSolution
#print axioms BlowupDensity.Contracts.V2.Continuation.RestartFixedForce
#print axioms BlowupDensity.Contracts.V2.Continuation.ManuscriptHorizonLowerBoundH1
#print axioms BlowupDensity.Contracts.V2.Continuation.ContinuationV2API
#print axioms BlowupDensity.Bindings.continuationV2_restartFixedForce_eq
#print axioms BlowupDensity.Bindings.continuationV2_manuscriptHorizonLowerBoundH1_eq
#print axioms BlowupDensity.Bindings.continuationV2_solvesBelow_iff
#print axioms BlowupDensity.Bindings.continuationV2_isMaximalSolution_iff
#print axioms BlowupDensity.Bindings.continuationV2
#print axioms BlowupDensity.Tests.checkedContinuationV2

/-! ## A concrete nonzero force in `F_R` -/

def forceTimeBump : ContDiffBump (2 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

def forceSpaceBump : ContDiffBump (0 : Space) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- A nonzero compactly supported smooth spacetime force. -/
def nonzeroForce : SpaceTimeField :=
  fun z => (forceTimeBump z.1 * forceSpaceBump z.2) •
    (EuclideanSpace.single 0 1 : Space)

def forceSupport : Set SpaceTime :=
  closedBall (2 : ℝ) 1 ×ˢ closedBall (0 : Space) 1

theorem nonzeroForce_zero_outside : ∀ z ∉ forceSupport, nonzeroForce z = 0 := by
  intro z hz
  have hscalar : forceTimeBump z.1 * forceSpaceBump z.2 = 0 := by
    by_cases ht : z.1 ∈ closedBall (2 : ℝ) 1
    · have hx : z.2 ∉ closedBall (0 : Space) 1 := fun h => hz ⟨ht, h⟩
      have hd : (1 : ℝ) ≤ dist z.2 0 :=
        le_of_lt (by simpa [mem_closedBall] using hx)
      rw [show forceSpaceBump z.2 = 0 from forceSpaceBump.zero_of_le_dist hd,
        mul_zero]
    · have hd : (1 : ℝ) ≤ dist z.1 2 :=
        le_of_lt (by simpa [mem_closedBall] using ht)
      rw [show forceTimeBump z.1 = 0 from forceTimeBump.zero_of_le_dist hd,
        zero_mul]
  change (forceTimeBump z.1 * forceSpaceBump z.2) •
    (EuclideanSpace.single 0 1 : Space) = 0
  rw [hscalar, zero_smul]

theorem nonzeroForce_compact :
    NSFormalization.Section4.D01.MemForceCompact nonzeroForce := by
  have hcompact : IsCompact forceSupport :=
    (isCompact_closedBall (2 : ℝ) 1).prod (isCompact_closedBall (0 : Space) 1)
  have hclosed : IsClosed forceSupport :=
    isClosed_closedBall.prod isClosed_closedBall
  refine ⟨?_, HasCompactSupport.intro hcompact nonzeroForce_zero_outside, ?_⟩
  · exact (((forceTimeBump.contDiff (n := (⊤ : ℕ∞))).comp contDiff_fst).mul
      ((forceSpaceBump.contDiff (n := (⊤ : ℕ∞))).comp contDiff_snd)).smul
        contDiff_const
  · refine (closure_minimal
      (Function.support_subset_iff'.2 nonzeroForce_zero_outside) hclosed).trans ?_
    rintro ⟨t, x⟩ ⟨ht, -⟩
    refine ⟨?_, mem_univ _⟩
    have hb : |t - 2| ≤ 1 := by simpa [Real.dist_eq] using ht
    obtain ⟨hlower, -⟩ := abs_le.mp hb
    simp only [mem_Ioi]
    linarith

theorem nonzeroForce_memForceR : MemForceR nonzeroForce :=
  NSFormalization.Section4.D01.memForceR_of_memForceCompact nonzeroForce_compact

theorem nonzeroForce_ne_zero : nonzeroForce ≠ 0 := by
  intro h
  have ht : forceTimeBump (2 : ℝ) = 1 :=
    forceTimeBump.one_of_mem_closedBall (by norm_num [forceTimeBump, mem_closedBall])
  have hx : forceSpaceBump (0 : Space) = 1 :=
    forceSpaceBump.one_of_mem_closedBall (by norm_num [forceSpaceBump, mem_closedBall])
  have hz := congrFun h (2, 0)
  change (forceTimeBump (2 : ℝ) * forceSpaceBump (0 : Space)) •
    (EuclideanSpace.single 0 1 : Space) = 0 at hz
  rw [ht, hx, one_mul, one_smul] at hz
  have hc := congrFun (congrArg (fun v : Space => (v : Fin 3 → ℝ)) hz) 0
  simp at hc

/-! ## A concrete nonzero datum in `X_R` -/

def datumBump : ContDiffBump (0 : Space) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def datumPotential : Space → Space :=
  fun x => (datumBump x * x 0) • (coordinateVector 2)

def nonzeroDatum : SpatialField := curl datumPotential

theorem datumPotential_smooth : ContDiff ℝ ∞ datumPotential := by
  exact (datumBump.contDiff.mul
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).contDiff).smul
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : Space => (coordinateVector 2 : Space)))

theorem datumPotential_compact : HasCompactSupport datumPotential := by
  have hc := datumBump.hasCompactSupport.smul_right
    (f' := fun x : Space => x 0 • (coordinateVector 2 : Space))
  have heq : datumPotential =
      fun x : Space => datumBump x • (x 0 • (coordinateVector 2 : Space)) := by
    funext x
    simp only [datumPotential, smul_smul]
  rw [heq]
  exact hc

theorem nonzeroDatum_smooth : ContDiff ℝ ∞ nonzeroDatum :=
  contDiff_curl datumPotential_smooth (by simp)

theorem nonzeroDatum_compact : HasCompactSupport nonzeroDatum :=
  hasCompactSupport_curl datumPotential_compact

theorem nonzeroDatum_mem_initialClassR : nonzeroDatum ∈ initialClassR := by
  constructor
  · exact NSFormalization.Section4.D01.memHInfty_of_contDiff_memLp
      nonzeroDatum_smooth
      (fun n => (nonzeroDatum_smooth.continuous_iteratedFDeriv (by simp))
        |>.memLp_of_hasCompactSupport (nonzeroDatum_compact.iteratedFDeriv n))
  · intro x
    exact divergence_curl (datumPotential_smooth.contDiffAt.of_le (by simp))

theorem nonzeroDatum_ne_zero : nonzeroDatum ≠ 0 := by
  intro h
  have hzero := congrFun h 0
  have hb : ∀ᶠ y in nhds (0 : Space), datumBump y = 1 := by
    filter_upwards
      [Metric.closedBall_mem_nhds (x := (0 : Space)) (by norm_num : 0 < (1 : ℝ))]
      with y hy
    exact datumBump.one_of_mem_closedBall hy
  have hp : datumPotential =ᶠ[nhds (0 : Space)]
      fun x => x 0 • coordinateVector 2 := by
    filter_upwards [hb] with y hy
    simp [datumPotential, hy]
  have hd : fderiv ℝ datumPotential 0 =
      fderiv ℝ (fun x : Space => x 0 • coordinateVector 2) 0 :=
    hp.fderiv_eq
  let L : Space →L[ℝ] Space :=
    (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).smulRight (coordinateVector 2)
  have hfun : (fun x : Space => x 0 • coordinateVector 2) = L := rfl
  have hlin : fderiv ℝ (fun x : Space => x 0 • coordinateVector 2) 0 = L := by
    rw [hfun]
    exact L.hasFDerivAt.fderiv
  have hcomponent : nonzeroDatum 0 1 = -1 := by
    change (curlLinear (fderiv ℝ datumPotential 0)) 1 = -1
    rw [hd, hlin]
    simp [L, coordinateVector]
  rw [show nonzeroDatum 0 = 0 from hzero] at hcomponent
  simp at hcomponent

/-- The approved restart field is exercised simultaneously at a nonzero force
and a nonzero admissible datum.  Its output contains a genuine positive real
duration and a concrete lower bound on the actual local horizon. -/
theorem nonvacuous_restart_nonzero_force_datum :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ NSFormalization.Section4.A01.localHorizon' 1 nonzeroDatum
        (timeShift 0 nonzeroForce) := by
  have hK : sobolevENorm 7 nonzeroDatum ≠ ⊤ :=
    NSFormalization.Section4.D01.sobolevENorm_ne_top_of_contDiff_memLp
      nonzeroDatum_smooth
      (fun n => (nonzeroDatum_smooth.continuous_iteratedFDeriv (by simp))
        |>.memLp_of_hasCompactSupport (nonzeroDatum_compact.iteratedFDeriv n)) 7
  obtain ⟨δ, hδ, hr⟩ := BlowupDensity.Tests.checkedContinuationV2.restart
    1 (by norm_num) nonzeroForce nonzeroForce_memForceR 1 (by norm_num)
      (sobolevENorm 7 nonzeroDatum) hK
  exact ⟨δ, hδ, hr 0 (by norm_num) nonzeroDatum
    nonzeroDatum_mem_initialClassR le_rfl⟩

/- These examples expose the concrete nonzero instantiation in example form as
requested by the contract audit. -/
example : nonzeroForce ≠ 0 := nonzeroForce_ne_zero

example : nonzeroDatum ≠ 0 := nonzeroDatum_ne_zero

example :
    ∃ δ : ℝ, 0 < δ ∧
      δ ≤ NSFormalization.Section4.A01.localHorizon' 1 nonzeroDatum
        (timeShift 0 nonzeroForce) :=
  nonvacuous_restart_nonzero_force_datum

#print axioms nonzeroForce_memForceR
#print axioms nonzeroForce_ne_zero
#print axioms nonzeroDatum_mem_initialClassR
#print axioms nonzeroDatum_ne_zero
#print axioms nonvacuous_restart_nonzero_force_datum

end ContinuationV2ContractConformance
