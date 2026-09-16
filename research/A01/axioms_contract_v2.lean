import Tests.LocalTheoryV2
import NSFormalization.Section4.D01.OrderZeroSymbol
import NavierStokes.SpatialCurl

/-!
# Axiom and non-vacuity audit for A01 local theory V2

Besides printing the binding's transitive axioms, this file instantiates the
registered API simultaneously at a concrete nonzero compactly supported force
and a concrete nonzero compactly supported solenoidal datum.  The H⁷ lower
bound returns an actual real `δ` together with `0 < δ`; hence the quantitative
field is not exercised through an empty hypothesis class or a zero-only case.
-/

noncomputable section

open Set Metric MeasureTheory NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Tests
open NSFormalization.Section4
open scoped ContDiff ENNReal

namespace Lane212AxiomAudit

/-! ## A concrete nonzero force in `F_R` -/

def timeBump : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
def spaceBump : ContDiffBump (0 : Space) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

def nonzeroForce : SpaceTimeField :=
  fun p => (timeBump p.1 * spaceBump p.2) • (EuclideanSpace.single 0 1 : Space)

def forceSupport : Set SpaceTime :=
  closedBall (2 : ℝ) 1 ×ˢ closedBall (0 : Space) 1

theorem nonzeroForce_zero_outside : ∀ p ∉ forceSupport, nonzeroForce p = 0 := by
  intro p hp
  have hz : timeBump p.1 * spaceBump p.2 = 0 := by
    by_cases h1 : p.1 ∈ closedBall (2 : ℝ) 1
    · have h2 : p.2 ∉ closedBall (0 : Space) 1 := fun h => hp ⟨h1, h⟩
      have hd : (1 : ℝ) ≤ dist p.2 0 :=
        le_of_lt (by simpa [mem_closedBall] using h2)
      rw [show spaceBump p.2 = 0 from spaceBump.zero_of_le_dist hd, mul_zero]
    · have hd : (1 : ℝ) ≤ dist p.1 2 :=
        le_of_lt (by simpa [mem_closedBall] using h1)
      rw [show timeBump p.1 = 0 from timeBump.zero_of_le_dist hd, zero_mul]
  rw [nonzeroForce, hz, zero_smul]

theorem nonzeroForce_compact : D01.MemForceCompact nonzeroForce := by
  have hKc : IsCompact forceSupport :=
    (isCompact_closedBall (2 : ℝ) 1).prod (isCompact_closedBall (0 : Space) 1)
  have hKcl : IsClosed forceSupport := isClosed_closedBall.prod isClosed_closedBall
  refine ⟨?_, HasCompactSupport.intro hKc nonzeroForce_zero_outside, ?_⟩
  · exact (((timeBump.contDiff (n := (⊤ : ℕ∞))).comp contDiff_fst).mul
      ((spaceBump.contDiff (n := (⊤ : ℕ∞))).comp contDiff_snd)).smul contDiff_const
  · refine (closure_minimal
      (Function.support_subset_iff'.2 nonzeroForce_zero_outside) hKcl).trans ?_
    rintro ⟨t, x⟩ ⟨ht, -⟩
    refine ⟨?_, mem_univ x⟩
    have hb : |t - 2| ≤ 1 := by simpa [Real.dist_eq] using ht
    obtain ⟨ha, -⟩ := abs_le.mp hb
    simp only [mem_Ioi]
    linarith

theorem nonzeroForce_memForceR : MemForceR nonzeroForce :=
  D01.memForceR_of_memForceCompact nonzeroForce_compact

theorem nonzeroForce_ne_zero : nonzeroForce ≠ 0 := by
  intro hF
  have ht : timeBump (2 : ℝ) = 1 :=
    timeBump.one_of_mem_closedBall (by norm_num [timeBump, mem_closedBall])
  have hx : spaceBump (0 : Space) = 1 :=
    spaceBump.one_of_mem_closedBall (by norm_num [spaceBump, mem_closedBall])
  have hp := congrFun hF (2, 0)
  change (timeBump 2 * spaceBump 0) • (EuclideanSpace.single 0 1 : Space) = 0 at hp
  rw [ht, hx, one_mul, one_smul] at hp
  have hcoord := congrFun (congrArg (fun v : Space => (v : Fin 3 → ℝ)) hp) 0
  simp at hcoord

/-! ## A concrete nonzero solenoidal datum in `X_R` -/

def datumPotentialCLM : Space →L[ℝ] Space :=
  (EuclideanSpace.proj 0).smulRight (coordinateVector 1)

def datumPotential : Space → Space := datumPotentialCLM

def nonzeroDatum : SpatialField :=
  NavierStokes.SpatialCurl.curl
    (fun x => D01.Cut.bump x • datumPotential x)

theorem nonzeroDatum_smooth : ContDiff ℝ ∞ nonzeroDatum := by
  apply NavierStokes.SpatialCurl.contDiff_curl
    (D01.Cut.bump_smooth.smul datumPotentialCLM.contDiff)
  simp

theorem nonzeroDatum_compact : HasCompactSupport nonzeroDatum :=
  NavierStokes.SpatialCurl.hasCompactSupport_curl_cutoff
    D01.Cut.bump_cs datumPotential

theorem nonzeroDatum_memLp (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n nonzeroDatum) 2 volume :=
  (nonzeroDatum_smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
    (nonzeroDatum_compact.iteratedFDeriv n)

theorem nonzeroDatum_mem_initialClassR : nonzeroDatum ∈ initialClassR := by
  refine ⟨D01.memHInfty_of_contDiff_memLp nonzeroDatum_smooth nonzeroDatum_memLp, ?_⟩
  intro x
  change (∑ i : Fin 3,
    (fderiv ℝ nonzeroDatum x (coordinateVector i)) i) = 0
  exact NavierStokes.SpatialCurl.divergence_curl
    ((D01.Cut.bump_smooth.smul datumPotentialCLM.contDiff).contDiffAt.of_le (by simp))

theorem datumPotential_curl_component :
    (NavierStokes.SpatialCurl.curl datumPotential 0) 2 = 1 := by
  unfold NavierStokes.SpatialCurl.curl datumPotential
  rw [datumPotentialCLM.hasFDerivAt.fderiv]
  simp [datumPotentialCLM, NavierStokes.SpatialCurl.curlLinear_apply_two,
    coordinateVector]

theorem nonzeroDatum_ne_zero : nonzeroDatum ≠ 0 := by
  intro hzero
  have hcut : nonzeroDatum 0 = NavierStokes.SpatialCurl.curl datumPotential 0 :=
    NavierStokes.SpatialCurl.curl_cutoff_eq D01.Cut.bump.eventuallyEq_one
  have hcomponent := congrArg (fun v : Space => v 2) (congrFun hzero 0)
  rw [hcut, datumPotential_curl_component] at hcomponent
  simp at hcomponent

theorem nonzeroDatum_H7_ne_top : sobolevENorm 7 nonzeroDatum ≠ ⊤ :=
  D01.sobolevENorm_ne_top_of_contDiff_memLp
    nonzeroDatum_smooth nonzeroDatum_memLp 7

/-! ## Concrete instantiations of the registered fields -/

/-- The selected-solution field applies with both inputs nonzero and produces a
classical solution whose horizon is genuinely positive. -/
example :
    nonzeroDatum ≠ 0 ∧ nonzeroForce ≠ 0 ∧
      ∃ w : ClassicalSolutionR 1 nonzeroDatum nonzeroForce
          (checkedLocalTheoryV2.horizon 1 nonzeroDatum nonzeroForce),
        w.velocity (0, 0) = nonzeroDatum 0 ∧
          0 < checkedLocalTheoryV2.horizon 1 nonzeroDatum nonzeroForce := by
  let w := checkedLocalTheoryV2.solution 1 nonzeroDatum nonzeroForce
    (by norm_num) nonzeroDatum_mem_initialClassR nonzeroForce_memForceR
  exact ⟨nonzeroDatum_ne_zero, nonzeroForce_ne_zero, w, w.initial 0, w.horizon_pos⟩

/-- The fixed-force H⁷ field returns an actual positive real lower bound for
the same concrete nonzero force and nonzero datum. -/
example : ∃ δ : ℝ, 0 < δ ∧
    δ ≤ checkedLocalTheoryV2.horizon 1 nonzeroDatum nonzeroForce := by
  obtain ⟨δ, hδ, hall⟩ := checkedLocalTheoryV2.horizon_lower_bound
    1 (by norm_num) nonzeroForce nonzeroForce_memForceR
    (sobolevENorm 7 nonzeroDatum) nonzeroDatum_H7_ne_top
  exact ⟨δ, hδ, hall nonzeroDatum nonzeroDatum_mem_initialClassR le_rfl⟩

end Lane212AxiomAudit

#print axioms BlowupDensity.Bindings.localTheoryV2_convectionDivergence_eq
#print axioms BlowupDensity.Bindings.localTheoryV2_hasSymmetricJacobian_eq
#print axioms BlowupDensity.Bindings.localTheoryV2_isLerayComplement_eq
#print axioms BlowupDensity.Bindings.localTheoryV2_pressurePotential_eq
#print axioms BlowupDensity.Bindings.localTheoryV2_sobolevENorm_eq
#print axioms BlowupDensity.Bindings.localTheoryV2_toA02_ofA02
#print axioms BlowupDensity.Bindings.localTheoryV2_ofA02_toA02
#print axioms BlowupDensity.Bindings.localTheoryV2_regularity_ofA02
#print axioms BlowupDensity.Bindings.localTheoryV2
#print axioms BlowupDensity.Bindings.regularityPartial_of_v2
#print axioms BlowupDensity.Tests.checkedLocalTheoryV2
#print axioms Lane212AxiomAudit.nonzeroForce_memForceR
#print axioms Lane212AxiomAudit.nonzeroForce_ne_zero
#print axioms Lane212AxiomAudit.nonzeroDatum_mem_initialClassR
#print axioms Lane212AxiomAudit.nonzeroDatum_ne_zero
#print axioms Lane212AxiomAudit.nonzeroDatum_H7_ne_top
