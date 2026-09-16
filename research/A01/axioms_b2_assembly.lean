import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A04.ZeroSolution

noncomputable section

namespace NSFormalization.Section4.A01.B2AssemblyConformance

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.A02 (ClassicalSolutionR)
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open scoped ContDiff

#print axioms NSFormalization.Section4.A01.constructedVelocity
#print axioms NSFormalization.Section4.A01.constructedVelocity_slice
#print axioms NSFormalization.Section4.A01.constructedVelocity_zero
#print axioms NSFormalization.Section4.A01.velocity_divergence
#print axioms NSFormalization.Section4.A01.velocitySobolev_of_hslice
#print axioms NSFormalization.Section4.A01.pressurePotential_contDiffOn_slab
#print axioms NSFormalization.Section4.A01.momentum_of_supplied_gradient
#print axioms NSFormalization.Section4.A01.carrierConstructor_of_localTheory
#print axioms NSFormalization.Section4.A01.CarrierConstructorFullClamped
#print axioms NSFormalization.Section4.A01.PressureSupply
#print axioms NSFormalization.Section4.A01.CarrierConstructorFull
#print axioms NSFormalization.Section4.A01.carrierConstructorFull_of_hyps
#print axioms NSFormalization.Section4.A01.apriori_rows_of_hslice_same_horizon
#print axioms NSFormalization.Section4.A01.rows_from_constructor_full

/-! The three open rungs are all inhabited by the zero carrier.  Applying the
actual assembly theorem, rather than inserting `A04.zeroSol` directly, produces
a genuine solution whose velocity is zero on the honest horizon. -/
example :
    ∃ w : ClassicalSolutionR 1
        (fun x : Space => (0 : NSFormalization.Section4.A02.SpaceTimeField) (0, x)) 0
        (1 : ℝ),
      w.velocity = 0 ∧
      ∀ t : Icc (0 : ℝ) 1,
        (fun x : Space => w.velocity (t.1, x)) =ᵐ[volume]
          ⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t) := by
  let u : C(Icc (0 : ℝ) 1, SobolevSpace 1 (6 + 1)) := 0
  let U : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2) := 0
  have hU : ∀ t, ordinaryLift (U t) = value 1 (u t) := by
    intro t
    change ordinaryLift (0 : EulerMeanSolenoidal.L2) =
      value 1 (0 : SobolevSpace 1 (6 + 1))
    rw [map_zero]
    rfl
  have hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0 := by
    intro t
    change (0 : LiftL2 1) ∈ divergenceFreeSpace 1 1 0
    exact Submodule.zero_mem _
  have hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
    intro m
    refine ⟨fun _ => 0, contDiffOn_const, ?_⟩
    intro t
    apply IsSobolevDatum.congr_field (isSobolevDatum_zero (m : ℝ))
    exact (Lp.coeFn_zero Space 2 volume).symm
  let velocity : NSFormalization.Section4.A02.SpaceTimeField := 0
  have hslice : ∀ t : Icc (0 : ℝ) 1,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t) := by
    intro t
    change (0 : Space → Space) =ᵐ[volume] ⇑(0 : EulerMeanSolenoidal.L2)
    exact (Lp.coeFn_zero Space 2 volume).symm
  have hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) := contDiffOn_const
  let G : NSFormalization.Section4.A02.SpaceTimeField := 0
  have hgradient_zero : pressureGradientOfVelocity 1 0 velocity = 0 := by
    funext z
    simp [velocity, pressureGradientOfVelocity, momentumResidualOfVelocity,
      NavierStokes.ProblemStatement.advection,
      NavierStokes.ProblemStatement.spatialLaplacian,
      NavierStokes.ProblemStatement.spatialDerivative,
      NavierStokes.ProblemStatement.temporalDerivative]
  have hG_int : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity 1 0 velocity (t, x) := by
    intro t ht x
    rw [hgradient_zero]
  have hG :
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) 1 ×ˢ (univ : Set Space)) ∧
      ∀ t ∈ Ico (0 : ℝ) 1,
        MemLp (fun x : Space => G (t, x)) 2 volume ∧
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x)) := by
    refine ⟨contDiffOn_const, ?_⟩
    intro t ht
    refine ⟨MemLp.zero', ?_⟩
    change RadialPotential.HasSymmetricJacobian (fun _ : Space => (0 : Space))
    refine ⟨differentiable_const 0, ?_⟩
    intro x i j
    simp
  have hresult := carrierConstructor_of_localTheory (q := 6) (S := 1) (ν := 1)
    (by norm_num) u U hU hdiv 0 velocity hslice hsob hc3 G hG_int hG
  exact hresult

/-! Satisfiability probe.  Each named regularity input is obtained by a one-line
restriction of a standard global property, while `hslice` is exactly the
representative identity supplied by lane 190. -/
example {q : ℕ} {S ν : ℝ} (hS : 0 < S)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (f velocity : NSFormalization.Section4.A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hsobGlobal : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiff ℝ 0 G ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (hvelocityGlobal : ContDiff ℝ ∞ velocity)
    (hgradientGlobal : ContDiff ℝ ∞ (pressureGradientOfVelocity ν f velocity))
    (hgradientMemLp : ∀ t : ℝ,
      MemLp (fun x : Space => pressureGradientOfVelocity ν f velocity (t, x)) 2 volume)
    (hgradientSymm : ∀ t : ℝ,
      RadialPotential.HasSymmetricJacobian (fun x : Space =>
        pressureGradientOfVelocity ν f velocity (t, x))) :
    ∃ w : ClassicalSolutionR ν (fun x : Space => velocity (0, x)) f S,
      w.velocity = velocity ∧
        ∀ t : Icc (0 : ℝ) S,
          (fun x : Space => w.velocity (t.1, x)) =ᵐ[volume] ⇑(U t) := by
  have hsob : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
    intro m; obtain ⟨G, hG, hd⟩ := hsobGlobal m; exact ⟨G, hG.contDiffOn, hd⟩
  have hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := hvelocityGlobal.contDiffOn
  let G := pressureGradientOfVelocity ν f velocity
  have hG_int : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x : Space,
      G (t, x) = pressureGradientOfVelocity ν f velocity (t, x) := by
    intros
    rfl
  have hGSmooth : ContDiffOn ℝ ∞ G
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) := hgradientGlobal.contDiffOn
  have hGMem : ∀ t ∈ Ico (0 : ℝ) S,
      MemLp (fun x : Space => G (t, x)) 2 volume :=
    fun t _ => hgradientMemLp t
  have hGSymm : ∀ t ∈ Ico (0 : ℝ) S,
      RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x)) :=
    fun t _ => hgradientSymm t
  exact carrierConstructor_of_localTheory hS u U hU hdiv f velocity hslice hsob hc3
    G hG_int ⟨hGSmooth, fun t ht => ⟨hGMem t ht, hGSymm t ht⟩⟩

end NSFormalization.Section4.A01.B2AssemblyConformance
