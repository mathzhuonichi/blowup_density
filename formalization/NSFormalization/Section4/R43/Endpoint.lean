import NSFormalization.Section4.R43.ForcePath
import NSFormalization.Section4.R43.MaximalEndpoint
import NSFormalization.Section4.A04.ShiftedExtension

/-! Proposition 4.3 at zero datum. The force norm in the final theorem is
exactly `research/R43/Spec.lean:243–247`. The homogeneous version is stronger.
The endpoint integral uses C01's uniform budget at S, never a value of u(S). -/
noncomputable section
namespace NSFormalization.Section4.R43
open Set MeasureTheory
open A02
open D01 (forceSobolevENormL1)
open D01.Homogeneous (forceHomogeneousENorm)
open scoped ENNReal

/-- One viscosity-independent radius for the bootstrap and C01 absorption. -/
def criticalConst : ℝ :=
  min (1 / (8 * trilinearConst))
    (1 / (4 * (A05.gradientL6Const * A05.criticalL3Const)))

/-- The radius is strictly positive. -/
theorem criticalConst_pos : 0 < criticalConst := by
  unfold criticalConst
  exact lt_min (by positivity [trilinearConst_pos])
    (by positivity [A05.gradientL6Const_pos, A05.criticalL3Const_pos])

/-- Strict room in the critical bootstrap. -/
theorem criticalConst_lt_bootstrap : criticalConst < 1 / (2 * trilinearConst) := by
  apply lt_of_le_of_lt (min_le_left _ _)
  apply div_lt_div_of_pos_left one_pos (by positivity [trilinearConst_pos])
  linarith [trilinearConst_pos]

/-- The second radius restriction is precisely C01's L³ gate. -/
theorem criticalConst_absorption :
    A05.gradientL6Const * A05.criticalL3Const * criticalConst ≤ 1 / 4 := by
  have hp : 0 < A05.gradientL6Const * A05.criticalL3Const :=
    mul_pos A05.gradientL6Const_pos A05.criticalL3Const_pos
  calc
    _ ≤ A05.gradientL6Const * A05.criticalL3Const *
        (1 / (4 * (A05.gradientL6Const * A05.criticalL3Const))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le
    _ = 1 / 4 := by
      field_simp
      exact div_self hp.ne'

/-- Global homogeneous smallness controls every finite forcing prefix. -/
theorem criticalForcePrimitive_le_criticalConst {ν S : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f) (hS : 0 ≤ S)
    (hsmall : forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν)) :
    criticalForcePrimitive f S ≤ criticalConst * ν := by
  exact (ENNReal.ofReal_le_ofReal_iff (mul_pos criticalConst_pos hν).le).mp
    ((criticalForcePrimitive_le_forceHomogeneousENorm hf hS).trans hsmall.le)

/-- The bootstrap bound on every slice strictly inside a classical horizon. -/
theorem criticalNormAt_le_criticalConst {ν T : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν (fun _ => 0) f T)
    (hsmall : forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    criticalNormAt w.velocity t ≤ criticalConst * ν :=
  critical_bootstrap_zero_datum hν hf w ht.1 ht.2 criticalConst_pos.le
    criticalConst_lt_bootstrap (criticalForcePrimitive_le_criticalConst hν hf ht.1 hsmall)
    t ⟨ht.1, le_rfl⟩

/-- S3 discharged with the registered embedding and absorption constants. -/
theorem critical_absorption_of_small_force {ν T : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν (fun _ => 0) f T)
    (hsmall : forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice w.velocity t) ≤
      ENNReal.ofReal (ν / 4) := by
  apply criticalL3_gate_enorm A05.gradientL6Const_pos.le A05.criticalL3Const_pos.le
    hν (criticalNormAt_le_criticalConst hν hf w hsmall ht) _ criticalConst_absorption
  have he := A05.velocityCriticalL3 _ (C01.velocity_slice_memHInfty w ht)
  have hd := criticalVelocityHalf_isDatum w t ht
  rw [A05.u1_dotHomogeneousENorm_eq hd] at he
  rw [criticalNormAt_eq_norm hd, ENNReal.ofReal_mul A05.criticalL3Const_pos.le,
    ofReal_norm]
  exact he

/-- The maximal family inherits absorption on all presingular slices. -/
theorem maximal_critical_absorption {ν : ℝ} {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (hf : MemForceR f)
    (hu : IsMaximalSolution ν (fun _ => 0) f u p)
    (hsmall : forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    {t : ℝ} (ht : t ∈ presingularTimes ν (fun _ => 0) f) :
    ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice u t) ≤
      ENNReal.ofReal (ν / 4) := by
  obtain ⟨T, htT, w, hw, _⟩ := hu.exists_solution_after ht
  simpa only [hw] using critical_absorption_of_small_force hν hf w hsmall ⟨ht.1, htT⟩

/-- The explicit zero-datum C01 budget at every finite S up to the lifespan.
All shorter intervals use this same S-dependent budget in the gluing argument. -/
theorem maximal_h2TimeIntegral_zero_of_small_force
    {ν S : ℝ} {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (hf : MemForceR f)
    (hu : IsMaximalSolution ν (fun _ => 0) f u p)
    (hsmall : forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    (hS : 0 < S) (hSL : ENNReal.ofReal S ≤ maximalLifespanR ν (fun _ => 0) f) :
    ∫⁻ t in Ioo (0 : ℝ) S, D01.sobolevENorm 2 (C01.slice u t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * C01.forcePrimitive f S ^ 2 +
        32 * (ν⁻¹) ^ 2 * ∫ t in (0 : ℝ)..S, C01.l2Sq (C01.slice f t)) := by
  have hb := maximal_h2TimeIntegral hν zero_mem_initialClassR hf hu hS hSL
    (fun t ht => maximal_critical_absorption hν hf hu hsmall
      ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hS).mpr ht.2).trans_le hSL⟩)
  simpa [C01.energyBudget, C01.l2Norm, C01.l2Sq, C01.gradientSq] using hb

/-- S4/G5: finite H² integral including a finite maximal endpoint. -/
theorem maximal_squaredHTwoIntegral_of_small_force
    {ν S : ℝ} {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (hf : MemForceR f)
    (hu : IsMaximalSolution ν (fun _ => 0) f u p)
    (hsmall : forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    (hS : 0 < S) (hSL : ENNReal.ofReal S ≤ maximalLifespanR ν (fun _ => 0) f) :
    A04.squaredHTwoIntegral S u ≠ ⊤ := by
  apply maximal_squaredHTwoIntegral_ne_top hν zero_mem_initialClassR hf hu hS hSL
  intro t ht
  exact maximal_critical_absorption hν hf hu hsmall
    ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hS).mpr ht.2).trans_le hSL⟩

/-- The stronger homogeneous-smallness endpoint theorem. -/
theorem homogeneousAtZero_of_memForceR :
    ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν) →
        maximalLifespanR ν (fun _ => 0) f = ⊤ := by
  intro ν hν f hf hsmall
  obtain ⟨u, p, hu⟩ := exists_maximal' ν (fun _ => 0) f hν zero_mem_initialClassR hf
  exact A04.lifespanInfiniteOfLocallyFinite_of_memForceR' ν (fun _ => 0) f
    hν zero_mem_initialClassR hf u p hu
    (fun _ hS hSL => maximal_squaredHTwoIntegral_of_small_force hν hf hu hsmall hS hSL)

/-- Exactly the `inhomogeneousAtZero` field of `RCritical1API`, with explicit c. -/
theorem inhomogeneousAtZero_of_memForceR :
    ∀ ν : ℝ, 0 < ν → ∀ f : SpaceTimeField, MemForceR f →
      forceSobolevENormL1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν) →
        maximalLifespanR ν (fun _ => 0) f = ⊤ := by
  intro ν hν f hf hsmall
  exact homogeneousAtZero_of_memForceR ν hν f hf
    ((forceHomogeneousENorm_le_forceSobolevENormL1 f hf).trans_lt hsmall)

end NSFormalization.Section4.R43
