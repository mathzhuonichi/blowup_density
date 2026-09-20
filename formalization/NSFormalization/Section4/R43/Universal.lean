import NSFormalization.Section4.R43.Endpoint

noncomputable section
namespace NSFormalization.Section4.R43
open Set MeasureTheory
open A02
open D01 (dotHomogeneousENorm)
open D01.Homogeneous (forceHomogeneousENorm)
open scoped ENNReal

/-- General initial energy version of the critical scalar bootstrap. -/
theorem critical_norm_bound_general {T ν C K ρ : ℝ} {y E' z b N : ℝ → ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (hC : 0 ≤ C) (hρK : ρ < K)
    (hK : C * K ≤ ν / 2) (hy : Continuous y) (hy0 : y 0 ≤ N 0)
    (hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hN : ContinuousOn N (Icc 0 T))
    (hNbound : ∀ t ∈ Icc 0 T, N t ≤ ρ)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt (fun x => (y x) ^ 2) (E' t) t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t)
    (henergy : ∀ t ∈ Ioo 0 T,
      E' t / 2 + (ν - C * y t) * (z t) ^ 2 ≤ b t * y t) :
    ∀ t ∈ Icc 0 T, y t ≤ ρ := by
  apply NSFormalization.Paper1.continuous_bootstrap hy
    (hy0.trans (hNbound 0 ⟨le_rfl, hT⟩)) hρK
  intro t ht hprefix
  have hsub : Icc 0 t ⊆ Icc 0 T := fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  have hsub' : Ioo 0 t ⊆ Ioo 0 T := fun x hx => ⟨hx.1, hx.2.trans_le ht.2⟩
  have hbnd := C01.sqrt_energy_le_primitive' ht.1 (hy.pow 2).continuousOn
    (hN.mono hsub) (by simpa only [Pi.pow_apply, Real.sqrt_sq (hynonneg 0 ⟨le_rfl, hT⟩)] using hy0) (fun x _ => sq_nonneg (y x))
    (fun x hx => hb x (hsub' hx)) (fun x hx => hdE x (hsub' hx))
    (fun x hx => hdN x (hsub' hx))
    (fun x hx => by
      have hsmall : C * y x ≤ ν / 2 :=
        (mul_le_mul_of_nonneg_left (hprefix x ⟨hx.1.le, hx.2.le⟩) hC).trans hK
      have hd := NSFormalization.Paper1.critical_squared_derivative_bound hν
        (NSFormalization.Paper1.critical_energy_absorption hsmall (henergy x (hsub' hx)))
      simpa only [Pi.pow_apply, Real.sqrt_sq (hynonneg x (hsub ⟨hx.1.le, hx.2.le⟩))] using hd)
    t ⟨ht.1, le_rfl⟩
  simp only [Pi.pow_apply, Real.sqrt_sq (hynonneg t ht)] at hbnd
  exact hbnd.trans (hNbound t ht)

/-- Critical bootstrap with arbitrary initial datum. -/
theorem critical_bootstrap_general
    {ν T S c : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T)
    (hS : 0 ≤ S) (hST : S < T)
    (_hc0 : 0 ≤ c) (hclt : c < 1 / (2 * trilinearConst))
    (hsmall : criticalNormAt w.velocity 0 + criticalForcePrimitive f S ≤ c * ν) :
    ∀ t ∈ Icc (0 : ℝ) S, criticalNormAt w.velocity t ≤ c * ν := by
  let hcrit := criticalDatumPath w hf (criticalDatumInputs_of_classical hν hf w)
  let y : ℝ → ℝ := criticalNormAt w.velocity
  let yExt : ℝ → ℝ := fun r => y (projIcc 0 S hS r)
  have hyIcc : ContinuousOn y (Icc (0 : ℝ) S) :=
    (criticalNormAt_continuousOn hcrit).mono
      (fun t ht => ⟨ht.1, ht.2.trans_lt hST⟩)
  have hyExt : Continuous yExt :=
    (continuousOn_iff_continuous_domRestrict.mp hyIcc).comp continuous_projIcc
  have hynonneg : ∀ t ∈ Icc (0 : ℝ) S, 0 ≤ yExt t := by
    intro t ht
    simp only [yExt, projIcc_of_mem hS ht]
    exact ENNReal.toReal_nonneg
  have hNbound : ∀ t ∈ Icc (0 : ℝ) S, yExt 0 + criticalForcePrimitive f t ≤ c * ν := by
    intro t ht
    have hm := (criticalForcePrimitive_monotoneOn hf) ht.1 hS ht.2
    simpa only [yExt, projIcc_left, y] using (add_le_add_right hm (y 0)).trans hsmall
  have hrc := rcritical1_of_classical' hν hf w
  have hdE : ∀ t ∈ Ioo (0 : ℝ) S,
      HasDerivAt (fun r => yExt r ^ 2)
        (criticalEnergyDerivative hcrit t) t := by
    intro t ht
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans hST⟩
    have heq : (fun r => yExt r ^ 2) =ᶠ[nhds t] (fun r => y r ^ 2) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      simp only [yExt, projIcc_of_mem hS ⟨hr.1.le, hr.2.le⟩]
    exact (hrc.1 t htT).congr_of_eventuallyEq heq
  have henergy : ∀ t ∈ Ioo (0 : ℝ) S,
      criticalEnergyDerivative hcrit t / 2 +
          (ν - trilinearConst * yExt t) *
            criticalDissipationAt w.velocity t ^ 2
        ≤ criticalForceAt f t * yExt t := by
    intro t ht
    have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans hST⟩
    simpa only [yExt, projIcc_of_mem hS ⟨ht.1.le, ht.2.le⟩, y] using hrc.2 t htT
  have hK : trilinearConst * (ν / (2 * trilinearConst)) ≤ ν / 2 := by
    exact le_of_eq (by field_simp [ne_of_gt trilinearConst_pos])
  have hρK : c * ν < ν / (2 * trilinearConst) := by
    calc
      c * ν < (1 / (2 * trilinearConst)) * ν := mul_lt_mul_of_pos_right hclt hν
      _ = _ := by ring
  have hb := critical_norm_bound_general (N := fun t => yExt 0 + criticalForcePrimitive f t) hS hν.le trilinearConst_pos.le hρK hK
    hyExt (by simp only [criticalForcePrimitive_zero, add_zero]; exact le_rfl)
    hynonneg (continuousOn_const.add (criticalForcePrimitive_continuousOn hf hS))
    hNbound (fun t _ => criticalForceAt_nonneg f t) hdE
    (fun t ht => (criticalForcePrimitive_hasDerivAt hf hS ht).const_add (yExt 0))
    henergy
  intro t ht
  simpa only [yExt, projIcc_of_mem hS ht, y] using hb t ht


/-- The ENNReal smallness premise controls the initial norm plus every prefix. -/
theorem critical_initial_add_prefix_le {ν T S : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hS : 0 ≤ S)
    (hsmall : dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
      < ENNReal.ofReal (criticalConst * ν)) :
    criticalNormAt w.velocity 0 + criticalForcePrimitive f S ≤ criticalConst * ν := by
  have ha0 : (fun x => w.velocity (0, x)) = a := funext w.initial
  have hfinite : dotHomogeneousENorm (1 / 2) a ≠ ⊤ :=
    ne_of_lt ((le_add_right le_rfl).trans_lt (hsmall.trans ENNReal.ofReal_lt_top))
  have hp0 : 0 ≤ criticalForcePrimitive f S :=
    intervalIntegral.integral_nonneg hS (fun t _ => criticalForceAt_nonneg f t)
  apply (ENNReal.ofReal_le_ofReal_iff (mul_pos criticalConst_pos hν).le).mp
  rw [ENNReal.ofReal_add (show 0 ≤ criticalNormAt w.velocity 0 from ENNReal.toReal_nonneg) hp0]
  have heq : ENNReal.ofReal (criticalNormAt w.velocity 0) =
      dotHomogeneousENorm (1 / 2) a := by
    rw [criticalNormAt, ha0, ENNReal.ofReal_toReal hfinite]
  rw [heq]
  exact (add_le_add_right (criticalForcePrimitive_le_forceHomogeneousENorm hf hS) _).trans
    hsmall.le

/-- Uniform critical bound on arbitrary classical slices. -/
theorem criticalNormAt_le_general {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f) (w : ClassicalSolutionR ν a f T)
    (hsmall : dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
      < ENNReal.ofReal (criticalConst * ν))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    criticalNormAt w.velocity t ≤ criticalConst * ν :=
  critical_bootstrap_general hν hf w ht.1 ht.2 criticalConst_pos.le
    criticalConst_lt_bootstrap (critical_initial_add_prefix_le hν hf w ht.1 hsmall)
    t ⟨ht.1, le_rfl⟩

/-- S3 discharged with the registered embedding and absorption constants. -/
theorem critical_absorption_general {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T)
    (hsmall : dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice w.velocity t) ≤
      ENNReal.ofReal (ν / 4) := by
  apply criticalL3_gate_enorm A05.gradientL6Const_pos.le A05.criticalL3Const_pos.le
    hν (criticalNormAt_le_general hν hf w hsmall ht) _ criticalConst_absorption
  have he := A05.velocityCriticalL3 _ (C01.velocity_slice_memHInfty w ht)
  have hd := criticalVelocityHalf_isDatum w t ht
  rw [A05.u1_dotHomogeneousENorm_eq hd] at he
  rw [criticalNormAt_eq_norm hd, ENNReal.ofReal_mul A05.criticalL3Const_pos.le,
    ofReal_norm]
  exact he

/-- The maximal family inherits absorption on all presingular slices. -/
theorem maximal_critical_absorption_general {ν : ℝ} {a : SpatialField} {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (hf : MemForceR f)
    (hu : IsMaximalSolution ν a f u p)
    (hsmall : dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    {t : ℝ} (ht : t ∈ presingularTimes ν a f) :
    ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice u t) ≤
      ENNReal.ofReal (ν / 4) := by
  obtain ⟨T, htT, w, hw, _⟩ := hu.exists_solution_after ht
  simpa only [hw] using critical_absorption_general hν hf w hsmall ⟨ht.1, htT⟩

/-- The explicit general-datum C01 budget at every finite S up to the lifespan.
All shorter intervals use this same S-dependent budget in the gluing argument. -/
theorem maximal_h2TimeIntegral_general
    {ν S : ℝ} {a : SpatialField} {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (hu : IsMaximalSolution ν a f u p)
    (hsmall : dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    (hS : 0 < S) (hSL : ENNReal.ofReal S ≤ maximalLifespanR ν a f) :
    ∫⁻ t in Ioo (0 : ℝ) S, D01.sobolevENorm 2 (C01.slice u t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * C01.energyBudget a f S ^ 2 +
        32 * ν⁻¹ * C01.gradientSq a +
        32 * (ν⁻¹) ^ 2 * ∫ t in (0 : ℝ)..S, C01.l2Sq (C01.slice f t)) := by
  have hb := maximal_h2TimeIntegral hν ha hf hu hS hSL
    (fun t ht => maximal_critical_absorption_general hν hf hu hsmall
      ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hS).mpr ht.2).trans_le hSL⟩)
  exact hb

/-- S4/G5: finite H² integral including a finite maximal endpoint. -/
theorem maximal_squaredHTwoIntegral_general
    {ν S : ℝ} {a : SpatialField} {f u : SpaceTimeField} {p : SpaceTimeScalar}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (hu : IsMaximalSolution ν a f u p)
    (hsmall : dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f < ENNReal.ofReal (criticalConst * ν))
    (hS : 0 < S) (hSL : ENNReal.ofReal S ≤ maximalLifespanR ν a f) :
    A04.squaredHTwoIntegral S u ≠ ⊤ := by
  apply maximal_squaredHTwoIntegral_ne_top hν ha hf hu hS hSL
  intro t ht
  exact maximal_critical_absorption_general hν hf hu hsmall
    ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hS).mpr ht.2).trans_le hSL⟩

 /-- Exactly the universal field, with the same explicit constant as lane 223. -/
theorem universal_of_memForceR :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (criticalConst * ν) →
            maximalLifespanR ν a f = ⊤ := by
  intro ν hν a ha f hf hsmall
  obtain ⟨u, p, hu⟩ := exists_maximal' ν a f hν ha hf
  exact A04.lifespanInfiniteOfLocallyFinite_of_memForceR' ν a f hν ha hf u p hu
    (fun _ hS hSL => maximal_squaredHTwoIntegral_general hν ha hf hu hsmall hS hSL)

end NSFormalization.Section4.R43
