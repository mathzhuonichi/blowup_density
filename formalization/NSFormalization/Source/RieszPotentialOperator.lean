import NSFormalization.Source.RieszComplexPotential

/-! The actual unnormalized complex Riesz potential as a bounded linear operator. -/
noncomputable section
namespace NSFormalization.RieszPotentialOperator
open MeasureTheory
open NSFormalization.RieszComplexPotential NSFormalization.RieszPotentialLp
open scoped ENNReal
abbrev Space := NSFormalization.RieszPotentialAssembly.Space

theorem complexPotential_add_ae {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g h : Space → ℂ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    complexPotential a (g + h) =ᵐ[volume] complexPotential a g + complexPotential a h := by
  filter_upwards [ae_integrable ha ha3 hg, ae_integrable ha ha3 hh] with x hx hy
  simp only [complexPotential, Pi.add_apply, smul_add]
  exact integral_add hx hy

theorem complexPotential_smul (a : ℝ) (c : ℂ) (g : Space → ℂ) :
    complexPotential a (c • g) = c • complexPotential a g := by
  funext x
  simp only [complexPotential, Pi.smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => smul_comm (‖y‖ ^ (a-3)) c (g (x-y)))

def potentialToLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    Lp ℂ (ENNReal.ofReal (targetExponent a)) (volume : Measure Space) :=
  (complexPotential_memLp ha ha3 (Lp.memLp g)).toLp (complexPotential a g)

theorem potentialToLp_coe_ae {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    ⇑(potentialToLp ha ha3 g) =ᵐ[volume] complexPotential a g :=
  MemLp.coeFn_toLp _

def potentialLinearMap {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2) :
    Lp ℂ 2 (volume : Measure Space) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal (targetExponent a)) (volume : Measure Space) where
  toFun := potentialToLp ha ha3
  map_add' g h := by
    apply Lp.ext
    have he := complexPotential_congr_ae (Lp.coeFn_add g h) a
    exact (potentialToLp_coe_ae ha ha3 (g+h)).trans
      ((Filter.EventuallyEq.of_eq he).trans
        ((complexPotential_add_ae ha ha3 (Lp.memLp g) (Lp.memLp h)).trans
          (((potentialToLp_coe_ae ha ha3 g).add (potentialToLp_coe_ae ha ha3 h)).symm.trans
            (Lp.coeFn_add _ _).symm)))
  map_smul' c g := by
    apply Lp.ext
    have he := complexPotential_congr_ae (Lp.coeFn_smul c g) a
    exact (potentialToLp_coe_ae ha ha3 (c • g)).trans
      ((Filter.EventuallyEq.of_eq (he.trans (complexPotential_smul a c g))).trans
        (((potentialToLp_coe_ae ha ha3 g).const_smul c).symm.trans (Lp.coeFn_smul _ _).symm))

theorem potentialToLp_norm_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    ‖potentialToLp ha ha3 g‖ ≤
      (potentialConstant a * (512:ℝ)^(1/targetExponent a)) * ‖g‖ := by
  rw [potentialToLp, Lp.norm_toLp, Lp.norm_def]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNorm_complexPotential_le ha ha3 (Lp.memLp g))
  rw [ENNReal.toReal_ofReal (by unfold potentialConstant; positivity)] at hb
  exact hb

theorem targetExponent_one_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2) :
    1 ≤ ENNReal.ofReal (targetExponent a) := by
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  unfold targetExponent
  apply (le_div_iff₀ (by linarith : 0 < 3 - 2*a)).2
  linarith

def potentialOperator {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2) :
    letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) := ⟨targetExponent_one_le ha ha3⟩
    Lp ℂ 2 (volume : Measure Space) →L[ℂ]
      Lp ℂ (ENNReal.ofReal (targetExponent a)) (volume : Measure Space) := by
  letI : Fact (1 ≤ ENNReal.ofReal (targetExponent a)) := ⟨targetExponent_one_le ha ha3⟩
  exact (potentialLinearMap ha ha3).mkContinuous
    (potentialConstant a * (512:ℝ)^(1/targetExponent a))
    (potentialToLp_norm_le ha ha3)

theorem potentialOperator_coe_ae {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    ⇑(potentialOperator ha ha3 g) =ᵐ[volume] complexPotential a g :=
  potentialToLp_coe_ae ha ha3 g

/-- The output quotient is the quotient of the actual integral for every L2 representative. -/
theorem potentialOperator_toLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : MemLp g 2 volume) :
    potentialOperator ha ha3 (hg.toLp g) =
      (complexPotential_memLp ha ha3 hg).toLp (complexPotential a g) := by
  apply Lp.ext
  exact (potentialOperator_coe_ae ha ha3 (hg.toLp g)).trans
    ((Filter.EventuallyEq.of_eq (complexPotential_congr_ae (MemLp.coeFn_toLp hg) a)).trans
      (MemLp.coeFn_toLp _).symm)

theorem potentialOperator_norm_le {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (g : Lp ℂ 2 (volume : Measure Space)) :
    ‖potentialOperator ha ha3 g‖ ≤
      (potentialConstant a * (512:ℝ)^(1/targetExponent a)) * ‖g‖ :=
  potentialToLp_norm_le ha ha3 g

end NSFormalization.RieszPotentialOperator
