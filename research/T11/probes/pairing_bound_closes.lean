import NSFormalization.Section3.T11.PairingBound

/-!
# Lane 336 probe — the tame pairing bound closes the shape lane 322 needs

Three checks, none of them inside the module:

1. `hRhigh_nonlinear_term_closes` — the nonlinear term of lane 322's `hRhigh`
   binder (`Section3/T11/HighOrder.lean`, `higherOrderBound_of_energyInequality`),
   copied in the exact shape `Chigh m * ‖u(t)‖_{H²} * ‖u(t)‖_{H^m} * g` with
   `g ≥ 0` existentially quantified, is supplied by `torusPairingBound_profile`
   with `Chigh m := torusPairingConstant m` and `g := ‖u(t)‖_{H^{m+1}}`.
2. `reweight_form_closes` — the same with consumer-supplied `H^m` and `H²` data.
3. Non-vacuity at a **nonzero** datum: the shear mode `2 e₂ cos(2πx₀)`
   (two conjugate lattice modes `±(1,0,0)`), for which both sides are finite and
   the right-hand side is strictly positive; the datum is solenoidal, so the
   projected form applies to it as well.
-/

noncomputable section

namespace NSFormalization.Section3.T11.PairingBoundProbe

open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped BigOperators ENNReal ComplexConjugate

local instance probeNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance probeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. The shape `hRhigh` needs -/

/-- **The nonlinear term of `eq:Rhigh` closes.**  Copied from the `hRhigh`
binder of `higherOrderBound_of_energyInequality`: one constant family
`Chigh : ℕ → ℝ`, orders `m ≥ 3`, and a nonnegative `g` playing the role of the
dissipation/gradient norm. -/
theorem hRhigh_nonlinear_term_closes :
    ∃ Chigh : ℕ → ℝ, ∀ (m : ℕ), 3 ≤ m →
      ∀ (u : SpaceTimeField) (t : ℝ) (A : PeriodicSobolev ((m : ℝ) + 1))
        (hr : (3 : ℝ) ≤ (m : ℝ) + 1) (_h2 : (2 : ℝ) ≤ (m : ℝ) + 1)
        (hs : (m : ℝ) ≤ (m : ℝ) + 1),
      IsPeriodicDatum ((m : ℝ) + 1) (fun x ↦ u (t, x)) A →
        ∃ g : ℝ, 0 ≤ g ∧
          |torusRealPairing (torusConvectionDatumReal hr A A)
              (torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs A)| ≤
            Chigh m * torusSobolevNormAt 2 u t * torusSobolevNormAt (m : ℝ) u t * g := by
  refine ⟨fun m ↦ torusPairingConstant (m : ℝ), ?_⟩
  intro m _ u t A hr h2 hs hA
  exact ⟨torusSobolevNormAt ((m : ℝ) + 1) u t, torusSobolevNormAt_nonneg _ _ _,
    torusPairingBound_profile hr h2 hs (by ring) hA⟩

/-- The consumer-facing form: the `H^m` and `H²` data are supplied as reweights
of the top-order datum, which is what a solution carrier hands over. -/
theorem reweight_form_closes (m : ℕ) (hm : 3 ≤ m)
    (hr : (3 : ℝ) ≤ (m : ℝ) + 1) (h2 : (2 : ℝ) ≤ (m : ℝ) + 1) (hs : (m : ℝ) ≤ (m : ℝ) + 1)
    (A : PeriodicSobolev ((m : ℝ) + 1)) (G : PeriodicSobolev (m : ℝ))
    (E : PeriodicSobolev 2)
    (hG : IsPeriodicReweight ((m : ℝ) + 1) (m : ℝ) A G)
    (hE : IsPeriodicReweight ((m : ℝ) + 1) 2 A E) :
    |torusRealPairing (torusConvectionDatumReal hr A A) G| ≤
      torusPairingConstant (m : ℝ) * ‖E‖ * ‖G‖ * ‖A‖ := by
  have _ := hm
  exact torusPairingBound_of_reweights hr h2 hs (by ring) A G E hG hE

/-! ## 2. A nonzero witness: two conjugate lattice modes

The shear flow `u(x) = 2 e₂ cos(2πx₀)` carried by the mode pair `±(1,0,0)` in
the second component.  Copied from `research/T11/probes/high_order_closes.lean`
(lane 322), where the same witness exhibits the pressure drop. -/

/-- The lattice frequency `(1,0,0)`. -/
def shearFreq : PeriodicFrequency := fun j ↦ if j = 0 then 1 else 0

theorem shearFreq_ne_neg : shearFreq ≠ -shearFreq := by
  intro h
  have h0 := congrFun h 0
  simp [shearFreq] at h0

theorem shearFreq_component_one : shearFreq 1 = 0 := by simp [shearFreq]

/-- A genuinely nonzero solenoidal velocity datum. -/
def torusShearDatum (s : ℝ) : PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun i ↦ if i = 1 then
      lp.single 2 shearFreq (1 : ℂ) + lp.single 2 (-shearFreq) (1 : ℂ) else 0), ?_⟩
  intro i k
  by_cases hi : i = 1
  · subst hi
    change ((lp.single 2 shearFreq (1 : ℂ) +
        lp.single 2 (-shearFreq) (1 : ℂ) : PeriodicScalarData)) (-k) =
      star ((lp.single 2 shearFreq (1 : ℂ) +
        lp.single 2 (-shearFreq) (1 : ℂ) : PeriodicScalarData) k)
    by_cases h1 : k = shearFreq
    · subst h1
      simp [lp.single_apply, shearFreq_ne_neg, (shearFreq_ne_neg).symm]
    · by_cases h2 : k = -shearFreq
      · subst h2
        simp [lp.single_apply, shearFreq_ne_neg, (shearFreq_ne_neg).symm, neg_neg]
      · have h3 : -k ≠ shearFreq := fun h ↦ h2 (by rw [← h, neg_neg])
        have h4 : -k ≠ -shearFreq := fun h ↦ h1 (neg_injective h)
        simp [lp.single_apply, h1, h2, h3, h4]
  · simp [hi]

theorem torusShearDatum_apply (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    (torusShearDatum s).1 i k =
      if i = 1 then
        (if k = shearFreq then (1 : ℂ) else 0) + (if k = -shearFreq then (1 : ℂ) else 0)
      else 0 := by
  by_cases hi : i = 1
  · subst hi
    change ((lp.single 2 shearFreq (1 : ℂ) +
      lp.single 2 (-shearFreq) (1 : ℂ) : PeriodicScalarData)) k = _
    simp [lp.single_apply, Pi.single_apply]
  · simp [torusShearDatum, hi]

theorem torusShearDatum_ne_zero (s : ℝ) : torusShearDatum s ≠ 0 := by
  intro h
  have hv := congrArg (fun A : PeriodicSobolev s ↦ A.1 1 shearFreq) h
  rw [torusShearDatum_apply] at hv
  simp [shearFreq_ne_neg] at hv

theorem torusShearDatum_solenoidal (s : ℝ) :
    IsSolenoidalPeriodicDatum (torusShearDatum s) := by
  intro k
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [torusShearDatum_apply]
  by_cases hj : j = 1
  · subst hj
    by_cases h1 : k = shearFreq
    · subst h1
      simp [periodicDerivativeSymbol, shearFreq_component_one]
    · by_cases h2 : k = -shearFreq
      · subst h2
        simp [periodicDerivativeSymbol, shearFreq_component_one]
      · simp [h1, h2]
  · simp [hj]

/-- Reweighting preserves coefficient-side solenoidality. -/
theorem reweight_solenoidal {s t : ℝ} {A : PeriodicSobolev s} {B : PeriodicSobolev t}
    (hA : IsSolenoidalPeriodicDatum A) (hB : IsPeriodicReweight s t A B) :
    IsSolenoidalPeriodicDatum B := by
  intro k
  have h : ∑ j : Fin 3, periodicDerivativeSymbol j k * B.1 j k =
      ((periodicFrequencyWeight k ^ ((t - s) / 2) : ℝ) : ℂ) *
        ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hB j k, Complex.real_smul]
    ring
  rw [h, hA k, mul_zero]

/-- The order-descended shear datum is still solenoidal. -/
theorem shear_down_solenoidal {r s : ℝ} (hs : s ≤ r) :
    IsSolenoidalPeriodicDatum (torusOrderDown r s hs (torusShearDatum r)) :=
  reweight_solenoidal (torusShearDatum_solenoidal r) (torusOrderDown_reweight r s hs _)

/-- Every order-descended shear datum has strictly positive norm: the mode
`(1,0,0)` survives the descending multiplier. -/
theorem shear_down_norm_pos {r s : ℝ} (hs : s ≤ r) :
    0 < ‖torusOrderDown r s hs (torusShearDatum r)‖ := by
  have hco : (torusOrderDown r s hs (torusShearDatum r)).1 1 shearFreq =
      ((periodicFrequencyWeight shearFreq ^ ((s - r) / 2) : ℝ) : ℂ) * 1 := by
    rw [torusOrderDown_reweight r s hs _ 1 shearFreq, torusShearDatum_apply,
      Complex.real_smul]
    simp [shearFreq_ne_neg]
  have hpos : (0 : ℝ) < periodicFrequencyWeight shearFreq ^ ((s - r) / 2) := by
    apply Real.rpow_pos_of_pos
    unfold periodicFrequencyWeight
    positivity
  have hne : ‖(torusOrderDown r s hs (torusShearDatum r)).1 1 shearFreq‖ ≠ 0 := by
    rw [hco]
    simp only [mul_one, Complex.norm_real, Real.norm_eq_abs, ne_eq, abs_eq_zero]
    exact ne_of_gt hpos
  have h1 : ‖(torusOrderDown r s hs (torusShearDatum r)).1 1 shearFreq‖ ≤
      ‖(torusOrderDown r s hs (torusShearDatum r)).1 1‖ :=
    lp.norm_apply_le_norm (by norm_num) _ _
  have h2 : ‖(torusOrderDown r s hs (torusShearDatum r)).1 1‖ ≤
      ‖torusOrderDown r s hs (torusShearDatum r)‖ :=
    PiLp.norm_apply_le (torusOrderDown r s hs (torusShearDatum r)).1 1
  have h3 : (0 : ℝ) < ‖(torusOrderDown r s hs (torusShearDatum r)).1 1 shearFreq‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
  linarith

/-- **Non-vacuity.**  At the nonzero shear datum the estimate is a statement
about a strictly positive right-hand side, and the same bound holds for the
Leray-projected convection because the datum is solenoidal. -/
theorem pairing_bound_nonvacuous (m : ℕ) (hm : 3 ≤ m)
    (hr : (3 : ℝ) ≤ (m : ℝ) + 1) (h2 : (2 : ℝ) ≤ (m : ℝ) + 1) (hs : (m : ℝ) ≤ (m : ℝ) + 1) :
    torusShearDatum ((m : ℝ) + 1) ≠ 0 ∧
      0 < torusPairingConstant (m : ℝ) *
          ‖torusOrderDown ((m : ℝ) + 1) 2 h2 (torusShearDatum ((m : ℝ) + 1))‖ *
          ‖torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs (torusShearDatum ((m : ℝ) + 1))‖ *
          ‖torusShearDatum ((m : ℝ) + 1)‖ ∧
      |torusRealPairing
          (torusConvectionDatumReal hr (torusShearDatum ((m : ℝ) + 1))
            (torusShearDatum ((m : ℝ) + 1)))
          (torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs (torusShearDatum ((m : ℝ) + 1)))| ≤
        torusPairingConstant (m : ℝ) *
          ‖torusOrderDown ((m : ℝ) + 1) 2 h2 (torusShearDatum ((m : ℝ) + 1))‖ *
          ‖torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs (torusShearDatum ((m : ℝ) + 1))‖ *
          ‖torusShearDatum ((m : ℝ) + 1)‖ ∧
      |torusRealPairing
          (torusProjectedConvectionDatumReal hr (torusShearDatum ((m : ℝ) + 1))
            (torusShearDatum ((m : ℝ) + 1)))
          (torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs (torusShearDatum ((m : ℝ) + 1)))| ≤
        torusPairingConstant (m : ℝ) *
          ‖torusOrderDown ((m : ℝ) + 1) 2 h2 (torusShearDatum ((m : ℝ) + 1))‖ *
          ‖torusOrderDown ((m : ℝ) + 1) (m : ℝ) hs (torusShearDatum ((m : ℝ) + 1))‖ *
          ‖torusShearDatum ((m : ℝ) + 1)‖ := by
  have _ := hm
  have hA : (0 : ℝ) < ‖torusShearDatum ((m : ℝ) + 1)‖ :=
    norm_pos_iff.mpr (torusShearDatum_ne_zero _)
  refine ⟨torusShearDatum_ne_zero _, ?_,
    torusPairingBound hr h2 hs (by ring) _,
    torusProjectedPairingBound hr h2 hs (by ring) _ (shear_down_solenoidal hs)⟩
  have hc := torusPairingConstant_pos ((m : ℝ))
  have h2p := shear_down_norm_pos (r := (m : ℝ) + 1) (s := 2) h2
  have hmp := shear_down_norm_pos (r := (m : ℝ) + 1) (s := (m : ℝ)) hs
  positivity

end NSFormalization.Section3.T11.PairingBoundProbe
