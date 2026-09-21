import NSFormalization.Source.RieszPotentialAssembly
import Mathlib.Topology.Order.DenselyOrdered

/-! # Pointwise epsilon optimization for the actual unnormalized Riesz potential -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace NSFormalization.RieszHedberg
open NSFormalization.RieszPotentialAssembly NSFormalization.CenteredMaximal
abbrev Space := NSFormalization.RieszPotentialAssembly.Space

private theorem balance_near {M L : ℝ} (hM : 0 < M) (hL : 0 < L) (a : ℝ) :
    M * ((L/M)^((2:ℝ)/3))^a = M^(1-2*a/3) * L^(2*a/3) := by
  rw [← Real.rpow_mul (div_nonneg hL.le hM.le), show (2:ℝ)/3*a=2*a/3 by ring,
    Real.div_rpow hL.le hM.le, Real.rpow_sub hM, Real.rpow_one]
  ring

private theorem balance_far {M L : ℝ} (hM : 0 < M) (hL : 0 < L) (a : ℝ) :
    L * ((L/M)^((2:ℝ)/3))^(a-3/2) = M^(1-2*a/3) * L^(2*a/3) := by
  rw [← Real.rpow_mul (div_nonneg hL.le hM.le), show (2:ℝ)/3*(a-3/2)=2*a/3-1 by ring,
    Real.div_rpow hL.le hM.le, div_eq_mul_inv, ← Real.rpow_neg hM.le,
    show -(2*a/3-1)=1-2*a/3 by ring]
  have he : L * L^(2*a/3-1) = L^(2*a/3) := by
    rw [Real.rpow_sub hL, Real.rpow_one]
    field_simp
  calc
    _ = M^(1-2*a/3) * (L * L^(2*a/3-1)) := by ring
    _ = _ := by rw [he]

/-- Scalar optimization includes both zero cases by positive regularization. -/
theorem scalar_hedberg {a C D M L P : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ R : ℝ, 0 < R → P ≤ C*M*R^a + D*L*R^(a-3/2)) :
    P ≤ (C+D)*M^(1-2*a/3)*L^(2*a/3) := by
  have he (ε : ℝ) (hε : 0 < ε) :
      P ≤ (C+D)*(M+ε)^(1-2*a/3)*(L+ε)^(2*a/3) := by
    let R : ℝ := ((L+ε)/(M+ε))^((2:ℝ)/3)
    have hR : 0 < R := Real.rpow_pos_of_pos (div_pos (by linarith) (by linarith)) _
    calc
      P ≤ C*M*R^a + D*L*R^(a-3/2) := hbound R hR
      _ ≤ C*(M+ε)*R^a + D*(L+ε)*R^(a-3/2) := by gcongr <;> linarith
      _ = _ := by
        have hn := balance_near (by linarith : 0 < M+ε) (by linarith : 0 < L+ε) a
        have hf := balance_far (by linarith : 0 < M+ε) (by linarith : 0 < L+ε) a
        change C*(M+ε)*R^a + D*(L+ε)*R^(a-3/2) = _
        change (M+ε)*R^a = _ at hn
        change (L+ε)*R^(a-3/2) = _ at hf
        calc
          _ = C*((M+ε)*R^a)+D*((L+ε)*R^(a-3/2)) := by ring
          _ = _ := by rw [hn,hf]; ring
  have hc : Continuous (fun ε : ℝ => (C+D)*(M+ε)^(1-2*a/3)*(L+ε)^(2*a/3)) :=
    (continuous_const.mul ((Real.continuous_rpow_const (by linarith : 0 ≤ 1-2*a/3)).comp
      (continuous_const.add continuous_id))).mul
      ((Real.continuous_rpow_const (by linarith : 0 ≤ 2*a/3)).comp (continuous_const.add continuous_id))
  have ht := hc.continuousAt.tendsto.mono_left (inf_le_left :
    nhdsWithin (0:ℝ) (Ioi 0) ≤ nhds 0)
  let : Filter.NeBot (nhdsWithin (0:ℝ) (Ioi 0)) := nhdsWithin_Ioi_neBot le_rfl
  have hb := ge_of_tendsto (x := nhdsWithin (0:ℝ) (Ioi 0)) ht (Filter.Eventually.mono self_mem_nhdsWithin (fun ε hε => he ε hε))
  simpa only [add_zero] using hb

/-- Hedberg's bound for the same actual potential at every finite-maximal point. -/
theorem realPotential_hedberg {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) (x : Space)
    (hx : centeredMaximal (normDensity g) x < ⊤) :
    realPotential a g x ≤ (4*Real.pi/a + Real.sqrt (4*Real.pi/(3-2*a))) *
      (centeredMaximal (normDensity g) x).toReal^(1-2*a/3) * (eLpNorm g 2 volume).toReal^(2*a/3) := by
  apply scalar_hedberg ha ha3 (by positivity) (Real.sqrt_nonneg _) ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  intro R hR
  exact realPotential_bound ha ha3 hR hg h2 x hx

theorem ae_realPotential_hedberg {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    {g : Space → ℂ} (hg : Measurable g) (h2 : MemLp g 2 volume) :
    ∀ᵐ x : Space ∂volume, realPotential a g x ≤ (4*Real.pi/a + Real.sqrt (4*Real.pi/(3-2*a))) *
      (centeredMaximal (normDensity g) x).toReal^(1-2*a/3) * (eLpNorm g 2 volume).toReal^(2*a/3) := by
  filter_upwards [centeredMaximal_ae_lt_top hg.norm (fun _ => norm_nonneg _) h2.norm] with x hx
  exact realPotential_hedberg ha ha3 hg h2 x hx

end NSFormalization.RieszHedberg
