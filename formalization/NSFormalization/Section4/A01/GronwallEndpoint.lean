import NSFormalization.Section4.A01.AprioriRows
import NSFormalization.Section4.D01.LerayLowering

/-! Full-horizon Grönwall with the endpoint cap. No value or limit of the
classical solution at `T` is asserted. The cylinder bound remains a hypothesis. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerCylinderSobolev
open scoped ENNReal

variable {ν T R : ℝ} {a : SpatialField} {f : SpaceTimeField} {q : ℕ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    (hT : 0 < T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (hslice : ∀ t : Icc (0 : ℝ) T,
      (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hR : ‖u‖ ≤ R)

include hν ha hf hpath hT hu hU hq hslice hR

/-- Apply the existing half-open Grönwall theorem directly with horizon `T₀ = T`.
The closed cap restricts to `Ico`; its constant does not depend on an interior horizon. -/
theorem highOrder_bddAbove_of_kbnd_Ico_full {m : ℕ} (hm : 3 ≤ m) :
    ∀ t ∈ Ico (0 : ℝ) T,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (A04.forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (A04.Cgron m ν * (256 * R ^ 2 * T)) := by
  apply highOrder_bddAbove_of_kbnd hν ha hf (memL1Hm_of_memForceR hf)
    w hpath hm hT le_rfl
  intro t ht
  exact kbnd_of_sup_bound_Icc_endpoint u U hu hU hq w.velocity hslice hR
    (continuousOn_sobolevNormAt_velocity w 2) t ⟨ht.1, ht.2.le⟩

/-- Every high order has a finite real bound on the same full half-open horizon. -/
theorem highOrder_bddAbove_all_orders_Ico_full :
    ∀ m : ℕ, 3 ≤ m →
      BddAbove (range (fun t : Ico (0 : ℝ) T => sobolevNormAt (m : ℝ) w.velocity t)) := by
  intro m hm
  refine ⟨(sobolevNormAt (m : ℝ) w.velocity 0 +
    (A04.forceSobolevENormL1 (m : ℝ) f).toReal) *
      Real.exp (A04.Cgron m ν * (256 * R ^ 2 * T)), ?_⟩
  rintro y ⟨t, rfl⟩
  exact highOrder_bddAbove_of_kbnd_Ico_full hν ha hf w hpath hT u U hu hU hq hslice hR hm t t.property

/-- The finite `ENNReal` velocity-bound input of A04's `restartBeyond`.
Lower order three using the continuous linear datum lowering map. Its fixed operator
norm is harmless for restart; no finiteness of a `.toReal` is assumed implicitly. -/
theorem hOne_uniform_Ico_full :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ t ∈ Ico (0 : ℝ) T,
      sobolevENorm 1 (fun x : Space => w.velocity (t, x)) ≤ K := by
  let B := (sobolevNormAt (3 : ℝ) w.velocity 0 + (A04.forceSobolevENormL1 (3 : ℝ) f).toReal)
    * Real.exp (A04.Cgron 3 ν * (256 * R ^ 2 * T))
  let L := lowerVectorL 3 1 (by norm_num)
  refine ⟨ENNReal.ofReal (‖L‖ * B), ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  obtain ⟨G, _, hG⟩ := w.sobolev 3
  have hd := hG t ht
  have hl := Leray.isSobolevDatum_lower (by norm_num : (1 : ℝ) ≤ 3) hd
  rw [sobolevENorm_eq hl]
  have hb : ‖G t‖ ≤ B := by
    have hh := highOrder_bddAbove_of_kbnd_Ico_full hν ha hf w hpath hT
      u U hu hU hq hslice hR (m := 3) (by omega) t ht
    change (sobolevENorm (3 : ℝ) (fun x => w.velocity (t, x))).toReal ≤ B at hh
    have he := sobolevENorm_eq hd
    norm_num only [Nat.cast_ofNat] at he
    rw [he] at hh
    simpa using hh
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((L.le_opNorm (G t)).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg L)))

end NSFormalization.Section4.A01
