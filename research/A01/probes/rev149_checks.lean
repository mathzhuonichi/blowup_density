import NSFormalization.Section4.A01.AprioriRows

/-!
Reviewer probes for lane 149 (`Section4/A01/AprioriRows.lean`).  Read-only checks; nothing here
is part of the lane.  Each section is referenced from `research/A01/REVIEW_APRIORI_ROWS.md`.
-/

noncomputable section

namespace Rev149

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04 (sobolevNormAt Cgron MemL1Hm HasSmoothSobolevPath)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NavierStokes.ProblemStatement (Space)
open EulerCylinderSobolevSpace
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ### (1) The widened bound's constant is *literally* `highOrder_bddAbove_of_kbnd`'s.
The statement below is written with `GronwallInstance`'s own names (`forceSobolevENormL1`,
`Cgron`, opened from `A04`), and is discharged by the lane theorem verbatim. -/
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ Kbnd : ℝ} (hT₀ : 0 ≤ T₀) (hT₀T : T₀ < T)
    (hkbnd : ∀ t ∈ Ico (0 : ℝ) T,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Icc (0 : ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (NSFormalization.Section4.A04.forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (Cgron m ν * Kbnd) :=
  -- N1 applied: `highOrder_bddAbove_of_kbnd_Icc` now takes an intermediate horizon `T₁`;
  -- here `T₁ := T` (so `hT₀T : T₀ < T` and `le_rfl : T ≤ T`), recovering the full-horizon form.
  highOrder_bddAbove_of_kbnd_Icc hν ha hf hf1 w hpath hm hT₀ hT₀T le_rfl hkbnd

/-! ### (2) What the tree's own cap supplies for the widened theorem's `hkbnd` on `Ico 0 T`:
`kbnd_of_sup_bound` at horizon `T₀ := T`, i.e. `Kbnd = 256·R²·T` (not `256·R²·T₀`). -/
example {q : ℕ} {T : ℝ}
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, EulerMeanOrdinaryLift.ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (v : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) T, (fun x : Space => v (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R)
    (hcont : ContinuousOn (fun s => sobolevNormAt (2 : ℝ) v s) (Ico (0 : ℝ) T))
    (hT : 0 < T) :
    ∀ t ∈ Ico (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, sobolevNormAt (2 : ℝ) v s ^ 2) ≤ 256 * R ^ 2 * T :=
  kbnd_of_sup_bound u U hu hU hq v hslice hR hcont hT le_rfl

/-! ### (3) `hword_jet` at `n = 0` is about the *order-zero coordinate* `value 1 u`, not `‖u‖`:
the word at the empty index is definitionally `value`. -/
example {q : ℕ} (u : SobolevSpace 1 q) :
    word 1 u (Nat.zero_le q) Fin.elim0 = value 1 u := rfl

/-! ### (4) The assembled converse fires on a genuine instance (zero cylinder field, zero slice):
`hword_jet` is satisfiable and the conclusion is a real inequality `0 ≤ jetSobolevConst (q+1) * 0`.
(The lane's `axioms_apriori_rows.lean` exercises only the two components, not the assembly.) -/
example (q : ℕ) :
    ‖(0 : SobolevSpace 1 (q + 1))‖
      ≤ jetSobolevConst (q + 1)
        * (sobolevENorm ((q + 1 : ℕ) : ℝ) (fun _ : Space => (0 : Space))).toReal := by
  refine sobolevSpace_norm_le_sobolevENorm (0 : SobolevSpace 1 (q + 1)) contDiff_const
    (sobolevENorm_ne_top_of_contDiff_memLp contDiff_const
      (fun k => by rw [show iteratedFDeriv ℝ k (fun _ : Space => (0 : Space)) = 0 from
        iteratedFDeriv_fun_zero]; exact MemLp.zero) _) (fun n hn w => ?_)
  rw [show word 1 (0 : SobolevSpace 1 (q + 1)) hn w = 0 from rfl, norm_zero]
  exact ENNReal.toReal_nonneg

/-! ### (5) `hfin` is load-bearing: at `sobolevENorm (q+1) z = ⊤` the right-hand side of the
reverse embedding collapses to `0`, so the `hfin`-free statement would force every smooth field
without an order-`(q+1)` datum to have vanishing order-`n` jet `L²` norm. -/
example (q : ℕ) {z : Space → Space} (htop : sobolevENorm ((q + 1 : ℕ) : ℝ) z = ⊤) :
    jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal = 0 := by
  rw [htop]; simp

example (q n : ℕ) {z : Space → Space} (htop : sobolevENorm ((q + 1 : ℕ) : ℝ) z = ⊤)
    (hbad : (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
      ≤ jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal) :
    (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal = 0 := by
  have h0 : jetSobolevConst (q + 1) * (sobolevENorm ((q + 1 : ℕ) : ℝ) z).toReal = 0 := by
    rw [htop]; simp
  have := hbad.trans_eq h0
  exact le_antisymm this ENNReal.toReal_nonneg

/-! ### (6) The three spatial directions of a cylinder word are `Fin.succ`; direction `0` is the
angular one (`EulerProof.lean:6529/6535`).  The descent `exists_descend` is only ever applied to
`Fin.cons j.succ w`, so the words `hword_jet` quantifies over include angular words that no
property of the spatial slice `z` can control — discharging `hword_jet` therefore needs the
angle invariance `hu` of row (iv). -/
example : EulerCylinderSobolev.standardDirection 0 = (0, 1) := by simp

example (i : Fin 3) :
    EulerCylinderSobolev.standardDirection i.succ = (EuclideanSpace.single i (1:ℝ), 0) := by simp

/-! ### (7) The converse's conclusion could equivalently be phrased on the a.e. representative
`⇑(U t)` (the shape the residual-row audit asked for): the datum norm is an a.e. invariant, so
routing the *proof* through the smooth slice costs nothing in the *statement*. -/
theorem sobolevENorm_congr_ae {s : ℝ} {z z' : Space → Space} (h : z =ᵐ[volume] z') :
    sobolevENorm s z = sobolevENorm s z' := by
  refine le_antisymm ?_ ?_
  · simp only [sobolevENorm]
    exact le_iInf fun A => sobolevENorm_le_of_isSobolevDatum
      (NSFormalization.Section4.A01.IsSobolevDatum.congr_field A.2 h.symm)
  · simp only [sobolevENorm]
    exact le_iInf fun A => sobolevENorm_le_of_isSobolevDatum
      (NSFormalization.Section4.A01.IsSobolevDatum.congr_field A.2 h)

end Rev149
