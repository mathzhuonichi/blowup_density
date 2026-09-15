import NSFormalization.Section4.C01.PressureJetPath
import Euler.OrdinaryWordTime

/-!
# Section 4 · C01 row E4 — the time derivative of the `L²` energy

The `L²` energy `s ↦ ‖u(s,·)‖²_{L²}` of a classical solution
`w : ClassicalSolutionR ν a f T` is differentiable at every interior time, with derivative
`2⟪u(t,·), ∂ₜu(t,·)⟫_{L²}`.  This is row **E4** of `research/C01/ENERGY_SPLIT.md`; it
discharges the last hypothesis of `energyIdentity_classical`
(`Section4/C01/MomentumCarrierB.lean`).

The proof feeds the jet-continuity facts of lanes 143/146/148 into the vendor's
`EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` (`Euler/OrdinaryWordTime.lean:87`), which
lives on a *closed* interval `Icc 0 T'`.  Because the `∂ₜu` `L²` jets are only continuous on a
window `[c,S] ⊂ (0,T)` bounded away from the left endpoint, we translate the window by `+c`:
the velocity/derivative paths are re-indexed over `Icc 0 (S-c)` through the continuous shift
`σ r = r + c`, and the pointwise time derivative is transported by the `+c` chain rule and a
`projIcc` congruence.

* `energyDerivative_hasDerivAt` — the exact statement `energyIdentity_classical` consumes.
* `energyIdentity_classical_unconditional` — item 4 fed into `energyIdentity_classical`: the
  energy of a classical solution has, at every interior time, the derivative asserted by the
  raw-integral form of the ordinary energy identity (`02-preliminaries.tex:136-139`, invoked at
  `04-whole-space.tex:117`; eq:RL2 at `:118-119` is its `L²`-bound corollary).
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-- At `s = 0` the ordinary word energy collapses to the `L²` norm squared (there is no
`wordEnergy_zero` simp lemma in the vendor; the single empty word `Fin 0 → Fin 3` gives it). -/
theorem wordEnergy_zero (A : SmoothL2Field Space) :
    wordEnergy 0 A = ‖A.toLp‖ ^ 2 := by
  simp [wordEnergy, wordField_zero]

/-- The `s = 0` pairing sum produced by `wordEnergy_hasDerivWithinAt` collapses to a single
`L²` inner product. -/
theorem wordInner_sum_zero (X Y : SmoothL2Field Space) :
    (∑ n ∈ Finset.range 1, ∑ w : Fin n → Fin 3,
      ⟪(wordField X w).toLp, (wordField Y w).toLp⟫) = ⟪X.toLp, Y.toLp⟫ := by
  simp [wordField_zero]

/-- **Item 2, the pointwise `hd` seed.**  The velocity slice `s ↦ u(s,x)` has, at every
interior time, the derivative `∂ₜu(s,x)`.  Re-proved unconditionally from `velocity_smooth`
(the only prior copy is inline in `A04.timeDeriv_isSobolevDatum`, guarded by `2 ≤ m` and a
`ContDiffOn` datum-path hypothesis neither of which `ClassicalSolutionR` supplies). -/
theorem velocity_hasDerivAt_time (w : ClassicalSolutionR ν a f T)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) (x : Space) :
    HasDerivAt (fun ρ => w.velocity (ρ, x)) (temporalDerivative w.velocity s x) s := by
  have hmap : ContDiffOn ℝ ∞ (fun r : ℝ => ((r, x) : ℝ × Space)) (Ico (0 : ℝ) T) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have hsub : (Ico (0 : ℝ) T) ⊆
      (fun r : ℝ => ((r, x) : ℝ × Space)) ⁻¹' (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    fun r hr => ⟨hr, mem_univ x⟩
  have hcd : ContDiffOn ℝ ∞ (fun r => w.velocity (r, x)) (Ico (0 : ℝ) T) :=
    w.velocity_smooth.comp hmap hsub
  exact ((hcd.differentiableOn (by simp) s (Ioo_subset_Ico_self hs)).differentiableAt
    (Ico_mem_nhds hs.1 hs.2)).hasDerivAt

/-- **Row E4.**  On a window `[c,S] ⊂ (0,T)` (`0 < c ≤ S < T`) of a classical solution `w`
with real admissible force `hf`, the `L²` energy `ρ ↦ ‖u(·,·)‖²` (re-indexed by the shift
`ρ ↦ ρ + c`, clamped to `[0,S]`) is differentiable at every interior `r ∈ Ioo 0 (S-c)`, with
derivative `2⟪u(r+c,·), ∂ₜu(r+c,·)⟫_{L²}`.

This is the exact fact `energyIdentity_classical` (`MomentumCarrierB.lean`) takes as its `hd`
hypothesis at the interior time `r + c`.  Assembled from the vendor's
`wordEnergy_hasDerivWithinAt` at `s = 0`, with the velocity jets (`velocityField_jetLp_continuous`)
and the `∂ₜu` jets (`temporalSlicePath_jetLp_continuous`) as `hA`/`hB` and the `+c` chain rule
as `hd`. -/
theorem energyDerivative_hasDerivAt
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    (hc : 0 < c) (hcS : c ≤ S) (hST : S < T)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (S - c)) :
    HasDerivAt
      (fun ρ : ℝ =>
        ‖(velocityField w hST
            ⟨(projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).1 + c,
              ⟨by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.1; linarith,
               by have h := (projIcc (0 : ℝ) (S - c) (sub_nonneg.mpr hcS) ρ).2.2;
                  linarith⟩⟩).toLp‖ ^ 2)
      (2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩)))).toLp,
            (temporalSliceField w hf
                (mem_Ioo_of_mem_Icc hc hST (show r + c ∈ Icc c S from
                  ⟨by linarith [hr.1], by linarith [hr.2]⟩))).toLp⟫)
      r := by
  have hT' : (0 : ℝ) ≤ S - c := sub_nonneg.mpr hcS
  -- the velocity-index shift `Icc 0 (S-c) → Icc 0 S`
  let ιvel : Icc (0 : ℝ) (S - c) → Icc (0 : ℝ) S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hιvel : Continuous ιvel :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  -- the derivative-index shift `Icc 0 (S-c) → Icc c S`
  let σ : Icc (0 : ℝ) (S - c) → Icc c S := fun ρ =>
    ⟨ρ.1 + c, ⟨by have := ρ.2.1; linarith, by have := ρ.2.2; linarith⟩⟩
  have hσ : Continuous σ :=
    (continuous_subtype_val.add continuous_const).subtype_mk _
  -- the velocity path and its derivative path over the shifted window
  let A : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ => velocityField w hST (ιvel ρ)
  let B : Icc (0 : ℝ) (S - c) → SmoothL2Field Space := fun ρ =>
    temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST (σ ρ).2)
  have hA : ∀ n, Continuous (fun ρ => (A ρ).jetLp n) :=
    fun n => (velocityField_jetLp_continuous w hST n).comp hιvel
  have hB : ∀ n, Continuous (fun ρ => (B ρ).jetLp n) :=
    fun n => (temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ
  -- the pointwise `hd` clause: `∂ₜ (velocity at ρ+c)` via the `+c` chain rule
  have hd : ∀ t (ht : t ∈ Ioo 0 (S - c)) x,
      HasDerivAt (fun ρ => (A (projIcc 0 (S - c) hT' ρ)).field x)
        ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t := by
    intro t ht x
    have htc : t + c ∈ Ioo (0 : ℝ) T :=
      ⟨by linarith [ht.1, hc], by linarith [ht.2, hST]⟩
    have hbase := velocity_hasDerivAt_time w htc x
    have hshift : HasDerivAt (fun ρ : ℝ => ρ + c) 1 t := (hasDerivAt_id t).add_const c
    have hcomp := hbase.scomp t hshift
    rw [one_smul] at hcomp
    have h₁ : (fun ρ => w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x))
        =ᶠ[𝓝 t] ((fun ρ : ℝ => w.velocity (ρ, x)) ∘ (fun ρ : ℝ => ρ + c)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun ρ hρ => by
        show w.velocity ((projIcc (0 : ℝ) (S - c) hT' ρ).1 + c, x) = w.velocity (ρ + c, x)
        rw [projIcc_of_mem hT' (Ioo_subset_Icc_self hρ)])
    exact hcomp.congr_of_eventuallyEq h₁
  -- apply the vendor derivative machinery at `s = 0`
  have hderiv := wordEnergy_hasDerivWithinAt (S - c) hT' A B hA hB hd 0 ⟨r, hr.1.le, hr.2.le⟩
  simp only [Nat.zero_add, wordEnergy_zero, wordInner_sum_zero] at hderiv
  exact hderiv.hasDerivAt (Icc_mem_nhds hr.1 hr.2)

/-- **Row `energyIdentity` (the ordinary energy identity, `02-preliminaries.tex:136-139`, cf.
`04-whole-space.tex:117`), the raw-integral form.**  For a classical solution `w`
with real admissible force `hf`, at every interior time `t ∈ Ioo 0 T` the `L²` energy
`s ↦ ‖u(s,·)‖²_{L²}` — presented on the closed window `[0,(t+T)/2]` via `projIcc`, which is the
identity near `t` — is differentiable at `t`, with the ordinary energy identity's asserted
derivative

  `d/dt ‖u‖²_{L²} = −2ν · ∫ ∑ᵢ ‖∂ᵢu(t,·)‖² + 2 · ∫ ⟪u(t,·), f(t,·)⟫`.

This feeds row E4 (`energyDerivative_hasDerivAt`, with the window `c = t/2`, `S = (t+T)/2`, so
`r + c = t`) into `energyIdentity_classical` and undoes the window translation by the `−c`
chain rule.  The derivative value is in the **raw-integral** vocabulary of
`energyIdentity_classical` (`∫ ∑ᵢ ‖fderiv u · (axis i)‖²`, `∫ ⟪u, f⟫` on the carrier's
`.field`s).  The one-line bridge remaining to `research/C01/Spec.lean`'s `energyIdentity` is
the `gradientSq`/`pairing` vocabulary step (`PiLp.norm_sq_eq_of_L2`, cf.
`research/C01/REVIEW_E3E4.md`). -/
theorem energyIdentity_classical_unconditional
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s : ℝ =>
        ‖(velocityField w (show (t + T) / 2 < T by linarith [ht.2])
            (projIcc (0 : ℝ) ((t + T) / 2) (by linarith [ht.1, ht.2]) s)).toLp‖ ^ 2)
      (-2 * ν * (∫ x, ∑ i : Fin 3,
            ‖fderiv ℝ (velocitySliceField w (Ioo_subset_Ico_self ht)).field x (axis i)‖ ^ 2)
          + 2 * (∫ x, ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).field x,
                       (forceSliceField hf (le_of_lt ht.1)).field x⟫))
      t := by
  have hc : 0 < t / 2 := by linarith [ht.1]
  have hcS : t / 2 ≤ (t + T) / 2 := by linarith [ht.2]
  have hST : (t + T) / 2 < T := by linarith [ht.2]
  have hSnn : (0 : ℝ) ≤ (t + T) / 2 := by linarith [ht.1, ht.2]
  have hr : t - t / 2 ∈ Ioo (0 : ℝ) ((t + T) / 2 - t / 2) := by
    constructor <;> [linarith [ht.1]; linarith [ht.2]]
  have hg := energyDerivative_hasDerivAt w hf hc hcS hST hr
  have harith : (t - t / 2) + t / 2 = t := by ring
  -- transport the interior point `t - t/2 ↦ t` by the `−(t/2)` chain rule
  have hunshift : HasDerivAt (fun s : ℝ => s - t / 2) 1 t := (hasDerivAt_id t).sub_const (t / 2)
  have hcomp := hg.comp t hunshift
  rw [mul_one] at hcomp
  -- rewrite the derivative value's slice times `(t - t/2) + t/2 ↦ t`
  have hvel : velocitySliceField w (Ioo_subset_Ico_self
        (mem_Ioo_of_mem_Icc hc hST (show (t - t / 2) + t / 2 ∈ Icc (t / 2) ((t + T) / 2) from
          ⟨by linarith [hr.1], by linarith [hr.2]⟩)))
      = velocitySliceField w (Ioo_subset_Ico_self ht) :=
    field_ext (by simp only [velocitySliceField_field, harith])
  have htmp : temporalSliceField w hf
        (mem_Ioo_of_mem_Icc hc hST (show (t - t / 2) + t / 2 ∈ Icc (t / 2) ((t + T) / 2) from
          ⟨by linarith [hr.1], by linarith [hr.2]⟩))
      = temporalSliceField w hf ht :=
    field_ext (by simp only [temporalSliceField_field, harith])
  rw [hvel, htmp] at hcomp
  -- discharge the energy identity at the interior time `t`
  have hId := energyIdentity_classical w hf ht
      (d := 2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self ht)).toLp,
                 (temporalSliceField w hf ht).toLp⟫) rfl
  rw [hId] at hcomp
  -- the clamped energy `‖u(projIcc s,·)‖²` agrees with the shifted energy near `t`
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds
      (show t ∈ Ioo (t / 2) ((t + T) / 2) from ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    with s hs
  have hsS : s ∈ Icc (0 : ℝ) ((t + T) / 2) := ⟨by linarith [hs.1, ht.1], hs.2.le⟩
  have hsSc : s - t / 2 ∈ Icc (0 : ℝ) ((t + T) / 2 - t / 2) :=
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  simp only [Function.comp]
  refine congrArg (fun z : SmoothL2Field Space => ‖z.toLp‖ ^ 2) ?_
  refine congrArg (velocityField w hST) (Subtype.ext ?_)
  rw [projIcc_of_mem hSnn hsS, projIcc_of_mem (sub_nonneg.mpr hcS) hsSc]
  show s = (s - t / 2) + t / 2
  ring

end NSFormalization.Section4.C01
