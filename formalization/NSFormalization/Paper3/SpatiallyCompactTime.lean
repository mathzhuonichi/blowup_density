import NSFormalization.Paper3.WeightedFourierLp

/-! Time-continuity estimates for smooth families with one fixed spatial support.
No compact time support is assumed; this permits integrated difference quotients. -/
noncomputable section
namespace NSFormalization.Paper3
open Set Filter MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NavierStokesR3.HarmonicTestFunctionals
open scoped ContDiff ENNReal Topology

 theorem family_slice_compact {F : ℝ × Space → ℂ} {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (t : ℝ) :
    HasCompactSupport (fun x => F (t, x)) := HasCompactSupport.intro hK (hz t)

/-- Every ambient directional derivative keeps the same uniform spatial support. -/
theorem family_derivative_support {F : ℝ × Space → ℂ} {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (v : ℝ × Space) :
    ∀ t x, x ∉ K → fderiv ℝ F (t, x) v = 0 := by
  have hs : tsupport F ⊆ univ ×ˢ K := by
    apply closure_minimal _ (isClosed_univ.prod hK.isClosed)
    intro z hz'
    refine ⟨mem_univ _, ?_⟩
    by_contra hx
    exact hz' (hz z.1 z.2 hx)
  intro t x hx
  have hn : (t, x) ∉ tsupport F := fun h => hx (hs h).2
  rw [fderiv_of_notMem_tsupport ℝ hn]
  simp

 theorem family_spacetimePartial_support {F : ℝ × Space → ℂ} {K : Set Space} (hK : IsCompact K)
    (hz : ∀ t x, x ∉ K → F (t, x) = 0) (i : Fin 3) :
    ∀ t x, x ∉ K → spacetimePartial i F (t, x) = 0 :=
  family_derivative_support hK hz (0, coordinateVector i)

/-- Physical squared differences vary continuously in time under joint
continuity and one fixed compact spatial support. -/
theorem continuous_physical_sq_difference {F : ℝ × Space → ℂ} {K : Set Space}
    (hF : Continuous F) (hK : IsCompact K) (hz : ∀ t x, x ∉ K → F (t, x) = 0) (a : ℝ) :
    Continuous (fun t => ∫ x : Space, ‖F (t, x) - F (a, x)‖ ^ 2) := by
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hK
  · exact ((hF.sub (hF.comp (continuous_const.prodMk continuous_snd))).norm.pow 2).continuousOn
  · intro t x _ hx
    simp [hz t x hx, hz a x hx]

/-- Every integer-order Bessel energy of the actual temporal difference tends
to zero. The induction only uses physical compact parameter integrals and the
actual Fourier coordinate-derivative identity. -/
theorem tendsto_bessel_nat_difference (n : ℕ) {F : ℝ × Space → ℂ} {K : Set Space}
    (hF : ContDiff ℝ ∞ F) (hK : IsCompact K) (hz : ∀ t x, x ∉ K → F (t, x) = 0) (a : ℝ) :
    Tendsto (fun t => ∫ ξ : Space,
      besselIntegrand (n : ℝ) (𝓕 (fun x => F (t, x) - F (a, x))) ξ) (𝓝 a) (𝓝 0) := by
  induction n generalizing F with
  | zero =>
    have h := (continuous_physical_sq_difference hF.continuous hK hz a).continuousAt (x := a)
    have hp (t : ℝ) : (∫ ξ : Space, ‖𝓕 (fun x => F (t, x) - F (a, x)) ξ‖ ^ 2) =
        ∫ x : Space, ‖F (t, x) - F (a, x)‖ ^ 2 := by
      let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x) - F (a, x))
        ((hF.comp (contDiff_const.prodMk contDiff_id)).sub (hF.comp (contDiff_const.prodMk contDiff_id)))
        ((family_slice_compact hK hz t).sub (family_slice_compact hK hz a))
      exact SchwartzMap.integral_norm_sq_fourier φ
    simpa only [ContinuousAt, Nat.cast_zero, besselIntegrand, Real.rpow_zero, one_mul, hp,
      sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), integral_zero] using h
  | succ n ih =>
    have h₀ := ih hF hz
    have hd (i : Fin 3) := ih (spacetimePartial_smooth hF i) (family_spacetimePartial_support hK hz i)
    have hu := h₀.add (tendsto_finsetSum Finset.univ (fun i _ => hd i))
    have hupper (t : ℝ) : (∫ ξ : Space,
        besselIntegrand ((n + 1 : ℕ) : ℝ) (𝓕 (fun x => F (t, x) - F (a, x))) ξ) ≤
        (∫ ξ : Space, besselIntegrand (n : ℝ) (𝓕 (fun x => F (t, x) - F (a, x))) ξ) +
        ∑ i : Fin 3, ∫ ξ : Space, besselIntegrand (n : ℝ)
          (𝓕 (fun x => spacetimePartial i F (t, x) - spacetimePartial i F (a, x))) ξ := by
      let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport (fun x => F (t, x) - F (a, x))
        ((hF.comp (contDiff_const.prodMk contDiff_id)).sub (hF.comp (contDiff_const.prodMk contDiff_id)))
        ((family_slice_compact hK hz t).sub (family_slice_compact hK hz a))
      have heq (i : Fin 3) : (partialCLM i φ : Space → ℂ) =
          (fun x => spacetimePartial i F (t, x) - spacetimePartial i F (a, x)) := by
        funext x
        change NavierStokes.PeriodicIntegration.spatialPartial i
          (fun y => F (t, y) - F (a, y)) x = _
        have ht : DifferentiableAt ℝ (fun y : Space => F (t, y)) x :=
          ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
        have ha : DifferentiableAt ℝ (fun y : Space => F (a, y)) x :=
          ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
        unfold NavierStokes.PeriodicIntegration.spatialPartial
        change (fderiv ℝ ((fun y : Space => F (t, y)) - (fun y : Space => F (a, y))) x) (coordinateVector i) = _
        rw [fderiv_sub ht ha]
        simp only [ContinuousLinearMap.sub_apply, spacetimePartial_eq_slice hF,
          NavierStokes.PeriodicIntegration.spatialPartial]
      have hb := bessel_succ_energy_le (n : ℝ) φ
      simpa only [Nat.cast_add, Nat.cast_one, SchwartzMap.fourier_coe, heq, φ,
        NavierStokesR3.CompactSchwartz.coe_ofCompactSupport] using hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hu) (fun t => ?_) hupper
    exact integral_nonneg (fun ξ => by unfold besselIntegrand; positivity)

end NSFormalization.Paper3
