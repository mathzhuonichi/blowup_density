import Bindings.DatumLemmas
import Bindings.MainThresholds

/-!
# Corollary 4.5 for compactly supported forces

This file proves the `Y = forceClassCompact` instances of the `density` and
`zeroIff` fields of `research/R45/Spec.lean`.

The density proof is the two-case proof used for `forceClassR`: a target force
which already breaks down is its own approximant; otherwise the R42 insertion
record supplies an exact-lifespan perturbation.  Its compact difference from
the compact target is compact, so the inserted force stays in `F_c`.

For the only-if direction at zero datum, lane 232's explicit excluded ball in
`F_R` is used at the centre zero.  Compact forces lie in `F_R`, so a breakdown
force supplied by compact relative density would lie in that excluded ball.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set Filter
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal Topology

/-- If `g` and the difference `f - g` are compactly supported smooth forces,
then so is `f`.  This is the form consumed by the insertion argument. -/
theorem memForceCompact_add_memForceCompact {f g : SpaceTimeField}
    (hg : MemForceCompact g)
    (hd : MemForceCompact (fun z => f z - g z)) : MemForceCompact f := by
  have hsum := datumLemmas.memForceCompact_add
    (fun z => f z - g z) g hd hg
  have heq : (fun z => f z - g z) + g = f := by
    funext z
    exact sub_add_cancel (f z) (g z)
  rw [heq] at hsum
  exact hsum

/-- Every compactly supported smooth force belongs to the ambient regular
force class `F_R`. -/
theorem memForceR_of_memForceCompact {f : SpaceTimeField}
    (hf : MemForceCompact f) : MemForceR f :=
  datumLemmas.memForceCompact_memForceR f hf

/-- The `Y = forceClassCompact` specialization of
`RClassesAPI.density`, with exactly the field's binder order. -/
theorem density_compact :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassR →
          s < criticalOrder q.toReal →
            RelativelyDense q s forceClassCompact
              (breakdownSetIn forceClassCompact ν a T) := by
  intro ν hν T hT q hq s a ha hs g hg r hr
  by_cases hLife : maximalLifespanR ν a g ≤ ENNReal.ofReal T
  · refine ⟨g, ⟨hg, hLife⟩, ?_⟩
    simpa only [sub_self, density_forceSobolevENorm_zero] using hr
  · have hlong := lt_of_not_ge hLife
    obtain ⟨P, L, hLa, hLg, hLT⟩ :=
      insertionLifespanV2_of_data ν hν T hT a ha g
        (memForceR_of_memForceCompact hg) hlong
    have hs' : s < L.family.scaling.thresholds.exponent q.toReal 0 := by
      simpa only [L.family.scaling.thresholds.formula, sub_zero, criticalOrder] using hs
    have hsmall := (insertionFromData_forceConvergence L hLg q hq s hs').eventually
      (gt_mem_nhds hr)
    have hwindow : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ε ∈ Ioc (0 : ℝ) L.family.ε₀ :=
      Ioc_mem_nhdsGT L.family.eps_pos
    obtain ⟨ε, hε, hdist⟩ := (hwindow.and hsmall).exists
    refine ⟨L.family.force ε, ⟨?_, ?_⟩, hdist⟩
    · exact memForceCompact_add_memForceCompact
        (f := L.family.force ε) (g := L.family.g) (hLg.symm ▸ hg)
        (L.family.forceDifference_compact ε hε)
    · exact (insertionFromData_lifespan L hLa hLT ε hε).le

/-- The `Y = forceClassCompact` specialization of
`RClassesAPI.zeroIff`, with exactly the field's binder order. -/
theorem zeroIff_compact :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        RelativelyDense q s forceClassCompact
            (breakdownSetIn forceClassCompact ν (fun _ => 0) T) ↔
          s < criticalOrder q.toReal := by
  intro ν hν T hT q hq s
  constructor
  · intro hdense
    by_contra hsub
    have hge : criticalOrder q.toReal ≤ s := le_of_not_gt hsub
    have hzero : (0 : SpaceTimeField) ∈ forceClassCompact := by
      refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
      simp
    rcases hq with rfl | rfl
    · have hthreshold :
          R41.rMainThresholds.exponent 1 0 ≤ s := by
        simpa [R41.rMainThresholds, NSFormalization.Paper3.forceExponent,
          criticalOrder] using hge
      obtain ⟨ρ, hρ, hbound⟩ :=
        R41.nonDensityZero_of_q R41.rMainThresholds 1 (Or.inl rfl)
          ν T hν hT s hthreshold
      rw [mainThresholds_forceSobolevENorm_eq] at hbound
      obtain ⟨f, hf, hdist⟩ := hdense 0 hzero (ENNReal.ofReal ρ)
        (ENNReal.ofReal_pos.mpr hρ)
      have hfR : f ∈ breakdownSetRZero ν T :=
        ⟨memForceR_of_memForceCompact hf.1, hf.2⟩
      have hfR' : f ∈ R41.breakdownSetRZero ν T := by
        simpa only [R41.breakdownSetRZero, breakdownSetRZero,
          mainThresholds_breakdownSetR_eq] using hfR
      have hlower : ENNReal.ofReal ρ ≤ forceSobolevENorm 1 s f := by
        simpa using hbound f hfR'
      exact (not_lt_of_ge hlower) (by simpa only [sub_zero] using hdist)
    · have hthreshold :
          R41.rMainThresholds.exponent 2 0 ≤ s := by
        simpa [R41.rMainThresholds, NSFormalization.Paper3.forceExponent,
          criticalOrder] using hge
      obtain ⟨ρ, hρ, hbound⟩ :=
        R41.nonDensityZero_of_q R41.rMainThresholds 2 (Or.inr rfl)
          ν T hν hT s hthreshold
      rw [mainThresholds_forceSobolevENorm_eq] at hbound
      obtain ⟨f, hf, hdist⟩ := hdense 0 hzero (ENNReal.ofReal ρ)
        (ENNReal.ofReal_pos.mpr hρ)
      have hfR : f ∈ breakdownSetRZero ν T :=
        ⟨memForceR_of_memForceCompact hf.1, hf.2⟩
      have hfR' : f ∈ R41.breakdownSetRZero ν T := by
        simpa only [R41.breakdownSetRZero, breakdownSetRZero,
          mainThresholds_breakdownSetR_eq] using hfR
      have hlower : ENNReal.ofReal ρ ≤ forceSobolevENorm 2 s f := by
        simpa using hbound f hfR'
      exact (not_lt_of_ge hlower) (by simpa only [sub_zero] using hdist)
  · intro hs
    exact density_compact ν hν T hT q hq s (fun _ => 0)
      A04.zero_mem_initialClassR hs

end BlowupDensity.Bindings
