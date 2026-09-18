import NSFormalization.Section3.T17.Transport
import NSFormalization.Paper1.CorrectionVectorNorms
import NSFormalization.Source.PhysicalRemoval

/-! # T17 (`lem:correction`), unit U7: smoothness, periodicity and support of
the periodized correction force

The three canonical `CorrectionAPI` fields `force_smooth` / `force_periodic` /
`force_support` (`research/T17/Spec.lean:836-852`,
`Section3/T17/Correction.lean:161-173`) are proved here at the concrete
`correctionData` of unit U2, i.e. for the periodized correction
`latticeLift (physicalCorrection v x₀ T θ η ε)`.

## Route

`Transport.force_eq` writes `correctionForce ν v (correctionData …) ε` as
`latticeLift G` with `G = Source.correctionForce ν v (physicalCorrection …)`
the Section 4 single Euclidean copy.  Then:

* **smoothness** — `Paper1.CorrectionForceNorms.physicalForce_smooth` gives
  `ContDiff ℝ ∞ G`, and `G` has spatial slice support in `ball x₀ (ε·θR)`
  (`Source.LocalizedInsertion.correctionForce_support` composed with
  `Source.PhysicalRemoval.physical_support`), so `T16.latticeLift_smooth`
  applies;
* **periodicity** — `Transport.correctionForce_periodic`, itself
  `T16.latticeLift_periodic` after `force_eq`;
* **support** — the time projection is `T16.latticeLift_timeSupport`.  The
  spatial projection needs the *open* ball `ball x₀ (ε·θR)` of the manuscript,
  while `T16.latticeLift_sliceSupport` only gives `periodicSet (ball x₀ r)` for
  a strictly larger `r`, and is a statement about one spatial slice rather than
  about the space-time `tsupport`.  Section 0 below therefore proves the
  space-time companion `latticeLift_spaceSupport` of
  `T16.latticeLift_sliceSupport_closed`: it runs the same local-finiteness
  argument (`periodize_locally_eq_sum`, whose neighbourhood is already a
  *space-time* neighbourhood) at the space-time point.  Applied with the compact
  set `C = Prod.snd '' tsupport G`, which is contained in the open ball because
  `G` has compact support there, it yields `periodicSet C ⊆ periodicSet
  (ball x₀ (ε·θR))` with no closed-ball weakening.

## The `hv` premise

`physicalForce_smooth` (through `Paper1.physicalCorrection_smooth` and
`Source.LocalizedInsertion.correctionForce_smooth`) needs a **global**
`ContDiff ℝ ∞ v`; `force_eq` needs `v` smooth on the chart cylinder.  Both are
supplied by the single explicit premise `hv : ContDiff ℝ ∞ v`, exactly as in
units U3–U6.  This is the open G1 issue of `research/T17/SPEC_ISSUES.md`: the
canonical record carries only `reference_periodic`, so the assembly unit U12
must either add `reference_smooth` or truncate the reference.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set Filter Metric
open NavierStokes NavierStokes.ProblemStatement
open NavierStokes.PeriodicLocalization (Lattice lattice translate SupportedInCube
  latticeBoxFinset periodize_locally_eq_sum)
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Paper1.CorrectionForceNorms (physicalForce_smooth physicalForce_compact)
open NSFormalization.Source.PhysicalRemoval (physical_support)
open NSFormalization.Source.LocalizedInsertion (correctionForce_support)
open scoped ContDiff Topology BigOperators

/-! ## 0. The space-time companion of `T16.latticeLift_sliceSupport_closed` -/

/-- Space-time version of `T16.latticeLift_sliceSupport_closed`: if the spatial
slice support of `w` is contained in a *closed* set `C ⊆ ball x₀ ρ`, then the
whole space-time `tsupport` of the lift has its spatial projection inside
`periodicSet C`.  The proof is the slice proof run at the space-time point: the
neighbourhood produced by `periodize_locally_eq_sum` is already a space-time
neighbourhood, and each translate `translate w n` has its support inside the
closed preimage `(fun z => z.2 - lattice n) ⁻¹' C`. -/
theorem latticeLift_spaceSupport {w : SpaceTimeField} {C : Set Space} {x₀ : Space} {ρ : ℝ}
    (hCclosed : IsClosed C) (hCball : C ⊆ ball x₀ ρ)
    (hslice : ∀ z : SpaceTime, w z ≠ 0 → z.2 ∈ C) :
    tsupport (latticeLift w) ⊆ (univ : Set ℝ) ×ˢ periodicSet C := by
  have hsc : SupportedInCube (ρ + ‖x₀‖) w :=
    supportedInCube_of_ball (fun z hz => hCball (hslice z hz))
  intro z hz
  refine ⟨mem_univ _, ?_⟩
  by_contra hxnot
  obtain ⟨N, hN⟩ := periodize_locally_eq_sum hsc z
  have hNs : latticeLift w =ᶠ[𝓝 z]
      (fun y => ∑ n ∈ latticeBoxFinset N, translate w n y) := by
    filter_upwards [hN] with y hy
    rw [latticeLift_eq_periodize]
    exact hy
  have hterm : ∀ n ∈ latticeBoxFinset N, translate w n =ᶠ[𝓝 z] 0 := by
    intro n _
    rw [← notMem_tsupport_iff_eventuallyEq]
    intro hzin
    have hsuppn : Function.support (translate w n)
        ⊆ (fun y : SpaceTime => y.2 - lattice n) ⁻¹' C := by
      intro y hy
      have hyne : w (y.1, y.2 - lattice n) ≠ 0 := hy
      exact hslice (y.1, y.2 - lattice n) hyne
    have hclosed : IsClosed ((fun y : SpaceTime => y.2 - lattice n) ⁻¹' C) :=
      hCclosed.preimage (continuous_snd.sub continuous_const)
    exact hxnot ⟨n, closure_minimal hsuppn hclosed hzin⟩
  have hzero : (fun y => ∑ n ∈ latticeBoxFinset N, translate w n y) =ᶠ[𝓝 z] 0 := by
    have hall : ∀ᶠ y in 𝓝 z, ∀ n ∈ latticeBoxFinset N, translate w n y = 0 :=
      (eventually_all_finset _).mpr (fun n hn => hterm n hn)
    filter_upwards [hall] with y hy
    simp only [Pi.zero_apply]
    exact Finset.sum_eq_zero hy
  exact absurd hz (notMem_tsupport_iff_eventuallyEq.mpr (hNs.trans hzero))

/-! ## 1. The single Euclidean copy of the force -/

/-- The Section 4 single-copy correction force inherits the space-time cylinder
support of the single-copy correction: the force is a local operator of the
correction (`correctionForce_support`), whose support is the chart cylinder
(`physical_support`).  Note the spatial factor is the manuscript's **open**
ball. -/
theorem source_force_tsupport (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} {θR ε : ℝ} (hε : 0 < ε)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    tsupport (NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))
      ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * θR) :=
  (correctionForce_support ν v (physicalCorrection v x₀ T θ η ε)).trans
    (physical_support hε v x₀ T hθc hηc hθsupp hηsupp)

/-! ## 2. The three canonical fields at the concrete `correctionData` -/

/-- **U7 (a)** — `03-torus.tex:225`, `CorrectionAPI.force_smooth`: the
periodized correction force is globally smooth.  `hv` enters through Paper1's
`physicalForce_smooth` (global smoothness of the single copy) and through
`force_eq` (local smoothness of the reference). -/
theorem force_smooth (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      ContDiff ℝ ∞ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) := by
  intro ε hε
  have hforce := force_eq (ν := ν) (v := v) (x₀ := x₀) (T := T)
    (δ := δ) (r := r) (θ := θ) (η := η) (O := O) (θR := θR)
    (ε₀ := ε₀) (ε := ε) hvper hv.contDiffOn hθ hη hθc hηc hθsupp hηsupp hr2
    hε.1 (hεspace ε hε) (hεtime ε hε)
  rw [hforce]
  refine latticeLift_smooth (x₀ := x₀) (ρ := ε * θR)
    (physicalForce_smooth ν hv x₀ T ε hθ hη) ?_
  intro z hz
  exact (source_force_tsupport ν v x₀ T hε.1 hθc hηc hθsupp hηsupp
    (subset_tsupport _ hz)).2

/-- **U7 (b)** — `03-torus.tex:225,235-240`, `CorrectionAPI.force_periodic`:
the periodized correction force is unit-periodic.  `hv` enters only through
`force_eq`'s local smoothness premise. -/
theorem force_periodic (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      IsPeriodicOn univ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) := by
  intro ε hε
  exact correctionForce_periodic (ν := ν) (v := v) (x₀ := x₀) (T := T)
    (δ := δ) (r := r) (θ := θ) (η := η) (O := O) (θR := θR)
    (ε₀ := ε₀) (ε := ε) hvper hv.contDiffOn hθ hη hθc hηc hθsupp hηsupp hr2
    hε.1 (hεspace ε hε) (hεtime ε hε)

/-- **U7 (c)** — `03-torus.tex:225`, `CorrectionAPI.force_support`: the
space-time support of the periodized correction force lies in the time window
`Ioo (T - 2ε²) (T + 2ε²)` times the periodic lift of the **open** spatial ball
`ball x₀ (ε·θRadius)`.  Here `hv` enters only through `force_eq`'s local
smoothness premise: the compact support of the single copy
(`physicalForce_compact`) and its cylinder support (`source_force_tsupport`)
need no regularity of the reference. -/
theorem force_support (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      tsupport (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ⊆
        Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ
          periodicSet (ball x₀ (ε * (correctionData v x₀ T θ η O θR ε₀).θRadius)) := by
  intro ε hε
  have hforce := force_eq (ν := ν) (v := v) (x₀ := x₀) (T := T)
    (δ := δ) (r := r) (θ := θ) (η := η) (O := O) (θR := θR)
    (ε₀ := ε₀) (ε := ε) hvper hv.contDiffOn hθ hη hθc hηc hθsupp hηsupp hr2
    hε.1 (hεspace ε hε) (hεtime ε hε)
  rw [hforce]
  have hGtsupp : tsupport (NSFormalization.Source.correctionForce ν v
        (physicalCorrection v x₀ T θ η ε))
      ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ ball x₀ (ε * θR) :=
    source_force_tsupport ν v x₀ T hε.1 hθc hηc hθsupp hηsupp
  have hGcs : HasCompactSupport (NSFormalization.Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε)) :=
    physicalForce_compact ν v x₀ T ε (ne_of_gt hε.1) hθc hηc
  have hGcompact : IsCompact (tsupport (NSFormalization.Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε))) := hGcs
  have hCcompact : IsCompact (Prod.snd '' tsupport (NSFormalization.Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε))) := hGcompact.image continuous_snd
  have hCball : Prod.snd '' tsupport (NSFormalization.Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε)) ⊆ ball x₀ (ε * θR) := by
    rintro _ ⟨z, hzmem, rfl⟩
    exact (hGtsupp hzmem).2
  have hslice : ∀ z : SpaceTime, NSFormalization.Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε) z ≠ 0 →
      z.2 ∈ Prod.snd '' tsupport (NSFormalization.Source.correctionForce ν v
        (physicalCorrection v x₀ T θ η ε)) :=
    fun z hz => ⟨z, subset_tsupport _ hz, rfl⟩
  have htime : tsupport (latticeLift (NSFormalization.Source.correctionForce ν v
        (physicalCorrection v x₀ T θ η ε)))
      ⊆ Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space) :=
    latticeLift_timeSupport hGcs
      (hGtsupp.trans (Set.prod_mono (subset_refl _) (subset_univ _)))
  have hspace : tsupport (latticeLift (NSFormalization.Source.correctionForce ν v
        (physicalCorrection v x₀ T θ η ε)))
      ⊆ (univ : Set ℝ) ×ˢ periodicSet (Prod.snd '' tsupport
        (NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε))) :=
    latticeLift_spaceSupport (ρ := ε * θR) hCcompact.isClosed hCball hslice
  intro z hz
  exact ⟨(htime hz).1, periodicSet_mono hCball (hspace hz).2⟩

end NSFormalization.Section3.T17
