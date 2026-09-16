import Bindings.BochnerPartial
import Bindings.CompactClassDensity

/-!
# Proposition 4.6: completed inhomogeneous Sobolev density

This module proves the first field of `research/R46/Spec.lean`.  A completed
Bochner datum is first approximated by a compact smooth force.  Compact-class
relative density then replaces that force by one whose maximal lifespan is at
most the prescribed time.  The datum path of the compact perturbation is
extracted from `forceSobolevENorm`; adding it to the first datum path gives the
required completed-space approximation.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4
open scoped ENNReal

/-- Proposition 4.6, first clause, with the binder order and statement of
`REnergyAPI.completedSobolevDensity` verbatim. -/
theorem completedSobolevDensity :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
            ∀ s : ℝ, s < criticalOrder q.toReal →
              CompletedDense q s
                (breakdownSetIn forceClassCompact ν a T) := by
  intro a ha ν hν T hT q hq s hs b hb r hr
  have hq1 : 1 ≤ q := by
    rcases hq with rfl | rfl <;> norm_num
  have hqtop : q ≠ ⊤ := by
    rcases hq with rfl | rfl <;> norm_num
  have hrhalf : 0 < r / 2 := ENNReal.half_pos hr.ne'
  obtain ⟨g, hg, Dg, hDg, hDgmeas, hDgdist⟩ :=
    bochnerPartial.approxCompact q hq1 hqtop s b hb (r / 2) hrhalf
  obtain ⟨f, hf, hfgdist⟩ :=
    density_compact ν hν T hT q hq s a ha hs g hg (r / 2) hrhalf
  rw [forceSobolevENorm, iInf_lt_iff] at hfgdist
  obtain ⟨E, hEdist⟩ := hfgdist
  have hgR : MemForceR g := bochnerPartial.compactSubsetForceR hg
  have hfR : MemForceR f := bochnerPartial.compactSubsetForceR hf.1
  have hpairDiff :
      ∀ t : ℝ, 0 ≤ t → ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
        Integrable
          (fun x : Space => ψ x * ((((f - g) (t, x)) i : ℝ) : ℂ)) volume := by
    intro t ht i ψ
    have hfint := datumLemmas.memForceR_slice_integrable f hfR t ht i ψ
    have hgint := datumLemmas.memForceR_slice_integrable g hgR t ht i ψ
    convert hfint.sub hgint using 1
    funext x
    show ψ x * ((((f (t, x) - g (t, x)) i : ℝ) : ℂ)) = _
    rw [PiLp.sub_apply]
    push_cast
    change ψ x * (↑((f (t, x)).ofLp i) - ↑((g (t, x)).ofLp i)) =
      ψ x * ↑((f (t, x)).ofLp i) - ψ x * ↑((g (t, x)).ofLp i)
    exact mul_sub _ _ _
  have hpathSum : IsSobolevPath s (g + (f - g)) (Dg + E.1) :=
    datumLemmas.isSobolevPath_add s g (f - g) Dg E.1
      (datumLemmas.memForceR_slice_integrable g hgR) hpairDiff hDg E.2.1
  have hfield : g + (f - g) = f := by
    funext z
    change g z + (f z - g z) = f z
    abel
  refine ⟨f, hf, Dg + E.1, ?_, hDgmeas.add E.2.2, ?_⟩
  · simpa only [hfield] using hpathSum
  · show eLpNorm ((Dg + E.1) - b) q forceTimeMeasure < r
    rw [show (Dg + E.1) - b = E.1 + (Dg - b) by abel]
    refine (eLpNorm_add_le E.2.2 (hDgmeas.sub hb.1) hq1).trans_lt ?_
    exact (ENNReal.add_lt_add hEdist hDgdist).trans_eq (ENNReal.add_halves r)

/-! A concrete specialization certifying that the completed-density statement
really reaches the zero target at `ν = T = 1`, `a = 0`, `q = 1`, `s = 0`. -/
example :
    ∀ r : ℝ≥0∞, 0 < r →
      ∃ f ∈ breakdownSetIn forceClassCompact 1 (0 : SpatialField) 1,
        ∃ D : ℝ → RealVectorSobolev 0,
          IsSobolevPath 0 f D ∧
            AEStronglyMeasurable D forceTimeMeasure ∧
              bochnerDatumENorm 1 0
                (D - (fun _ : ℝ => (0 : RealVectorSobolev 0))) < r := by
  have hdense := completedSobolevDensity (0 : SpatialField)
    A04.zero_mem_initialClassR 1 (by norm_num) 1 (by norm_num)
    1 (Or.inl rfl) 0 (by norm_num [criticalOrder])
  exact hdense (fun _ : ℝ => (0 : RealVectorSobolev 0))
    (by
      change MemLp (0 : ℝ → RealVectorSobolev 0) 1 forceTimeMeasure
      exact MemLp.zero)

end BlowupDensity.Bindings
