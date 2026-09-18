import NSFormalization.Section3.T22.Domain
import NSFormalization.Section4.D01.DatumToJets

/-!
# T22 U-B2: regularity of a compactly supported zero extension

The literal extension `zeroExtension Ω z` is `Ω.indicator z`.  If its closed
support is contained in a compact set `K ⊆ Ω`, then the indicator agrees with
the smooth field on the open domain and is identically zero on the open
complement of its support.  These local descriptions glue to a global smooth
field, and compact support then gives all square-integrable spatial jets.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory Filter
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal Topology

/-- The zero extension is globally smooth when its closed support stays inside
the open domain. -/
theorem contDiff_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (_hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    ContDiff ℝ ∞ (zeroExtension Ω z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ω
  · have heq : zeroExtension Ω z =ᶠ[𝓝 x] z := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      simp [zeroExtension, hy]
    exact (hz.contDiffAt (hΩ.mem_nhds hx)).congr_of_eventuallyEq heq
  · have hxK : x ∉ K := fun hxK => hx (hKΩ hxK)
    have hxts : x ∉ tsupport (zeroExtension Ω z) := fun hxts =>
      hxK (hsupp hxts)
    have heq : zeroExtension Ω z =ᶠ[𝓝 x] (fun _ : Space => (0 : Space)) := by
      filter_upwards [(isClosed_tsupport (zeroExtension Ω z)).isOpen_compl.mem_nhds hxts]
        with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- The same support hypothesis gives compact support of the zero extension. -/
theorem hasCompactSupport_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (_hΩ : IsOpen Ω) (_hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (_hKΩ : K ⊆ Ω)
    (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    HasCompactSupport (zeroExtension Ω z) := by
  apply HasCompactSupport.intro hK
  intro x hxK
  apply image_eq_zero_of_notMem_tsupport
  intro hxts
  exact hxK (hsupp hxts)

/-- Every compactly supported smooth zero extension is square integrable. -/
theorem memLp_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    MemLp (zeroExtension Ω z) 2 volume := by
  exact (contDiff_zeroExtension hΩ hz hK hKΩ hsupp).continuous
    |>.memLp_of_hasCompactSupport (hasCompactSupport_zeroExtension hΩ hz hK hKΩ hsupp)

/-- All spatial jets of the zero extension are square integrable. -/
theorem smoothJets_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    SmoothSquareIntegrableJets (zeroExtension Ω z) := by
  let hsmooth : ContDiff ℝ ∞ (zeroExtension Ω z) :=
    contDiff_zeroExtension hΩ hz hK hKΩ hsupp
  let hcompact : HasCompactSupport (zeroExtension Ω z) :=
    hasCompactSupport_zeroExtension hΩ hz hK hKΩ hsupp
  refine ⟨hsmooth, ?_⟩
  intro n
  exact (hsmooth.continuous_iteratedFDeriv (by exact_mod_cast le_top)).memLp_of_hasCompactSupport
    (hcompact.iteratedFDeriv n)

/-- D01's all-order constructor applied to the compactly supported zero
extension. -/
theorem exists_datum_zeroExtension {Ω K : Set Space} {z : SpatialField}
    (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) (s : ℝ) :
    ∃ A, IsSobolevDatum s (zeroExtension Ω z) A := by
  have hjets : SmoothSquareIntegrableJets (zeroExtension Ω z) :=
    smoothJets_zeroExtension hΩ hz hK hKΩ hsupp
  exact exists_isSobolevDatum_of_contDiff_memLp hjets.1 hjets.2 s

end NSFormalization.Section3.T22
