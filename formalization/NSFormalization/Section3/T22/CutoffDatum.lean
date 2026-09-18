import NSFormalization.Section3.T22.Domain
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# T22 · unit U-B3 — smooth cutoffs and the cutoff datum of a zero extension

Two bookkeeping targets consumed by unit U-Z1 (`research/T22/T22_SPLIT.md`):

* `exists_cutoff` — for `K ⋐ Ω` with `Ω` open and `K` compact there is a smooth,
  compactly supported `χ : Space → ℝ` with `tsupport χ ⊆ Ω` which equals `1` on a
  neighbourhood of `K`.  The neighbourhood clause is stated in the filter form
  `∀ᶠ x in 𝓝ˢ K, χ x = 1`; `exists_cutoff_isOpen` repackages the same statement in
  the explicit form `∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1`.

* `isCutoffDatum_realizes_zeroExtension` — if `B` is the cutoff datum of `A`
  (`IsCutoffDatum s χ A B`, i.e. `B` is the transpose of multiplication by `χ`
  applied to `A`), `A` restricts on interior tests to the physical field `z`
  (`restrictDatum Ω s A = restrictField Ω z`), the zero extension `E₀z` is supported
  in `K`, and `χ = 1` near `K` with `tsupport χ ⊆ Ω`, then `B` is a genuine
  whole-space Sobolev datum of `E₀z`.

## Routes

`exists_cutoff` is Mathlib's smooth Urysohn lemma in the model-space form: `Space`
is a finite-dimensional real normed space, hence a `C^∞` manifold over
`𝓘(ℝ, Space)`, and it is `T2`, `NormalSpace` and `SigmaCompactSpace`, so
`exists_contMDiffMap_one_nhds_of_subset_interior` applies to the closed set `K` and
a compact neighbourhood `L` of `K` inside `Ω` produced by `exists_compact_between`.
`contMDiff_iff_contDiff` transports the smoothness back to `ContDiff ℝ ∞`.
(The vector-space-only bump API `exists_contDiff_tsupport_subset` /
`IsOpen.exists_contDiff_support_eq` in
`Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean` produces bumps at a
*single point* or supports equal to an open set, not a function equal to `1` on a
neighbourhood of an arbitrary compact set, so it does not close `exists_cutoff` on
its own.)

`isCutoffDatum_realizes_zeroExtension` is the pointwise identity
`(χ · ψ) x * z x i = ψ x * (E₀z) x i`, valid at *every* `x` — inside `tsupport (E₀z)`
because `χ x = 1` (and `χ x = 1 ≠ 0` forces `x ∈ tsupport χ ⊆ Ω`, so `E₀z x = z x`),
outside it because `E₀z x = 0` and either `x ∈ Ω` (so `z x = 0` too) or
`x ∉ tsupport χ` (so `χ x = 0`).  No measurability of `Ω` and no `IsOpen Ω` are
needed.

No `sorry`/`axiom`/`native_decide`; every declaration prints
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory Filter
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev angularRealization)
open NSFormalization.Source.RealSobolev (FourierData)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal SchwartzMap Topology Manifold

/-! ## 1. Existence of a smooth cutoff -/

/-- **U-B3 (a).**  A compact set inside an open set carries a smooth compactly supported
cutoff which is identically `1` on a neighbourhood of the compact set and whose closed
support stays inside the open set. -/
theorem exists_cutoff {Ω K : Set Space} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) := by
  obtain ⟨L, hLc, hKL, hLΩ⟩ := exists_compact_between hK hΩ hKΩ
  obtain ⟨f, hf1, hf0, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Space)) (M := Space)
      (n := ⊤) hK.isClosed hKL
  have hsupp : Function.support (f : Space → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (hf0 x hxL)
  have htsupp : tsupport (f : Space → ℝ) ⊆ L :=
    (closure_mono hsupp).trans hLc.isClosed.closure_subset
  refine ⟨f, ?_, ?_, htsupp.trans hLΩ, hf1⟩
  · exact contMDiff_iff_contDiff.mp f.contMDiff
  · exact hLc.of_isClosed_subset isClosed_closure htsupp

/-- The same statement with the neighbourhood spelled out as an explicit open set. -/
theorem exists_cutoff_isOpen {Ω K : Set Space} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      ∃ V : Set Space, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨χ, hχs, hχc, hχΩ, hχ1⟩ := exists_cutoff hΩ hK hKΩ
  obtain ⟨V, hVo, hKV, hVχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  exact ⟨χ, hχs, hχc, hχΩ, V, hVo, hKV, hVχ⟩

/-! ## 2. The cutoff datum realizes the zero extension -/

/-- **U-B3 (b).**  If `B` is the cutoff datum of `A` for a smooth compactly supported `χ`
with `tsupport χ ⊆ Ω` and `χ = 1` on a neighbourhood of `K`, if `A` restricts on interior
tests to the physical field `z`, and if the zero extension of `z` is supported in `K`, then
`B` is a whole-space Sobolev datum of the zero extension. -/
theorem isCutoffDatum_realizes_zeroExtension {Ω K : Set Space} {s : ℝ} {χ : Space → ℝ}
    {z : SpatialField} {A B : RealVectorSobolev s}
    (hχs : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (hχ1 : ∀ᶠ x in 𝓝ˢ K, χ x = 1)
    (hcut : IsCutoffDatum s χ A B)
    (hA : restrictDatum Ω s A = restrictField Ω z)
    (hsupp : tsupport (zeroExtension Ω z) ⊆ K) :
    IsSobolevDatum s (zeroExtension Ω z) B := by
  -- the complexified cutoff is a temperate-growth multiplier
  have hχCs : ContDiff ℝ ∞ (fun x => ((χ x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hχs
  have hχCc : HasCompactSupport (fun x => ((χ x : ℝ) : ℂ)) := by
    apply hχc.comp_left (g := fun r : ℝ => (r : ℂ)); simp
  have hgrowth : Function.HasTemperateGrowth (fun x => ((χ x : ℝ) : ℂ)) :=
    hχCc.hasTemperateGrowth hχCs
  -- `χ x = 0` off `tsupport χ`
  have hχzero : ∀ x, x ∉ tsupport χ → χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport hx
  intro i ψ
  set φ : SchwartzMap Space ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun x => ((χ x : ℝ) : ℂ)) ψ with hφdef
  have hφval : ∀ x, (φ : Space → ℂ) x = ((χ x : ℝ) : ℂ) * ψ x := by
    intro x
    rw [hφdef, SchwartzMap.smulLeftCLM_apply_apply hgrowth, smul_eq_mul]
  -- `φ` is an interior test
  have hφsupp : Function.support (φ : Space → ℂ) ⊆ Function.support χ := by
    intro x hx
    by_contra hxχ
    have : χ x = 0 := by simpa [Function.mem_support, not_not] using hxχ
    exact hx (by rw [hφval x, this]; simp)
  have hφtsupp : tsupport (φ : Space → ℂ) ⊆ Ω := (closure_mono hφsupp).trans hχΩ
  have hφc : HasCompactSupport (φ : Space → ℂ) :=
    hχc.of_isClosed_subset isClosed_closure (closure_mono hφsupp)
  -- the pointwise identity, valid at every point
  have hpt : ∀ x, (φ : Space → ℂ) x * ((z x i : ℝ) : ℂ)
      = ψ x * (((zeroExtension Ω z) x i : ℝ) : ℂ) := by
    intro x
    by_cases hx : x ∈ tsupport (zeroExtension Ω z)
    · have hχx : χ x = 1 := hχ1.self_of_nhdsSet x (hsupp hx)
      have hxΩ : x ∈ Ω := by
        refine hχΩ (subset_tsupport χ ?_)
        simp [Function.mem_support, hχx]
      rw [hφval x, hχx]
      simp [zeroExtension, Set.indicator_of_mem hxΩ]
    · have hE : zeroExtension Ω z x = 0 := image_eq_zero_of_notMem_tsupport hx
      by_cases hxΩ : x ∈ Ω
      · have hz : z x = 0 := by
          rw [zeroExtension, Set.indicator_of_mem hxΩ] at hE; exact hE
        simp [hφval x, hz, hE]
      · have hχx : χ x = 0 := hχzero x (fun h => hxΩ (hχΩ h))
        simp [hφval x, hχx, hE]
  -- off `Ω` the left integrand vanishes
  have hoff : ∀ x, x ∉ Ω → (φ : Space → ℂ) x * ((z x i : ℝ) : ℂ) = 0 := by
    intro x hx
    have hχx : χ x = 0 := hχzero x (fun h => hx (hχΩ h))
    simp [hφval x, hχx]
  calc angularRealization s ((B i : FourierData)) ψ
      = angularRealization s ((A i : FourierData)) φ := hcut i ψ
    _ = ∫ x in Ω, (φ : Space → ℂ) x * ((z x i : ℝ) : ℂ) :=
        congrFun (congrFun hA i) ⟨φ, hφc, hφtsupp⟩
    _ = ∫ x, (φ : Space → ℂ) x * ((z x i : ℝ) : ℂ) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hoff
    _ = ∫ x, ψ x * (((zeroExtension Ω z) x i : ℝ) : ℂ) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end NSFormalization.Section3.T22
