import NSFormalization.Section4.A02.Patch

/-!
# R42 split item #2a: pointwise speed blow-up ⟹ `L^∞` (essential-supremum) blow-up

`research/R42/LIFESPAN_SPLIT.md`, section "(#2) `blowup_essSup`".  The lifespan
identification of Theorem 4.2 (`paper/sections/04-whole-space.tex:34,53`) feeds
`A02`'s `MaximalPartial.lifespan_le_of_unbounded` the `L^∞` blow-up clause
`limsup_{t↑T} ‖u_ε(t)‖_{L^∞} = ∞` (`04-whole-space.tex:35`).  The assembly proves
only the **pointwise** blow-up `SpeedUnboundedAt T u_ε` (`Contracts/V1/Scaling.lean:124`).
This module bridges the two.

Contents.

1. `ofReal_le_eLpNormTop_of_continuous` (**S**) -- the essential supremum of a
   *continuous* spatial field dominates any value it attains: if `M < ‖z x‖` then
   `ENNReal.ofReal M ≤ eLpNorm z ⊤ volume`.  The open set `{y | M < ‖z y‖}` is
   nonempty (contains `x`), hence has positive Lebesgue measure (`volume` on
   `R³ = EuclideanSpace ℝ (Fin 3)` is `IsOpenPosMeasure`), so the essential
   supremum cannot drop below `ofReal M`.
2. `limsupLeft_speedENorm_eq_top` (**M**) -- the left limsup of the
   essential-supremum speed is `⊤`: for each `M, δ` the pointwise blow-up produces
   a time `t` arbitrarily close to `T` (below it) with a point where the speed
   exceeds `M`, and (1) turns that into `ofReal M ≤ ‖u_ε(t)‖_{L^∞}`; the
   `frequently`-characterisation of a limsup then forces it to `⊤`.
3. `continuous_slice_of_velocity_smooth` -- the `hcont` input of (2) from the exact
   shape of `InsertionFamilyAPI.velocity_smooth` (`ContDiffOn ℝ ∞` on `[0,T) × R³`),
   so the R42 assembly lane needs no glue.

`A02.limsupLeft T φ = Filter.limsup φ (nhdsWithin T (Iio T))` and
`A02.speedENorm z = eLpNorm z ⊤ volume` are imported verbatim from
`Section4/A02/Patch.lean:55,60` (byte-identical to
`verification/Contracts/V1/MaximalPartial.lean:101,106`); they are *not* restated
here.  The pointwise predicate `SpeedUnboundedAt` is **reused** from the pre-existing
canonical local copy `NSFormalization.Source.PacketScaling.SpeedUnboundedAt`
(`Source/PacketScaling.lean:22`, opened below; character-identical to
`verification/Contracts/V1/Scaling.lean:124` and already `rfl`-bridged in
`verification/Bindings/Scaling.lean:50`), not restated here.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling

namespace NSFormalization.Section4.R42

/-! ## 1. The essential supremum dominates an attained value (S) -/

/-- **Split item #2a, the pointwise-to-essSup step (S).**  If a *continuous*
spatial field `z : R³ → R³` attains `M < ‖z x‖` at some point `x`, then its
`L^∞` norm satisfies `ENNReal.ofReal M ≤ eLpNorm z ⊤ volume`.

The set `{y | M < ‖z y‖}` is open (`isOpen_lt`, `z` continuous) and nonempty (it
contains `x`), hence of positive Lebesgue measure because `volume` on
`R³ = EuclideanSpace ℝ (Fin 3)` is `IsOpenPosMeasure`.  Were the essential
supremum below `ofReal M`, `ae_lt_of_essSup_lt` would put `‖z y‖ₑ < ofReal M`
almost everywhere, i.e. the set above would be null -- contradicting its positive
measure.  (`M ≤ 0` is covered too: the open set is still nonempty and the
argument goes through unchanged.) -/
theorem ofReal_le_eLpNormTop_of_continuous {z : Space → Space} (hz : Continuous z)
    {M : ℝ} {x : Space} (hx : M < ‖z x‖) :
    ENNReal.ofReal M ≤ eLpNorm z ⊤ (volume : Measure Space) := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : essSup (fun y => ‖z y‖ₑ) volume < ENNReal.ofReal M`
  have hae : ∀ᵐ y ∂(volume : Measure Space), ‖z y‖ₑ < ENNReal.ofReal M :=
    ae_lt_of_essSup_lt hcon
  have hopen : IsOpen {y : Space | M < ‖z y‖} := isOpen_lt continuous_const hz.norm
  have hpos : 0 < volume {y : Space | M < ‖z y‖} := hopen.measure_pos volume ⟨x, hx⟩
  have hsub : {y : Space | M < ‖z y‖} ⊆ {y : Space | ¬ ‖z y‖ₑ < ENNReal.ofReal M} := by
    intro y hy
    have hy' : M < ‖z y‖ := hy
    show ¬ ‖z y‖ₑ < ENNReal.ofReal M
    rw [not_lt]
    calc ENNReal.ofReal M ≤ ENNReal.ofReal ‖z y‖ := ENNReal.ofReal_le_ofReal hy'.le
      _ = ‖z y‖ₑ := ofReal_norm _
  have hzero : volume {y : Space | ¬ ‖z y‖ₑ < ENNReal.ofReal M} = 0 := ae_iff.mp hae
  exact absurd ((measure_mono hsub).trans hzero.le) (not_le.mpr hpos)

/-! ## 2. The left limsup of the essential-supremum speed is `⊤` (M) -/

/-- **Split item #2, `blowup_essSup` (M).**  The pointwise blow-up
`SpeedUnboundedAt T u` together with continuity of each spatial slice `u(t,·)`
(here on `(0,T)`) forces the left limsup of the `L^∞` speed to be `⊤`:
`A02.limsupLeft T (fun t => A02.speedENorm (u(t,·))) = ⊤`, the manuscript's
`limsup_{t↑T} ‖u(t)‖_{L^∞} = ∞` (`paper/sections/04-whole-space.tex:35,53`).

Proof.  Suppose the limsup were `< ⊤`.  Pick `b` strictly between it and `⊤`.
The limsup is over `𝓝[<] T`, whose `Ioo · T` basis (`nhdsLT_basis`) makes
`∃ᶠ t, b ≤ speedENorm (u(t,·))` amount to: for every `c < T` there is
`t ∈ (c,T)` with `b ≤ speedENorm (u(t,·))`.  Apply `SpeedUnboundedAt` at
`M = b.toReal + 1` and `δ = T - c` to get such a `t` (and a point `x` with
`M < ‖u(t,x)‖`); step (1) gives `ofReal M ≤ speedENorm (u(t,·))`, and
`b ≤ ofReal M` since `b ≠ ⊤`.  Then `le_limsup_of_frequently_le'` yields
`b ≤ limsup`, contradicting `limsup < b`. -/
theorem limsupLeft_speedENorm_eq_top {T : ℝ} {u : ℝ × Space → Space}
    (hblow : SpeedUnboundedAt T u)
    (hcont : ∀ t ∈ Ioo (0:ℝ) T, Continuous (fun x => u (t, x))) :
    A02.limsupLeft T (fun t => A02.speedENorm (fun x => u (t, x))) = ⊤ := by
  by_contra hne
  have hlt : A02.limsupLeft T (fun t => A02.speedENorm (fun x => u (t, x))) < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  -- `hb1 : limsupLeft < b`, `hb2 : b < ⊤`
  have hfreq : ∃ᶠ t in nhdsWithin T (Iio T),
      b ≤ A02.speedENorm (fun x => u (t, x)) := by
    refine (nhdsLT_basis T).frequently_iff.mpr ?_
    intro c hc
    have hb0 : (0 : ℝ) ≤ b.toReal := ENNReal.toReal_nonneg
    obtain ⟨t, x, ht, htc, hMx⟩ :=
      hblow (b.toReal + 1) (by linarith) (T - c) (by linarith)
    refine ⟨t, ⟨by linarith [htc], ht.2⟩, ?_⟩
    have hM1 : ENNReal.ofReal (b.toReal + 1) ≤ A02.speedENorm (fun x => u (t, x)) :=
      ofReal_le_eLpNormTop_of_continuous (hcont t ht) hMx
    calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb2.ne).symm
      _ ≤ ENNReal.ofReal (b.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ A02.speedENorm (fun x => u (t, x)) := hM1
  have hle : b ≤ A02.limsupLeft T (fun t => A02.speedENorm (fun x => u (t, x))) :=
    le_limsup_of_frequently_le' hfreq
  exact absurd hle (not_le.mpr hb1)

/-! ## 3. Slice continuity from spacetime smoothness -- the `hcont` input of §2 -/

/-- **The `hcont` input of `limsupLeft_speedENorm_eq_top`, from the exact shape of
`InsertionFamilyAPI.velocity_smooth`** (`Contracts/V1/InsertionFamily.lean:196`,
mirroring `Data.ClassicalSolutionR.velocity_smooth`): every spatial slice `u(t,·)`
with `t ∈ (0,T)` is continuous, given `u` is `ContDiffOn ℝ ∞` on the half-open
spacetime box `[0,T) × R³`.  `Ioo 0 T ×ˢ univ` is an *open* subset of that box, so
the `ContinuousOn` upgrades to `ContinuousAt` there (`ContinuousOn.continuousAt` via
`IsOpen.mem_nhds`), and composing with the continuous `y ↦ (t,y)` gives full
continuity of the slice.  `Ioo` (not `Ico`) is deliberate: at `t = 0` the point sits
on the box's boundary and only `ContinuousWithinAt` is available.

This closes the R42 assembly lane's remaining glue for clause #2: with this lemma
`hcont` follows from `velocity_smooth` in one application.  Derivation supplied by
the lane-080 reviewer (`research/R42/REVIEW_BLOWUP.md`, finding 3). -/
theorem continuous_slice_of_velocity_smooth {T : ℝ} {u : ℝ × Space → Space}
    (hu : ContDiffOn ℝ ∞ u (Ico (0:ℝ) T ×ˢ (univ : Set Space))) :
    ∀ t ∈ Ioo (0:ℝ) T, Continuous (fun x => u (t, x)) := by
  intro t ht
  have hopen : IsOpen (Ioo (0:ℝ) T ×ˢ (univ : Set Space)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo (0:ℝ) T ×ˢ (univ : Set Space) ⊆ Ico (0:ℝ) T ×ˢ (univ : Set Space) :=
    Set.prod_mono Ioo_subset_Ico_self (subset_refl _)
  refine continuous_iff_continuousAt.mpr (fun x => ?_)
  have hmem : ((t, x) : ℝ × Space) ∈ Ioo (0:ℝ) T ×ˢ (univ : Set Space) := ⟨ht, mem_univ x⟩
  have hCA : ContinuousAt u (t, x) :=
    (hu.continuousOn.mono hsub).continuousAt (hopen.mem_nhds hmem)
  exact hCA.comp (by fun_prop : ContinuousAt (fun y : Space => ((t, y) : ℝ × Space)) x)

end NSFormalization.Section4.R42
