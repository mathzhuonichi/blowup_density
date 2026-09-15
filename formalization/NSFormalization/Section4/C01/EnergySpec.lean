import NSFormalization.Section4.C01.EnergyDerivative
import NSFormalization.Section4.C01.ForceSlices
import NSFormalization.Section4.C01.Vocabulary

/-!
# Section 4 · C01 — the ordinary energy identity in the spec's `l2Sq`/`slice`/`pairing` form

`energyIdentity_classical_unconditional` (`EnergyDerivative.lean`) is the ordinary energy
identity (`02-preliminaries.tex:136-139`, cf. `04-whole-space.tex:117`) as a genuine
`HasDerivAt` at every interior time, but with the `L²` energy presented on the closed
window `[0,(t+T)/2]` through `projIcc` and its derivative in the vendor's
`SmoothL2Field.field`/`.toLp` vocabulary.  This module restates it in the specification's
own time-slice vocabulary — `l2Sq`/`slice` (`research/C01/Spec.lean:172,167`, from
`ForceSlices`) and the new `pairing` (`Spec.lean:196`) — which is the shape the
`verification`-side C01 V2 contract field `energyIdentity` (`Spec.lean:344-350`) registers.

Only the LHS bridge `norm_toLp_sq_eq_l2Sq` (`Vocabulary.lean:107`, **not** `rfl`) and a
`projIcc`-locality `HasDerivAt.congr_of_eventuallyEq` are needed; the derivative value is
carried unchanged, because `axis i = coordinateVector i`, `⟪·,·⟫ = inner ℝ`, and `pairing`
unfolds to the raw force integral, all definitionally.  The one remaining vocabulary step to
the contract's `gradientSq` — `PiLp.norm_sq_eq_of_L2` — is taken in the V2 binding on the
`verification` side, where `gradientTensor` is importable.

This is the `formalization` prerequisite of the C01 V2 contract (the strictly nicer,
clamp-free statement `research/C01/REVIEW_E4.md` §4 prescribes; verified compiling as
`research/C01/probes/rev150_gap.lean`).
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-- `research/C01/Spec.lean:196`, the real `L²(R³;R³)` pairing `⟨w, z⟩ = ∫ x, ⟪w x, z x⟫`
(the domain is `A02.SpatialField`, i.e. the `Space → Space` of `slice`; this selective-open
module has no bare `SpatialField` in scope).  There is no other `pairing` in
`formalization/`; the V2 binding records `Contracts.V2.…pairing = this` by `rfl`. -/
def pairing (w z : A02.SpatialField) : ℝ := ∫ x, (inner ℝ (w x) (z x) : ℝ)

/-- **The ordinary energy identity in the spec's `l2Sq`/`slice`/`pairing` vocabulary.**
For a classical solution `w` with real admissible force `hf`, at every interior time
`t ∈ Ioo 0 T`,

  `d/dt (l2Sq (slice u s)) = −2ν · (∫ ∑ᵢ‖∂ᵢu(t,·)‖²) + 2 · pairing (u(t,·)) (f(t,·))`.

The clamp-free restatement of `energyIdentity_classical_unconditional`: the LHS
`s ↦ ‖(velocityField … (projIcc … s)).toLp‖²` becomes `s ↦ l2Sq (slice u s)` by
`norm_toLp_sq_eq_l2Sq` once the `projIcc` is the identity near `t`; the derivative value is
unchanged. -/
theorem energyIdentity_l2Sq (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => l2Sq (slice w.velocity s))
      (-2 * ν * (∫ x, ∑ i : Fin 3,
            ‖fderiv ℝ (slice w.velocity t) x (coordinateVector i)‖ ^ 2)
          + 2 * pairing (slice w.velocity t) (slice f t)) t := by
  have h := energyIdentity_classical_unconditional w hf ht
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds
      (show t ∈ Ioo (0 : ℝ) ((t + T) / 2) from ⟨ht.1, by linarith [ht.2]⟩)] with s hs
  have hsS : s ∈ Icc (0 : ℝ) ((t + T) / 2) := ⟨hs.1.le, hs.2.le⟩
  have hnn : (0 : ℝ) ≤ (t + T) / 2 := by linarith [ht.1, ht.2]
  rw [projIcc_of_mem hnn hsS]
  exact (norm_toLp_sq_eq_l2Sq
    (velocityField w (show (t + T) / 2 < T by linarith [ht.2]) ⟨s, hsS⟩)).symm

end NSFormalization.Section4.C01
