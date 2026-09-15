import NSFormalization.Section4.A02.Restrict

/-!
# A02 unit U6: the order theory of `T^ν_{max,R}`

`research/A02/COMPARISON.md` §3 unit **U6**: the six order-theoretic fields of
`MaximalSolutionAPI` (`research/A02/Spec.lean`), transcribed from
`NSFormalization/Source/SmoothLifespan.lean:44,48,58,101` with `Flow` replaced
by the manuscript's `ClassicalSolutionR`.

| here | spec field | source |
|---|---|---|
| `horizon_le_lifespan_of_localSolution` | `horizon_le_lifespan` (`Spec.lean:372-375`) | `SmoothLifespan.lean:44` |
| `lifespan_le_iff` | `lifespan_le_iff` (`Spec.lean:443-446`) | `:48` |
| `lifespan_le_iff_no_extension` | `lifespan_le_iff_no_extension` (`Spec.lean:451-455`) | `:58` |
| `lifespan_ge_of_forall_shorter` | `lifespan_ge_of_forall_shorter` (`Spec.lean:463-466`) | `:101` |
| `regularThrough_iff` | `regularThrough_iff` (`Spec.lean:476-478`) | gap; backward half uses U4 |
| `referenceLifespan` | `referenceLifespan` (`Spec.lean:500-504`) | gap; uses U4 |

Each of the six is stated with the spec field's own argument order, so a
`verification/Bindings` module can discharge the contract field by `exact` once
the two copies of `ClassicalSolutionR` are bridged.

Every proof is structure-agnostic: only `Nonempty (ClassicalSolutionR ν a f S)`,
`horizon_pos`, the `iSup` shape of `maximalLifespanR` and — for the last two —
`ClassicalSolutionR.restrict` of unit **U4** are used.  No analytic input, no
Sobolev estimate, no uniqueness.

**A01 is not assumed.**  The spec field `horizon_le_lifespan` quantifies over
`MaximalSolutionAPI.horizon` and rests on `⟪A01:LocalTheoryAPI.solution⟫`
(`research/A02/Spec.lean:318-321`).  That hypothesis is taken here as an
explicit argument `localSolution`, so the implication is available before A01
lands; instantiating it at A01's `LocalTheoryAPI` gives the field verbatim.
-/

noncomputable section

namespace NSFormalization.Section4.A02

open Set
open scoped ENNReal

/-! ## 1. `horizon_le_lifespan` -/

/-- `Source/SmoothLifespan.lean:44` on the manuscript's class: every realized
horizon is below the maximal lifespan.  This is the whole order-theoretic
content of the spec field; A01 only supplies the horizon. -/
theorem horizon_le_lifespan {ν S : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (u : ClassicalSolutionR ν a f S) :
    ENNReal.ofReal S ≤ maximalLifespanR ν a f :=
  le_iSup_of_le S (le_iSup_of_le ⟨u⟩ le_rfl)

/-- **Spec field `MaximalSolutionAPI.horizon_le_lifespan`**
(`research/A02/Spec.lean:372-375`), with ⟪A01:LocalTheoryAPI.solution⟫
(`Spec.lean:318-321`) as an explicit hypothesis rather than an assumption. -/
theorem horizon_le_lifespan_of_localSolution
    {horizon : ℝ → SpatialField → SpaceTimeField → ℝ}
    (localSolution : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ClassicalSolutionR ν a f (horizon ν a f)) :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanR ν a f :=
  fun ν a f hν ha hf => horizon_le_lifespan (localSolution ν a f hν ha hf)

/-! ## 2. `lifespan_le_iff` and `lifespan_le_iff_no_extension` -/

/-- **Spec field `MaximalSolutionAPI.lifespan_le_iff`**
(`research/A02/Spec.lean:443-446`); `Source/SmoothLifespan.lean:48`. -/
theorem lifespan_le_iff (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (hT : 0 ≤ T) :
    maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
      ∀ S : ℝ, Nonempty (ClassicalSolutionR ν a f S) → S ≤ T := by
  constructor
  · intro h S hS
    exact (ENNReal.ofReal_le_ofReal_iff hT).mp
      ((horizon_le_lifespan hS.some).trans h)
  · intro h
    exact iSup_le fun S => iSup_le fun hS => ENNReal.ofReal_le_ofReal (h S hS)

/-- **Spec field `MaximalSolutionAPI.lifespan_le_iff_no_extension`**
(`research/A02/Spec.lean:451-455`); `Source/SmoothLifespan.lean:58`. -/
theorem lifespan_le_iff_no_extension (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (T : ℝ) (hT : 0 ≤ T) :
    maximalLifespanR ν a f ≤ ENNReal.ofReal T ↔
      ∀ S : ℝ, T < S → IsEmpty (ClassicalSolutionR ν a f S) := by
  rw [lifespan_le_iff ν a f T hT]
  constructor
  · intro h S hTS
    exact ⟨fun u => (not_lt_of_ge (h S ⟨u⟩)) hTS⟩
  · intro h S hS
    by_contra hST
    exact (h S (lt_of_not_ge hST)).false hS.some

/-! ## 3. `lifespan_ge_of_forall_shorter` -/

/-- **Spec field `MaximalSolutionAPI.lifespan_ge_of_forall_shorter`**
(`research/A02/Spec.lean:463-466`); `Source/SmoothLifespan.lean:101`. -/
theorem lifespan_ge_of_forall_shorter (ν : ℝ) (a : SpatialField)
    (f : SpaceTimeField) (T : ℝ) (hT : 0 < T)
    (hshort : ∀ b : ℝ, 0 < b → b < T → Nonempty (ClassicalSolutionR ν a f b)) :
    ENNReal.ofReal T ≤ maximalLifespanR ν a f := by
  apply le_of_forall_lt
  intro c hc
  have hc_top : c ≠ (⊤ : ℝ≥0∞) := hc.ne_top
  have hcT : c.toReal < T := ENNReal.toReal_lt_of_lt_ofReal hc
  have hc0 : (0 : ℝ) ≤ c.toReal := ENNReal.toReal_nonneg
  obtain ⟨u⟩ := hshort ((c.toReal + T) / 2) (by linarith) (by linarith)
  have hcb : c < ENNReal.ofReal ((c.toReal + T) / 2) := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt hc_top]
    linarith
  exact hcb.trans_le (horizon_le_lifespan u)

/-! ## 4. `regularThrough_iff` and `referenceLifespan`

The backward half of the equivalence and both margins of `referenceLifespan`
use `ClassicalSolutionR.restrict` (unit **U4**) to shrink a realized horizon.
The in-tree `Flow` analogue `SmoothLifespan.bad_or_regular_reference` (`:70`) is
only the forward half in disjunctive form. -/

/-- A strict lifespan inequality produces a *realized* horizon strictly above
`T`.  This unpacks the double `iSup` of `maximalLifespanR` and is the only place
where the supremum is entered from below. -/
theorem exists_horizon_gt_of_lt_lifespan {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (hT : 0 ≤ T)
    (h : ENNReal.ofReal T < maximalLifespanR ν a f) :
    ∃ S : ℝ, T < S ∧ Nonempty (ClassicalSolutionR ν a f S) := by
  simp only [maximalLifespanR, lt_iSup_iff] at h
  obtain ⟨S, hne, hTS⟩ := h
  exact ⟨S, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT).mp hTS, hne⟩

/-- **Spec field `MaximalSolutionAPI.regularThrough_iff`**
(`research/A02/Spec.lean:476-478`): "regular through `T`" and "`T` is strictly
below the maximal lifespan" are the same condition. -/
theorem regularThrough_iff (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (hT : 0 < T) :
    RegularThrough ν a f T ↔ ENNReal.ofReal T < maximalLifespanR ν a f := by
  constructor
  · rintro ⟨δ, hδ, ⟨u⟩⟩
    refine lt_of_lt_of_le ?_ (horizon_le_lifespan u)
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  · intro h
    obtain ⟨S, hTS, ⟨u⟩⟩ := exists_horizon_gt_of_lt_lifespan hT.le h
    exact ⟨(S - T) / 2, by linarith, u.nonempty_restrict (by linarith) (by linarith)⟩

/-- **Spec field `MaximalSolutionAPI.referenceLifespan`**
(`research/A02/Spec.lean:500-504`): a `RegularThrough` hypothesis is upgraded to
one margin `δ` that simultaneously carries a solution on `[0,T+δ)`, a *strictly*
longer realized horizon — which is what puts the reference's smoothness on the
closed `Icc 0 (T+δ)` of `research/section4/STATEMENTS.md:332` — and the strict
lifespan inequality R42 declares. -/
theorem referenceLifespan (ν : ℝ) (a : SpatialField) (g : SpaceTimeField)
    (T : ℝ) (hT : 0 < T) (h : RegularThrough ν a g T) :
    ∃ δ : ℝ, 0 < δ ∧ Nonempty (ClassicalSolutionR ν a g (T + δ)) ∧
      (∃ S : ℝ, T + δ < S ∧ Nonempty (ClassicalSolutionR ν a g S)) ∧
      ENNReal.ofReal (T + δ) < maximalLifespanR ν a g := by
  obtain ⟨δ₀, hδ₀, ⟨u⟩⟩ := h
  refine ⟨δ₀ / 2, by linarith, u.nonempty_restrict (by linarith) (by linarith),
    ⟨T + δ₀, by linarith, ⟨u⟩⟩, ?_⟩
  refine lt_of_lt_of_le ?_ (horizon_le_lifespan u)
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)

end NSFormalization.Section4.A02
