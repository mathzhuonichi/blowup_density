# Lane 167 report — A01 consumer-facing force bridge (review rework)

## 1. Exact final statements

```lean
def forceOfPath {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space) :
    A02.SpaceTimeField

@[simp] theorem forceOfPath_apply {S : ℝ}
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (t : Icc (0 : ℝ) S) (x : Space) :
    forceOfPath F (t.1, x) = (F t).field x

theorem forceOfPath_forcePath_eq_on_horizon {S : ℝ} {f : A02.SpaceTimeField}
    (hf : D01.MemForceR f) (t : Icc (0 : ℝ) S) (x : Space) :
    forceOfPath (C01.forcePath (S := S) hf) (t.1, x) = f (t.1, x)

theorem forcePath_of_memForceR {S : ℝ} {f : A02.SpaceTimeField}
    (hf : D01.MemForceR f) :
    ∃ F : Icc (0 : ℝ) S → SmoothL2Field Space,
      F = C01.forcePath hf ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm f

theorem initialClassR_of_smoothL2 {q : ℕ}
    (u : SobolevSpace 1 (q + 1))
    (U : EulerMeanSolenoidal.L2)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 (q + 1) (0, θ) u = u)
    (hU : ordinaryLift U = value 1 u)
    (hdiv : value 1 u ∈ divergenceFreeSpace 1 1 0)
    (a : SmoothL2Field Space)
    (ha : a.field =ᵐ[volume] ⇑U) :
    a.field ∈ A02.initialClassR
```

## 2. What is in Lean now

Row (v) is oriented in the constructor's consumer direction.  Given the paper's global force `f`
and `hf : MemForceR f`, `forcePath_of_memForceR` returns the canonical cylinder carrier
`F := C01.forcePath hf`, its jet continuity from `C01.forcePath_jetLp_continuous hf`, and
`A04.MemL1Hm f` from `A04.memL1Hm_of_memForceR hf`.  The constructor retains `f' := f` and the
original `hf`; it does not invent a global force from a finite path.

`forceOfPath` is retained only to express the exact pointwise comparison on `Icc 0 S`.
`forceOfPath_forcePath_eq_on_horizon` proves that reading the canonical carrier gives the original
physical slice.  No smoothness or force-class membership is asserted for its zero extension.

`ForcePathSmoothness` and every theorem depending on it were deleted.  The reviewer probe exhibits
a concrete nonzero `f ∈ F_R` for which zero-extending `C01.forcePath hf` jumps at `t = S`, so that
premise is false in general.  The dead `hF` argument from the old carrier-to-global theorem is gone.

`initialClassR_of_smoothL2` now imports lane 162's
`Section4/A01/ConstructorDivergence.lean`.  It takes the actual cylinder hypotheses required by
`divergence_ae_of_cylinder`, uses that theorem to obtain a.e. coordinate divergence zero for the
smooth representative `a`, and upgrades the equality to pointwise by continuity.  Pointwise
divergence is no longer assumed as though it came directly from the cylinder pair.

## 3. Gaps

There is no remaining force-interface gap in row (v): the canonical path, its `hF`, the retained
global `hf`, `MemL1Hm f`, and pointwise on-horizon identity are all available.

`forceOfPath F` is generally not a global member of `F_R`; for a nonzero endpoint it is not even
continuous at `S`.  This is deliberate and is no longer presented as a constructor route.  A
carrier-to-global theorem for arbitrary `F` would require a separately supplied smooth extension
with endpoint compatibility.

The full mild-to-classical constructor must still provide the cylinder data used by the initial
bridge.  For time-dependent candidate velocity slices it must also provide lane 162's `Z`,
`hslice`, and c3 spatial-`ContDiff` hypotheses.  This report does not claim those handoffs follow
from `divergenceFreeSpace` alone.

## 4. Commands and results

- `LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForceBridge` — passed; the target was
  silent and Lake completed successfully.
- `LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ForceBridge.lean`
  — passed with exactly zero output.
- `LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_force_bridge.lean` — passed.  All five
  declarations printed exactly `[propext, Classical.choice, Quot.sound]`; the nonzero force and
  inhabited cylinder examples compiled.
- `make check` — passed.
