# Lane 187 report — canonical force-path time smoothness

## 1. Theorems proved (exact statements)

```lean
theorem forcePath_sobolevPath_contDiffOn
    (hf : D01.MemForceR f) (hS : 0 < S) (q : ℕ) :
    ContDiffOn ℝ ∞
      (extendPath S hS.le
        (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q))
      (Icc (0 : ℝ) S)
```

```lean
theorem forcePath_of_memForceR_smooth (hf : D01.MemForceR f) (hS : 0 < S) :
    ∃ F : Icc (0 : ℝ) S → SmoothL2Field Space,
      F = C01.forcePath hf ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm f ∧
      ∀ q (_hq : 6 ≤ q),
        ∀ hF : ∀ n, Continuous fun t => (F t).jetLp n,
        ContDiffOn ℝ ∞
          (extendPath S hS.le
            (sobolevPath F hF q))
          (Icc (0 : ℝ) S)
```

The fixed reconstruction is exposed as

```lean
def datumSobolevCLM (q : ℕ) :
    RealVectorSobolev (q : ℝ) →L[ℝ] SobolevSpace 1 q
```

with the identification theorem

```lean
theorem datumSobolevCLM_eq_ordinarySobolev (q : ℕ) (A : SmoothL2Field Space)
    (G : RealVectorSobolev (q : ℝ)) (hG : IsSobolevDatum (q : ℝ) A.field G) :
    datumSobolevCLM q G = ordinarySobolev q A.toLp A.translation_contDiff
```

## 2. Files and what Lean now has

- `formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean`: bounded-linear datum-to-jet,
  datum-to-array, and datum-to-cylinder reconstruction; Schwartz-density compatibility; the exact
  `hfs` consumer theorem; and the extended force package.
- `research/A01/axioms_hfs.lean`: all 17 declarations audited to exactly
  `[propext, Classical.choice, Quot.sound]`, plus inhabited `f := 0`, `S := 1` examples using
  `A04.memForceR_zero`.
- `research/A01/ATTEMPTS_HFS.md`: successful construction and the rejected projection route.
- `research/A01/B1_LADDER.md`: R3/R4 now records the canonical force-side `hfs` input as discharged.

The proof works at every `q`; the consumer's `6 ≤ q` premise is unnecessary.

## 3. Remaining gaps / error text

This lane closes only force-side hfs; current integration now supplies common-horizon/cross-order R3 via lanes 178/186/188 given the all-order bounds, while the joint smooth representative and B2 joint pressure-gradient regularity remain.

The rejected orthogonal-projection draft failed with:

```text
failed to synthesize instance of type class
  InnerProductSpace ℝ (SobolevWord q → ↥(LiftL2 1))
```

It was replaced by a proof that the ambient reconstruction already lies in the closed Sobolev
subspace.  There are no errors in the delivered files.

The package's final clause quantifies the `hF` proof explicitly because `And` is nondependent and
cannot pass the proof in its earlier continuity conjunct as the proof argument of `sobolevPath F`.
Consumers apply this final clause to the preceding continuity proof; proof irrelevance removes any
dependence on the proof term.

## 4. Commands run

Final gate results are recorded after running:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForcePathSmooth
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ForcePathSmooth.lean
cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_hfs.lean
make check
```

All four commands exited `0`.  The direct module check produced zero bytes.  The axiom audit printed
only the required three axioms for every declaration, and `make check` passed all four repository
checks.  The exact `lake build` command replayed warnings already stored on imported dependency
facets (for example `FiniteHilbertBochner` and vendor modules); it emitted no warning from
`ForcePathSmooth.lean` and completed successfully.
