# T19 U7/U8/U9 attempts

This file records unsuccessful proof approaches for
`Section3/T19/DensityEngine.lean`, including Lean's exact diagnostics.

## Attempt 1: first build of the mixed-limit proof

The first draft used the wrong calligraphic Unicode character for the
neighbourhood notation. Command:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.DensityEngine
```

Exact errors:

```text
error: NSFormalization/Section3/T19/DensityEngine.lean:100:11: unexpected token '>'; expected ':' or term
error: NSFormalization/Section3/T19/DensityEngine.lean:86:56: Unknown identifier `𝒩`
error: NSFormalization/Section3/T19/DensityEngine.lean:86:62: Unknown identifier `𝒩`
error: NSFormalization/Section3/T19/DensityEngine.lean:89:62: Unknown identifier `𝒩`
error: NSFormalization/Section3/T19/DensityEngine.lean:89:68: Unknown identifier `𝒩`
error: NSFormalization/Section3/T19/DensityEngine.lean:95:9: Unknown identifier `𝒩`
error: NSFormalization/Section3/T19/DensityEngine.lean:95:15: Unknown identifier `𝒩`
error: NSFormalization/Section3/T19/DensityEngine.lean:100:9: Unknown identifier `𝒩`
```

Resolution attempted: replace `𝒩` with another visually similar
calligraphic character.  Attempt 2 records why that first correction was still
not the registered notation.

## Attempt 2: second Unicode correction

The first replacement was still a visually similar but unregistered character.
Exact errors:

```text
error: NSFormalization/Section3/T19/DensityEngine.lean:86:56: expected token
error: NSFormalization/Section3/T19/DensityEngine.lean:86:17: type expected, got
  (Tendsto (fun ε => ε ^ alphaT p q) ?m.200 : Filter ℝ → Prop)
```

Resolution: byte-check the notation in `Threading.lean` and use U+1D4DD
(`𝓝`, UTF-8 `f0 9d 93 9d`).

## Attempt 3: simplify the mixed zero difference

`simp only [sub_self, torusMixedLebesgueENormT_zero]` did not identify the
lambda-valued zero with the typed zero function. Exact error:

```text
error: NSFormalization/Section3/T19/DensityEngine.lean:74:4: Type mismatch: After simplification, term
  hr
 has type
  0 < r
but is expected to have type
  (mixedLebesgueENormT q p fun z => 0) < r
```

Resolution: prove `(fun z => g z - g z) = (0 : SpaceTimeField)` by
function extensionality before rewriting with `torusMixedLebesgueENormT_zero`.

## Attempt 4: projection syntax as a probe type

The first conformance probe tried to use record field projections themselves
as types. Lean correctly treated each projection as a function from the
record, rather than as its result type. Exact errors:

```text
../research/T19/probes/density_engine_closes.lean:5:10: error: type expected, got
  (PeriodicDensityAPI.fixedInitialDensity : PeriodicDensityAPI →
  ∀ a ∈ T10.initialClassT,
    ∀ (ν : ℝ),
      0 < ν → ∀ (T : ℝ), 0 < T → ∀ s < 1 / 2, T10.RelativelyDenseT 1 s T10.forceClassT (T10.breakdownSetT ν a T))
../research/T19/probes/density_engine_closes.lean:8:10: error: type expected, got
  (PeriodicDensityAPI.regularReferenceSingular : PeriodicDensityAPI →
  ∀ a ∈ T10.initialClassT,
    ∀ (ν : ℝ),
      0 < ν →
        ∀ (T : ℝ),
          0 < T →
            ∀ g ∈ T10.forceClassT,
              T10.RegularThroughT ν a g T →
                ∀ s < 1 / 2,
                  ∀ (r : ENNReal),
                    0 < r →
                      ∃ f ∈ T10.forceClassT,
                        (T10.forceSobolevENormT 1 s fun z => f z - g z) < r ∧
                          T10.maximalLifespanT ν a f = ENNReal.ofReal T)
../research/T19/probes/density_engine_closes.lean:11:10: error: type expected, got
  (MixedRegionAPI.mixedDensity : MixedRegionAPI →
  ∀ a ∈ T10.initialClassT,
    ∀ (ν : ℝ),
      0 < ν →
        ∀ (T : ℝ),
          0 < T →
            ∀ (p q : ENNReal) [inst : Fact (1 ≤ p)],
              1 ≤ q →
                3 < 3 / p.toReal + 2 / q.toReal → RelativelyDenseMixedT q p T10.forceClassT (T10.breakdownSetT ν a T))
```

Resolution: copy the three canonical field result types literally and close
each example with `exact fixedInitialDensity`, `exact
regularReferenceSingular`, or `exact mixedDensity`.
