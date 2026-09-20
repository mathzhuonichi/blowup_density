# Lane 165 report — A05 critical `L³` embedding

## 1. Theorems proved: names, statements, and constants

All names below are in `NSFormalization.Section4.A05`.

The local datum norm is

```lean
def dotHomogeneousENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  ⨅ G : {G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}, ‖G.1‖ₑ
```

It is the datum-form definition copied from `research/R43/Spec.lean`, pending
D01's canonical definition.  It is not `Contracts.V1.Data.dotHHalfENorm`.

The explicit constants are

```lean
def scalarCriticalConst (a : ℝ) : ℝ :=
  RieszKernelNormalization.coefficient a *
    (potentialConstant a * (512 : ℝ) ^ (1 / targetExponent a))

def criticalL3Const : ℝ := 3 * scalarCriticalConst (1 / 2)
```

with proved positivity

```lean
scalarCriticalConst_pos {a} (ha : 0 < a) (ha3 : a < 3 / 2) :
  0 < scalarCriticalConst a

criticalL3Const_pos : 0 < criticalL3Const
```

The requested final theorem is exactly

```lean
theorem velocityCriticalL3
    (z : NSFormalization.Section4.A02.SpatialField)
    (hz : NSFormalization.Section4.A02.MemHInfty z) :
    eLpNorm z 3 volume ≤
      ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1 / 2) z
```

The carrier and normalization lemmas are:

```lean
cyclesHomogeneousDatum_norm (G : FourierData) :
  ‖cyclesHomogeneousDatum G‖ = ‖G‖

cyclesHomogeneousDatum_ae (G : FourierData) :
  (cyclesHomogeneousDatum G : X → ℂ) =ᵐ[volume]
    fun ξ => frequencyUnit ^ (3 / 2 : ℝ) • G (frequencyUnit • ξ)

u2_normalizedMultiplier_cyclesDatum
    {a} (ha : 0 ≤ a) (ha3 : a < 3 / 2)
    (hG : IsHomogeneousDatum a G U) :
  normalizedMultiplier a ha ha3 (cyclesHomogeneousDatum G) =
    FourierTransform.fourier U

u1_dotHomogeneousENorm_eq
    (hA : IsHomogeneousSliceDatum s z A) :
  dotHomogeneousENorm s z = ‖A‖ₑ

u3_fourier_criticalInputFromDatum (G : FourierData) :
  FourierTransform.fourier (criticalInputFromDatum G) =
    cyclesHomogeneousDatum G

u3_norm_criticalInputFromDatum (G : FourierData) :
  ‖criticalInputFromDatum G‖ = ‖G‖
```

The scalar completion lemmas, for `0 < a < 3/2`, are:

```lean
u6_normalizedCriticalRealization_norm_le (G : FourierData) :
  ‖normalizedCriticalRealization ha ha3 G‖ ≤
    scalarCriticalConst a * ‖G‖

u6_normalizedCriticalRealization_toDistribution
    (hG : IsHomogeneousDatum a G U) :
  (normalizedCriticalRealization ha ha3 G : TemperedDistribution X ℂ) = U

u6_scalar_eLpNorm_le
    (hf : MemLp f 2 volume)
    (hU : ∀ ψ, U ψ = ∫ x, ψ x * f x)
    (hG : IsHomogeneousDatum a G U) :
  eLpNorm f (ENNReal.ofReal (targetExponent a)) volume ≤
    ENNReal.ofReal (scalarCriticalConst a) * ‖G‖ₑ
```

The vector/ENNReal packaging lemmas are:

```lean
u7_targetExponent_half :
  ENNReal.ofReal (targetExponent (1 / 2 : ℝ)) = 3

u7_norm_le_sum_coordinates (x : X) :
  ‖x‖ ≤ ∑ i : Fin 3, ‖((x i : ℝ) : ℂ)‖

u7_memLp_components_of_memHInfty (hz : MemHInfty z) :
  ∀ i : Fin 3, MemLp (fun x => ((z x i : ℝ) : ℂ)) 2 volume

u7_component_eLpNorm_le ... (i : Fin 3) :
  eLpNorm (fun x => ((z x i : ℝ) : ℂ)) 3 volume ≤
    ENNReal.ofReal (scalarCriticalConst (1 / 2)) * ‖G i‖ₑ

u7_vector_eLpNorm_le_components ... :
  eLpNorm z 3 volume ≤
    ∑ i : Fin 3, eLpNorm (fun x => ((z x i : ℝ) : ℂ)) 3 volume

u7_component_sum_le (G : RealVectorSobolev (1 / 2 : ℝ)) :
  ∑ i : Fin 3,
      ENNReal.ofReal (scalarCriticalConst (1 / 2)) * ‖G i‖ₑ ≤
    ENNReal.ofReal criticalL3Const * ‖G‖ₑ

u7_vector_eLpNorm_le_of_datum
    (hz : MemHInfty z)
    (hG : IsHomogeneousSliceDatum (1 / 2 : ℝ) z G) :
  eLpNorm z 3 volume ≤ ENNReal.ofReal criticalL3Const * ‖G‖ₑ
```

The factor `3` is explicit and comes only from the deliberately crude
three-coordinate `ℓ² ≤ ℓ¹` packaging.  No claim of sharpness is made.

## 2. What is in Lean now

`formalization/NSFormalization/Section4/A05/CriticalL3.lean` contains the full
proof of the requested datum-form critical embedding.  The proof:

1. uses D01's homogeneous datum uniqueness to evaluate the infimum;
2. transports angular data to the cycles convention with the correct
   `frequencyUnit` dilation;
3. realizes the cycles datum as an `L²` inverse Fourier transform;
4. applies `Source.FractionalRealization` and identifies the completed
   representative with the original distribution;
5. packages the three real components into the vector estimate; and
6. treats absence of a homogeneous datum by the honest value `⊤`.

`research/A05/axioms_critical_l3.lean` audits all nineteen exported theorems.
Every theorem prints exactly
`[propext, Classical.choice, Quot.sound]`.  The same file constructs the
concrete field

```lean
x ↦ Cut.bump x • coordinateVector 0
```

and proves it smooth, compactly supported, datum-form `MemHInfty`, and nonzero,
then applies `velocityCriticalL3` to it.  The five named witness theorems also
print exactly the standard three axioms, and the requested `example` elaborates.

No contract is registered in this lane.  The local norm is documented for
replacement once D01's canonical norm lands.

## 3. Gaps, per unit

| unit | status | remaining gap |
|---|---|---|
| U1 | closed | None for this lane; the infimum is attained at every order whenever a datum exists. |
| U2 | closed for this route | The exact direction and normalization used by the Riesz completion are proved. |
| U3 | partial | Physical inverse-transform and Plancherel from an existing homogeneous datum are proved.  The independent `homogeneousLeSobolev` constructor from an inhomogeneous datum, and its separate `s=3/2` endpoint producer, remain. |
| U4 | open, unused | Full `IsRieszPower` existence and norm preservation from `research/A05/Spec.lean:300-315`, including `a=3/2`. |
| U5 | open, unused | Full `IsBesselPower` existence and norm preservation from `research/A05/Spec.lean:318-331`. |
| U6 | closed | Scalar completion estimate and distribution identification for every `0<a<3/2`. |
| U7 | closed for requested theorem | The order-half vector velocity clause is complete.  The broader original row's unused `a=1` `embeddingPair` and separately named `criticalRepresentative` wrappers are not delivered. |

The final `velocityCriticalL3` theorem does not depend on U4 or U5.  Details and
the recorded failed diagnostics are in `ATTEMPTS_CRITICAL_L3.md`.

## 4. Commands and results

All commands ran inside this worktree with `scripts/lean-env.sh` sourced; every
`lake` command ran from `verification/`.

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A05.CriticalL3
```

Exit 0.  Lake replayed pre-existing warnings from imported modules; the target
itself emitted no warning and finished `Built ...CriticalL3` successfully.

```text
lake env lean ../formalization/NSFormalization/Section4/A05/CriticalL3.lean
```

Exit 0, exactly 0 output bytes.

```text
lake env lean ../research/A05/axioms_critical_l3.lean
```

Exit 0, no warnings; every one of the 24 printed theorem audits is exactly
`[propext, Classical.choice, Quot.sound]`.

```text
make check
```

Exit 0.  The architecture, contract-policy, and work-queue checks passed.  Its
informational plan JSON reports the branch's pre-existing
`source_hashes_match: false` and copied-source admission-token inventory; these
are not failures and this lane changes no copied source or contract.

```text
git diff --check
```

Exit 0.  The two new Lean files contain none of `sorry`, `admit`, `axiom`, or
`native_decide`, and no declaration-local heartbeat override is needed.
