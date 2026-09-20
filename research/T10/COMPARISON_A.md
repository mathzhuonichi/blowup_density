# T10 draft A comparison

This is an independent statement draft for the future
`Contracts/V1/TorusData.lean`. It follows the fixed Section 3 decision: physical
fields remain unit-periodic functions on `R^3`, while Sobolev analysis is done
on weighted discrete Fourier data.

## Paper notion to Lean definition

| Paper notion | Source | Draft A definition | Quantifiers / representation |
|---|---|---|---|
| Unit torus and lattice | `01-introduction.tex:9-11,83-90` | `PeriodicTorus`, `PeriodicFrequency` | `UnitAddTorus (Fin 3)` and `Fin 3 -> Z` |
| Physical periodic field | `02-preliminaries.tex:28` | `IsPeriodicSpatial`, `IsPeriodicSpaceTimeOn` | For every physical point and every integer lattice vector; solution periodicity is required only for every time in `[0,T)` |
| `H^s(T^3;R^3)` coefficient carrier | `01-introduction.tex:83-103`; `03-torus.tex:1-4` | `PeriodicSobolev s` | `lp (fun _ : Fin 3 -> Z => EuclideanSpace C (Fin 3)) 2`; `s` is a phantom index because the weight is stored in the datum |
| `(1+4 pi^2 |k|^2)^(s/2)` | `01-introduction.tex:76-89` | `periodicFrequencyWeight`, `periodicSobolevWeight` | `1 + 4*pi^2*sum_i k_i^2`, followed by `Real.rpow _ (s/2)` |
| Fourier coefficient `zhat(k)` | `01-introduction.tex:83-90` | `torusRepresentative`, `torusLift`, `periodicFourierCoeffT` | Componentwise `UnitAddTorus.mFourierCoeff (torusLift f) k`; this is exactly the convention of `Paper1/TorusCube.periodicFourierCoeff` |
| Physical field to weighted datum | `01-introduction.tex:83-103` | `IsPeriodicDatum s z A` | Periodicity, componentwise integrability, `forall k, A k = weight(s,k) • zhat(k)`, then conjugate reflection `forall k i` |
| `||z||_(H^s(T^3))` | `01-introduction.tex:83-103` | `periodicSobolevENorm` | Infimum over the subtype of all representing data; empty infimum is `top` |
| Spatial mean | `03-torus.tex:395-407` | `meanT` | Haar integral of the canonical torus lift, component by component |
| Mean-zero space and decomposition | `01-introduction.tex:105-109`; `03-torus.tex:395-414` | `PeriodicMeanZero`, `periodicMeanMode`, `periodicMeanZeroPart`, `periodicMeanDecomposition`; physical `meanPartT`, `meanZeroPartT` | Mean-zero means exactly `A 0 = 0`; the decomposition is zero mode plus its complement |
| Periodic Leray projector | `02-preliminaries.tex:75-83` | `solenoidalFiber`, `periodicLeraySymbol`, `periodicLerayProjector` | At each `k`, orthogonal projection onto the orthogonal complement of `span{k}`; this is identity at zero and `I-k tensor k/|k|^2` otherwise |
| Solenoidal coefficients | `02-preliminaries.tex:75-83` | `IsSolenoidalDatum` | `forall k, sum_i k_i A_i(k) = 0`; the zero-mode condition is vacuous |
| Pressure gauge | `02-preliminaries.tex:28,84-88` | `pressureMeanT`, `HasZeroPressureMeanT` | `forall t in I`, the torus lift is integrable and its integral is zero |
| `X_T` | `02-preliminaries.tex:7-15` | `initialClassT` | Globally smooth, unit-periodic physical fields whose pointwise divergence vanishes everywhere |
| `F_T` | `02-preliminaries.tex:7-10,22-26` | `HasCompactPositiveTimeSupportT`, `forceClassT` | Globally smooth periodic lifts; `exists` a compact time set `K subset (0,infinity)` outside which every spatial slice is zero |
| `L^q_t H^s_x` force norm | `01-introduction.tex:118-140`; `03-torus.tex:6-14` | `IsPeriodicSobolevPath`, `periodicBochnerDatumENorm`, `forceSobolevENormT` | Infimum over strongly measurable coefficient paths representing every slice at every `t >= 0`; time measure is Lebesgue restricted to `(0,infinity)` |
| Classical periodic solution | `02-preliminaries.tex:28-36,105-114` | `ClassicalSolutionT nu a f T` | Positive `T`; smoothness on `[0,T) x R^3`; periodicity on `[0,T)`; pressure mean zero at every such time; initial condition; divergence on `[0,T)`; momentum on `(0,T)`; continuous integer-order datum paths |
| Maximal lifespan | `02-preliminaries.tex:32-36` | `maximalLifespanT` | `sup S`, then `sup` over `Nonempty (ClassicalSolutionT nu a f S)`, of `ENNReal.ofReal S` |
| Regular through `T` | `02-preliminaries.tex:34-36` | `RegularThroughT` | `exists delta, 0 < delta` and a solution with horizon `T+delta` |
| `B_(nu,a,T)` and `B^0_(nu,T)` | `02-preliminaries.tex:38-46` | `breakdownSetT`, `breakdownSetTZero` | Force lies in `forceClassT` and `maximalLifespanT nu a f <= ofReal T` |
| Relative norm density | `01-introduction.tex:137-140`; `03-torus.tex:6-14` | `RelativelyDenseT q s Y S` | `forall g, g in Y -> forall r>0, exists f, f in S and distance(f,g)<r`, using the force norm of `f-g` |
| `E_T` | `01-introduction.tex:141-150`; `03-torus.tex:299,542-561` | `periodicGradientDatumENorm`, `periodicGradientENorm`, `energyEssSupT`, `energyGradientT`, `energyENormT` | Coefficient-side `L^infinity(0,T;l^2)` plus `L^2(0,T; (sum_k 4 pi^2 |k|^2 |A(k)|^2)^(1/2))`; no endpoint value at `T` |

## Choices fixed in draft A

- **Weight normalization.** The torus is `R^3/Z^3`, not a `2*pi`-periodic
  torus. The exact Bessel weight is therefore
  `(1 + 4*pi^2*|k|^2)^(s/2)`. The squared datum norm yields the paper's
  exponent `s`.

- **Complex versus real coefficients.** Fourier coefficients are complex
  three-vectors because that is the natural Mathlib Fourier carrier. The
  physical fields are real. `IsPeriodicDatum` explicitly requires
  `A(-k)_i = star (A(k)_i)`, so every admitted datum is the complex encoding of
  a real vector field. The raw `PeriodicSobolev s` carrier is not restricted to
  the real closed subspace; this keeps the carrier literally an `lp` space and
  makes Mathlib's Hilbert projection available. Later contracts should quantify
  over represented data or add a bundled real closed subspace if they need to
  quantify over arbitrary data.

- **Placement of the weight.** `PeriodicSobolev s` is the same complete `lp`
  type for every `s`; `A(k)` is the already-weighted coefficient. This exactly
  mirrors D01's datum architecture and makes its norm the `H^s` norm. It also
  means that coefficient operators acting on an order-`s` datum act after the
  weight.

- **Vector arrangement.** The three-vector is inside `lp`, one Euclidean
  complex vector per frequency. This is canonically isometric to three scalar
  `lp` components and directly implements “sum the squared component norms.”

- **Fourier bridge.** The draft rewrites the canonical representative and
  torus lift from `Paper1/TorusCube.lean`, then calls Mathlib's
  `UnitAddTorus.mFourierCoeff`. It does not import a local module, preserving the
  future contract import rule. A binding should identify these definitions
  with `NSFormalization.Paper1.torusLift` and `periodicFourierCoeff`.

- **Physical periodicity.** `z(x+n)=z(x)` is stated for every `x` and every
  `n : Z^3`. Initial data and forces are periodic globally. A classical
  solution's velocity and pressure are required to be periodic only for
  `t in [0,T)`, so arbitrary values of the total Lean functions outside their
  lifespan do not affect membership.

- **Datum totalization.** The Fourier integral is accompanied by explicit
  componentwise integrability. Thus a non-integrable physical field has no
  datum and `periodicSobolevENorm` is `top`, rather than acquiring zero
  coefficients from a totalized integral. Smooth periodic inputs satisfy this
  automatically.

- **Time slices.** A representing force path must agree at every `t >= 0`, not
  merely almost everywhere; its strong measurability is separately required
  before `eLpNorm` is taken. This follows the safe D01 convention and is
  equivalent on `forceClassT`.

- **Leray realization.** The symbol is defined as Hilbert orthogonal projection
  onto `span{k}^perp`. This handles `k=0` without division and supplies a genuine
  map `PeriodicSobolev s -> PeriodicSobolev s`. The coordinate formula is a
  lemma, rather than a division-by-zero branch inside the definition.

- **Pressure.** Zero mean is imposed at every time in `[0,T)`, including time
  zero. Integrability is included so the gauge is not satisfied through a
  totalized non-integrable integral.

- **Force support.** Compact support on the torus product becomes compact
  support only in time for the periodic lift to `R^3`; demanding compact
  spatial support of that lift would force it to vanish.

- **Classical solution structure.** `ClassicalSolutionT` is a new contract
  structure. It does not reuse a local periodic flow structure because the
  future `Contracts/V1` file may import only Mathlib/other contracts and because
  a structure cannot have an `rfl` bridge. Bindings will need fieldwise
  conversions and round-trip lemmas. Differential operators are stated in the
  draft itself with `fderiv`.

- **Energy.** `E_T` is coefficient-side. Its gradient term uses the homogeneous
  multiplier `4*pi^2*|k|^2` on the unweighted order-zero coefficient datum, so
  the zero mode contributes to the `L^2` term but not the dissipation term.
  Both time domains are the open interval `(0,T)`.

## Ambiguities and review points

1. The paper permits periodic distributions in general `H^s`, while the
   physical layer requested for T10 is a function layer. This draft bridges
   integrable physical functions only. That covers `X_T`, `F_T`, and classical
   solutions, but not every abstract negative-order periodic distribution.

2. The raw `PeriodicSobolev s` contains non-Hermitian complex data. Reality is
   part of `IsPeriodicDatum`, not the carrier. A real closed-subspace carrier
   would more closely imitate `RealVectorSobolev`, at the cost of more binding
   machinery and a less literal `lp` carrier.

3. `IsPeriodicDatum` redundantly asks for conjugate reflection after equating
   `A` with the Fourier coefficients of a real field. Keeping it explicit makes
   the real convention visible in the contract; it requires a routine Fourier
   reality lemma to show the class is inhabited.

4. `forceSobolevENormT` represents every nonnegative-time slice. The manuscript
   defines Bochner functions only almost everywhere. The stronger bridge is
   harmless for smooth forces but should be reviewed if the norm is later used
   on arbitrary measurable representatives.

5. `initialClassT` encodes smoothness and pointwise divergence, without an
   explicit “belongs to every Sobolev order” field. On a compact torus this is a
   theorem. Adding coefficient witnesses would mirror D01 more literally but
   duplicate a consequence of smooth periodicity.

6. `ClassicalSolutionT.sobolev` uses one continuous datum path on all `[0,T)`.
   This is local continuity, not a uniform bound up to `T`, but readers may
   prefer the paper's explicit “on every compact interval `[0,S]`, `S<T`”
   quantifier form.

7. The energy functions use a pointwise infimum over order-zero data before
   the time norm. Datum uniqueness should identify this with the measurable
   coefficient path of a classical field. For arbitrary pathological fields,
   measurability of the pointwise infimum is not included, so Mathlib's
   lower-integral totalization remains a caveat exactly as in D01's `E_T`.

8. The geometric Leray definition is mathematically the requested coordinate
   symbol but not definitionally written with division. If downstream
   coefficient calculations require rewriting by `rfl`, the contract could
   instead expose both the geometric map and a named coordinate-formula
   theorem.

9. The pressure and velocity are total Lean functions. Only smoothness,
   periodicity, the gauge, and equations on their lifespan are meaningful; no
   condition is placed outside `[0,T)`.

## Needs a lemma

- `torusRepresentative`/`torusLift` agree with
  `NSFormalization.Paper1.TorusCube.torusLift`, and `periodicFourierCoeffT`
  agrees componentwise with its `periodicFourierCoeff`.
- Scalar and vector Parseval/Plancherel: the order-zero datum norm is exactly
  the torus `L^2` norm, with the volume-one convention.
- `IsPeriodicDatum` uniqueness, and existence for every smooth periodic field
  at every real Sobolev order.
- Fourier reality: a real periodic physical field has conjugate-reflection
  coefficients; subtraction and the relevant multipliers preserve it.
- The zero coefficient equals `meanT`; `meanZeroPartT` has zero mean; and
  `A = periodicMeanMode s A + periodicMeanZeroPart s A` with the second term in
  `PeriodicMeanZero s`.
- The coordinate formula for `periodicLeraySymbol`: identity at `k=0` and
  `v_i - k_i (sum_j k_j v_j)/|k|^2` at `k != 0`.
- The Leray projector is complex-linear, self-adjoint, idempotent, a contraction
  in every `PeriodicSobolev s`, preserves Hermitian reality and the zero mode,
  maps into `IsSolenoidalDatum`, and fixes every solenoidal datum.
- Leray commutes with scalar Fourier weights, derivatives, and the periodic
  heat multiplier.
- Physical divergence-free fields correspond to `IsSolenoidalDatum`, including
  the converse for smooth represented fields.
- Pressure normalization by subtracting `pressureMeanT` preserves the pressure
  gradient and momentum equation, produces `HasZeroPressureMeanT`, and is
  unique among periodic representatives up to the chosen gauge.
- Smooth compact-time-supported periodic forces admit smooth, strongly
  measurable coefficient paths at every integer order; this identifies
  `forceClassT` with the existing `PeriodicForceSpace` interface.
- `periodicGradientDatumENorm` equals the physical `L^2` norm of the full
  spatial gradient; consequently `energyENormT` is the paper's physical
  `E_T` norm and is equivalent to the usual fixed-horizon
  `L^infinity_t L^2_x intersect L^2_t H^1_x` sum norm.
- The spatial mean obeys `m'(t) = meanT f(t)` along a classical solution; after
  the Galilean translation used in T11/T20, the mean-zero component solves the
  stated mean-free equation. In particular, mean-zero is preserved when the
  forcing has zero mean.
- Constant transport by the mean is skew-adjoint in `L^2` and commutes with all
  coefficient Sobolev multipliers.
- Fieldwise conversions between `ClassicalSolutionT` and the existing local
  periodic solution/flow structure, with both round trips.
- Local uniqueness makes `maximalLifespanT` coincide with the lifespan used by
  the existing periodic local theory and makes the breakdown predicate
  extensional in the force on nonnegative times.
