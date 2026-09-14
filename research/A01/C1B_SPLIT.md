# C1b — carrier-bridge sub-lemma split (lane 119, split-and-start)

Unit **C1b** of `research/A01/A01_SPLIT.md` (§c rows `c5`, `c6`, `c8`) and
`research/A01/COMPARISON.md` §3 (line 194): the order-by-order carrier bridge
between D01's angular Sobolev datum `IsSobolevDatum m z A` and the ordinary-`L²`
coordinate `EulerMeanSolenoidal.L2` produced by the forced local existence path
`NSFormalization.Source.OrdinaryForcedLocal.exists_local`
(`Source/OrdinaryForcedLocal.lean:32`), whose output
`U : C(Icc 0 T, EulerMeanSolenoidal.L2)` satisfies `U 0 = a.toLp`
(`:41`) and `∀ t, ordinaryLift (U t) = value 1 (u t)` (`:42`) for the abstract
cylinder Sobolev array `u : C(Icc 0 T, SobolevSpace 1 (q+1))`.

**What A01 needs from C1b** (rows c6/c8; c5's *pointwise* half is B1's, see
`C1b-rep`): for each order `m`, a **continuous** D01 datum path
`G : ℝ → RealVectorSobolev m` with `IsSobolevDatum m (velocity t) (G t)`, where
`velocity t` is the pointwise velocity of `ClassicalSolutionR`; C1b produces the
datum for the `L²` representative `⇑(U t)`, and the hand-off `velocity t =ᵐ ⇑(U t)`
(row `C1b-rep`, owned by B1) transfers it via `IsSobolevDatum.congr_field`.  C1b
also transports the divergence-free clause (`c6`).  A01's `A1` (tame product) is
A03's and needs a product estimate on the D01 carrier, **not** a carrier bridge —
it is not fed by any C1b row and is not promised here.

Size key (COMPARISON.md §3): **S** ≤ ~100 lines, no new machinery; **M** a
self-contained lemma with a known proof; **L** a multi-file campaign.
Status: **DONE** = proved and building this lane; **ready** = inputs present, no
blocker; **gap** = named blocker.

Every `file:line` below names a declaration opened and `#check`ed this lane
(probes `research/A01/probes/c1b_checks.lean`, `c1b_checks2.lean`,
`c1b_nextlane.lean`, `c1b_probe.lean`, `c1b_probe2.lean`).  Reviewer
(`research/A01/REVIEW_C1B.md`) re-`#check`ed all of them; line numbers below are
the corrected ones (finding 11).

---

## 0. The two Fourier normalizations, and the exact constants

C1b is where **two** of the project's three conventions meet (the third,
HeliCorgi Bessel, is C1c and is not on this route — `COMPARISON.md` §4
correction 1).

**(A) D01 angular** — `Source.angularFourier` (`Source/FourierConvention.lean:23`,
`#check`ed):
```
angularFourier f ξ = (2π)^(-3/2) • 𝓕 f ((2π)⁻¹ • ξ)        frequencyUnit = 2π  (:15)
```
with `𝓕` = Mathlib `Real.fourierIntegral` (`𝓕 f ζ = ∫ e^{-2πi⟨x,ζ⟩} f x dx`).
The order-`s` weight is `(1+‖ξ‖²)^s` **in the angular variable `ξ`**, equal to
`(1+(2π)²‖ξ‖²)^s` in the Mathlib-`𝓕` variable
(`angularSobolevSq_eq_frequency_weight`, `:50`, `#check`ed).  The `(2π)^(-3/2)`
amplitude and the `(2π)⁻¹` argument-rescaling make the transform **unitary**: at
`s = 0` the `(2π)^3` Jacobian of the rescaling exactly cancels the amplitude
squared (`hcoef` inside the proof of `:50`), so the order-0 constant is exactly
`1` (`‖angularFourier f‖₂ = ‖f‖₂`).

`angularRealization s : Lp ℂ 2 volume →L 𝓢'` (`Paper3/AngularFourierDilation.lean:177`,
`#check`ed) inverts this weighted transform.  **Precise form used by D01
(reviewer F6):** `angularRealization s` is *not* itself Mathlib's `𝓕⁻` — it is
`angularCoordinateRealization s ∘ angularFrequencyDilation.symm`, which differs
from `𝓕⁻` by the (unitary, non-identity) frequency dilation.  The identity that
`isSobolevDatum_orderZeroDatum` actually uses is the **composite**
```
angularRealization s (cyclesToAngularReal s h) = sobolevRealization s h
```
(`Paper3/AngularRealSobolev.lean:89`, `#check`ed), and at `s = 0`
`sobolevRealization 0` is Mathlib's genuine `L²` inverse-Fourier embedding
(`Paper3.sobolevRealization_zero`, `Paper3/SobolevHilbertModel.lean:130`, no `L¹`
hypothesis).  The constant-`1` conclusion is unaffected — the dilation is unitary
and is carried inside the datum.

*Derivative rule in this convention (derived, load-bearing; reviewer verified it
independently in Lean, finding 5):* the `2π` factors **cancel exactly** —
```
angularFourier (∂ⱼ f) ξ = (2π)^(-3/2) · (2πi (2π)⁻¹ ξⱼ) · 𝓕 f((2π)⁻¹ξ) = i ξⱼ · angularFourier f ξ,
```
so `∂ⱼ ↔ i ξⱼ` with **no `2π`**.  This is exactly why D01's
`isSobolevDatum_partialDeriv` (`Section4/D01/DerivativeDatum.lean:245`, `#check`ed)
carries multiplier `i ξⱼ (1+‖ξ‖²)^{-1/2}` — the `iξⱼ` is the derivative, the
`(1+‖ξ‖²)^{-1/2}` is the order-`(m+1)→m` Bessel lowering, and there is no loose
`2π`.  Sign is `+∂ⱼ`, not `−∂ⱼ` (reviewer: `translation a u = u(·+a)`,
`MeanSolenoidalTranslation.lean:18-20`).

**(B) Euler physical derivative tensors** — `ordinarySobolev`/`ordinaryLift`
(`vendor/.../Euler/MeanOrbitSobolev.lean:71,75`, `MeanOrdinaryLift.lean:24`, all
`#check`ed).  **Not a Fourier convention.**  The order-`m` coordinate is the
`m`-th Fréchet derivative tensor of the `L²` translation orbit at `0`, then
`ordinaryLift`ed to the cylinder.  In the angular variable this is
`(iξ)^{⊗m} · angularFourier u` — the **same `iξ`** (no `2π`) as (A)'s derivative
rule.  `ordinaryLift : L2 →ₗᵢ LiftL2 1` is an **isometry** (mass-1 angle
average), so it contributes **constant 1**.

**The exact C1b bridge constant, order by order.**
* Order `0`: **exactly `1`** — the datum realization is `sobolevRealization 0` =
  Mathlib `𝓕⁻` (via the composite above), and `ordinaryLift` is an isometry.
  *This is the only C1b order with no convention question to settle.*
* Order `m ≥ 1`: the **datum/multiplier identity is constant-free and has no `2π`**
  (the `2π` cancels, as derived above; `ordinaryLift` is unit-norm).  **The norm
  comparison is a different matter and does carry constants:** the Euler
  `SobolevSpace 1 q` norm is the norm of the *product* `SobolevWord q → LiftL2 1`,
  i.e. a **sup over derivative words** of `L²` norms of derivative tensors
  (`CylinderSobolevSpace.lean:49-53`; used by `ordinarySobolev_norm_le`), whereas
  the D01 order-`m` datum lives against the inhomogeneous Bessel weight
  `(1+‖ξ‖²)^{m/2}`.  These are **equivalent, not equal**, with `m`-dependent
  constants **in both directions**.  A01 never needs that norm identity:
  `ClassicalSolutionR.sobolev` (`verification/Contracts/V1/Data.lean:643`) asks
  for datum **existence** plus **continuity**, not a norm identity.

So there is **no hidden `(2π)^k`** to get wrong on the C1b route (contrast C1c,
which carries HeliCorgi's `(2π)` explicitly).  The risk `COMPARISON.md` §4 flags —
"the `(2π)` bookkeeping is where D01's first junk-value bug was" — is discharged
for C1b by the cancellation above (reviewer confirmed).  The residual C1b
difficulty is a **datum-existence** question at order `m ≥ 1`, not a
normalization: see rows C1b-m-E / C1b-m-D.

---

## 1. Sub-lemma table

| # | sub-lemma (Lean-ready statement) | size | inputs (file:line, #checked) | kind | status / blocker |
|---|---|---|---|---|---|
| **C1b-cong** | `IsSobolevDatum s z A → z =ᵐ[volume] z' → IsSobolevDatum s z' A` (all orders) | S | `IsSobolevDatum` (`Contracts/V1/Data.lean:160`; restated `D01/SmoothDatum.lean:237`) | bookkeeping (integral congruence) | **DONE** — `CarrierBridge.lean` `IsSobolevDatum.congr_field` |
| **C1b-0** | `(U : EulerMeanSolenoidal.L2) → IsSobolevDatum 0 (⇑U) (orderZeroDatum (Lp.memLp U))` | S | `orderZeroDatum` / `isSobolevDatum_orderZeroDatum` (`D01/OrderZeroDatum.lean:96,103`); `EulerMeanSolenoidal.L2 = Lp Space 2 volume` (`Euler/MeanSolenoidalSpace.lean:22`, `rfl`) | bookkeeping (order-0 seed re-export; constant `1`) | **DONE** — `CarrierBridge.lean` `isSobolevDatum_zero_ordinaryL2` (+ `exists_…`); reviewer F3: defeq re-export of `isSobolevDatum_orderZeroDatum` |
| **C1b-c5-0** | `U = a.toLp → IsSobolevDatum 0 a.field (orderZeroDatum (Lp.memLp U))` | S | `SmoothL2Field.toLp_ae` (`Euler/LpSmoothField.lean:44`); C1b-cong; C1b-0 | bookkeeping | **DONE** — `CarrierBridge.lean` `isSobolevDatum_zero_initial`.  Feeds **c8 at `t=0`**, *not* c5 (c5 is a pointwise equality — see C1b-rep) |
| **C1b-c5-all** | at the **initial** time, all orders: `IsSobolevDatum m a.field (smoothAngularDatum ⌈m⌉ m … a)` | S | `smoothAngularDatum_isSobolevDatum` (`D01/SmoothDatum.lean:278`), `exists_isSobolevDatum_of_contDiff_memLp` (`:290`) — `a : SmoothL2Field Space` supplies **all** orders directly, no Euler bridge | bookkeeping | **ready** (reviewer F4: subsumes C1b-c5-0 via `isSobolevDatum_unique`).  Also feeds c8 at `t=0`, not c5 |
| **C1b-lift0** | recover `U t` from the array: `ordinaryLift (U t) = value 1 (u t)`, `ordinaryLift` injective isometry, `ordinaryValue` its adjoint | — | `ordinarySobolev_value` (`Euler/MeanOrbitSobolev.lean:75`), `ordinaryValue`/`ordinaryValue_lift` (`Source/OrdinaryCylinderDescent.lean:56,60`), `exists_local` clause 4 (`Source/OrdinaryForcedLocal.lean:42`) | bookkeeping | **supplied upstream** (part of `exists_local`; no A01 obligation) |
| **C1b-unique** | Euler-derived datum = D01 datum where both exist: `IsSobolevDatum s z A → IsSobolevDatum s z B → A = B` | S | `isSobolevDatum_unique` (`D01/ForceClass.lean:286`) | bookkeeping | **ready** (makes "the" order-`m` datum path well-defined across constructions) |
| **C1b-rep** | **the B1 hand-off:** `velocity t =ᵐ[volume] ⇑(U t)` for `t ∈ Ico 0 T`, and `velocity (0,·) = a.field` pointwise | **L** | `ClassicalSolutionR.velocity` (`Contracts/V1/Data.lean:624`), C1b-cong | (produced by B1; **consumed** here) | **owned by B1** — given it, every datum row transfers to `velocity` by `IsSobolevDatum.congr_field`.  This is the *pointwise* half of c5 and the reason no datum row discharges c5 by itself |
| **C1b-m-E** | Euler side (`t>0`, no smoothness): each derivative word descends to an ordinary `L²` field — `{q n} (hq : n+3 ≤ q) (u : SobolevSpace 1 q) (hinv) (w : Fin n → Fin 4) → ∃ z, ordinaryLift z = word 1 u _ w` | M | abstract array `u t : SobolevSpace 1 (q+1)` + `word`/`word_hasDerivAt`/`word_has_jet`/`ofJet` (`Euler/CylinderSobolevSpace.lean:66,70,91,78`), `exists_ordinary_value` (`Source/OrdinaryCylinderDescent.lean:29`), clause 7 angle invariance (`Source/OrdinaryForcedLocal.lean:47`) | real analysis (Euler) | **ready→M** — no `SmoothOrbit`, no `SmoothL2Field`, no B1/T1: `word_hasDerivAt` already gives strong `L²` translation derivatives up to order `q+1` at fixed `t>0`; open item is whether `sobolevTranslation` is coordinatewise (reviewer did not verify) |
| **C1b-m-D** | D01 side — **the missing finite-order constructor:** `{m} (hz : MemLp z 2 volume) (L² derivs of z up to order m) → ∃ A : RealVectorSobolev m, IsSobolevDatum m z A` | **M–L** | parallel to `orderZeroDatum` (`D01/OrderZeroDatum.lean:96`); `isSobolevDatum_partialDeriv` (`D01/DerivativeDatum.lean:245`) is `SmoothL2Field`-only, so does not apply; `memLp_of_isSobolevDatum` (`D01/DatumToJets.lean:267`) | **real analysis (the actual blocker)** | **gap** — D01 jumps from order 0 (`orderZeroDatum`, bare `MemLp`) to all orders (`smoothAngularDatum`, `SmoothL2Field`) with nothing in between; the one new analytic input is the homogeneous↔inhomogeneous comparison `(1+‖ξ‖²)^m ≤ c_m(1+∑_{|α|=m}|ξ^α|²)` that lands the weighted transform in `L²` |
| **C1b-c8-0** | **★ next lane** — order-0 datum-path continuity: `{X}[TopologicalSpace X] (U : X → EulerMeanSolenoidal.L2) (hU : Continuous U) → Continuous (fun t => orderZeroDatum (Lp.memLp (U t)))` | M | `componentLp`/`memLp_component` as CLM of the `L²` arg (`D01/OrderZeroDatum.lean:67,72`), then `𝓕`/`realProjectionTo 0`/`WithLp.toLp`/`cyclesToAngularRealVector 0` (all CLM/CLE) | real analysis (CLM composition) | **ready→M** — no norm identity needed; must first prove `orderZeroDatum (Lp.memLp u) = Φ u` for an explicit CLM `Φ`, then transport continuity |
| **C1b-c8-m** | continuity of the order-`m ≥ 1` datum path | M–L | C1b-m-E, C1b-m-D; the vector order-`m` Plancherel isometry `‖smoothAngularDatum …‖ = ‖·‖_{Hᵐ}` | real analysis | **gap** — the order-`m` isometry is absent from the tree (`D01/OrderZeroDatum.lean:40-53` records this) |
| **C1b-c6** | divergence-free transport: `(∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)` → `spatialDivergence (⇑(U t)) = 0` (a.e./distributional) | M | `exists_local` clause 5 (`Source/OrdinaryForcedLocal.lean:43`), `EulerMeanSolenoidal.solenoidalSpace` (`Euler/MeanSolenoidalSpace.lean:58`) + weak-divergence test `mem_solenoidal_iff` (`:79`), `ordinaryLift_ae` (`Euler/MeanOrdinaryLift.lean:27`) | real analysis (descent) + bookkeeping | **gap** — descend cylinder divergence-free membership through `ordinaryLift` to the ordinary field, then align with D01's `spatialDivergence` |

## 2. Reading of the table

* **Bookkeeping rows** (angle invariance / `Fin 3` product vs. `PiLp` / a.e.
  transport / order-0 constant `1`): C1b-cong, C1b-0, C1b-c5-0, C1b-c5-all,
  C1b-lift0, C1b-unique.  Four are **DONE or ready this lane**; the order-0
  constant is settled (`= 1`).
* **Real-analysis rows**: C1b-m-E (Euler descent, M, ready), C1b-m-D (**the
  blocker**, missing D01 finite-order constructor), C1b-c8-0 (order-0 continuity,
  M, ready), C1b-c8-m (gap, needs the absent order-`m` isometry), C1b-c6
  (divergence descent, gap).
* **Which A01 obligation each row feeds** (reviewer's honest-status table):

  | A01 obligation | fed by C1b rows | honest status |
  |---|---|---|
  | **c8** `∀ m, ∃ G, ContinuousOn G ∧ IsSobolevDatum m (velocity t) (G t)` (`Data.lean:643`) | C1b-0 + C1b-c8-0 (`m=0`); C1b-m-E + C1b-m-D + C1b-c8-m (`m≥1`); C1b-cong + C1b-rep (`velocity ↔ ⇑(U t)`); C1b-unique | the only obligation C1b really serves; the **`∀ m` on one `T`** is additionally gated by **A3** (order-independent horizon, `A01_SPLIT.md:88`), because `exists_local`'s `T` depends on `q` — **not** by B1/T1 |
  | **c6** `spatialDivergence velocity = 0` (`Data.lean:638`) | C1b-c6 only | gap, as marked |
  | **c5** `initial : ∀ x, velocity (0,x) = a x` (`Data.lean:636`) | **none directly** | c5 is a *pointwise field equality*; C1b-c5-0/c5-all produce *datum* statements (feeding c8 at `t=0`).  The pointwise half is **C1b-rep** (B1's) |
  | **A1** tame product | **none** | A1 is A03's (product estimate on the D01 carrier); no carrier bridge involved.  Not promised in this table |

* **The one true blocker** that keeps C1b an **L**: **C1b-m-D**, a *missing D01
  finite-order datum constructor* — the order-`m` analogue of `orderZeroDatum`
  taking `MemLp 2` + strong `L²` derivatives up to order `m` to an order-`m`
  datum.  It is **not** a convention question (§0: no loose constant) and, per
  the reviewer (finding 9), **not** a B1/T1 dependence: the Euler side C1b-m-E
  already exposes strong `L²` derivatives up to order `q+1` at fixed `t>0` via
  `word_hasDerivAt`, with no `ContDiff`/`SmoothOrbit`/`SmoothL2Field`.  What is
  missing is the D01 constructor, where the homogeneous↔inhomogeneous comparison
  of §0 actually bites.

## 3. Proved in Lean this lane (unit C1b-0)

Module `formalization/NSFormalization/Section4/A01/CarrierBridge.lean`
(4 declarations; `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
`research/A01/axioms_c1b.lean`):

* `IsSobolevDatum.congr_field` — row C1b-cong (all orders); the one theorem with
  reusable content (reviewer F3): it carries every later row from `⇑(U t)` to the
  pointwise `velocity t` (row C1b-rep).
* `isSobolevDatum_zero_ordinaryL2` — row C1b-0 (defeq re-export of D01's seed).
* `exists_isSobolevDatum_zero_ordinaryL2` — the `∃` form.
* `isSobolevDatum_zero_initial` — row C1b-c5-0.

## 4. Recommended next lane

**★ C1b-c8-0** (order-0 datum-path continuity) — the only self-contained **M**
left, no new analysis and no upstream unit, half of what c8 wants at order 0:

```lean
theorem continuous_orderZeroDatum {X : Type*} [TopologicalSpace X]
    (U : X → EulerMeanSolenoidal.L2) (hU : Continuous U) :
    Continuous (fun t => orderZeroDatum (Lp.memLp (U t)))
```

Route (reviewer §5): re-express `componentLp` as
`Lp.compLpₗ (Complex.ofRealCLM.comp (EuclideanSpace.proj i))` (matching
`memLp_component`'s `comp_memLp'`, `OrderZeroDatum.lean:67,72`), compose the
remaining CLM/CLE factors (`𝓕 = Lp.fourierTransformₗᵢ`, `realProjectionTo 0`,
`WithLp.toLp 2`, `cyclesToAngularRealVector 0`); prove
`orderZeroDatum (Lp.memLp u) = Φ u` for that CLM `Φ`, then transport continuity.
No norm identity needed.

Then the two halves of C1b-m, neither touching B1 or T1:
**C1b-m-E** (`exists_ordinary_word`, Euler side, M — verify `sobolevTranslation`
is coordinatewise) and **C1b-m-D** (the missing D01 finite-order constructor,
M–L — the actual blocker; build it parallel to `orderZeroDatum` with the
homogeneous↔inhomogeneous comparison as its one new analytic input).
