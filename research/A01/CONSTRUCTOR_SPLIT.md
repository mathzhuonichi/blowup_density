# A01 — mild ⇒ classical constructor split (lane 158, resumed)

## 1. Target and hypotheses

The old `CarrierConstructor q ν S` in `probes/rev157_constructor_loop.lean` is a
consumer skeleton: lift compatibility alone omits both angular invariance and the
Duhamel equation. It is not the intended theorem to prove.

The exact Lean target and its consumer reduction are in
`research/A01/probes/ctor158_full.lean` (`CarrierConstructorFull`,
`rows_from_constructor_full`). The corrected target consumes fixed input `hq : 6 ≤ q`,
`hν : 0 < ν`, `hS : 0 < S`, `hR : 0 ≤ R`, a smooth solenoidal datum `a`, and the
forcing path `F` with `∀ n, Continuous (fun t => (F t).jetLp n)`. For the paths
`u : C(Icc 0 S, SobolevSpace 1 (q+1))` and `U : C(Icc 0 S, L2)`, retain **all seven**
conclusions of `localTheory_on_prescribed_horizon`:

1. `‖u‖ ≤ R`;
2. `u 0 = ordinarySobolev (q+1) a.toLp a.translation_contDiff`;
3. `U 0 = a.toLp`;
4. `∀ t, ordinaryLift (U t) = value 1 (u t)`;
5. `∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0`;
6. the exact `quadraticDuhamel` equation of `Horizon.lean:137`;
7. `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t`.

Its desired output remains
`∃ a' f' T, S < T ∧ ∃ w : ClassicalSolutionR ν a' f' T, ∀ t : Icc 0 S,
(fun x => w.velocity (↑t,x)) =ᵐ[volume] ⇑(U t)`.
This is a research target, **not a proved theorem or a new axiom**. Row (v) additionally
requires the chosen data and force to satisfy the manuscript classes and the links to
`a` and `F`; the bare consumer skeleton does not encode those links.

## 2. What is now proved

`formalization/NSFormalization/Section4/A01/ConstructorPieces.lean`:

- `hasWeakDerivsL2_of_word_full`: a spatial word of length `n` has all remaining
  weak derivatives of order `m` whenever `n+m ≤ q+1`.
- `hasWeakDerivsL2_of_cylinder_full`: `⇑U` has weak derivatives through every
  `m ≤ q+1`, assuming angular invariance and lift compatibility.
- `exists_isSobolevDatum_slice_of_cylinder`: for any candidate velocity with the
  a.e. hand-off `hslice`, each time slice has an order-`m` datum for **every
  `m ≤ q+1`**. No classical solution, spatial representative, or time smoothness is
  assumed. This strengthens the former `m+3 ≤ q+1` result.
- `exists_continuous_word_descent`: each spatial word of length `n ≤ q+1` has
  a bundled continuous ordinary `L²` path with exactly the required lifted word.
  The cylinder coordinate is continuous; `ordinaryLift` is an isometry, so its
  unique preimage is continuous. This is the time-continuity rung of c3.

The full-order induction uses lane 153 `word_descent_ae_top`, not the order-losing
`exists_descend`. The weak pairing is the existing
`weakDeriv_pairing_of_lift_hasDerivAt`. There is **no top-three-order gap**.

## 3. Remaining structure fields

| Unit | Current status / precise residual |
|---|---|
| Horizon `T>S` | **Analytic gap.** Choosing the number `S+1` is trivial, but a solution and its carrier identity must extend beyond `S`; the supplied pair only lives on `Icc 0 S`. The full row is not S. |
| c1 velocity / pressure | Choose actual jointly smooth fields; B1 and pressure recovery remain. |
| c2 `horizon_pos` | Arithmetic once an actual horizon `T>S>0` is available. |
| c3 `velocity_smooth` | Joint `ContDiffOn ℝ ∞` remains. Continuous spatial word paths are now proved. Duhamel time-derivative bootstrap and all spatial orders on one horizon still have to be assembled. |
| c4 `pressure_smooth` | Joint pressure regularity from Helmholtz recovery and B1 remains. |
| c5 `initial` | Defining `a'` as the initial slice gives this field by reflexivity; class membership and the link to `a` remain in (v). |
| c6 `divergence` | Descend cylinder divergence a.e., then upgrade using a continuous representative. Still open. |
| c7 `momentum` | Existing projected/residual identities give a reduction. Defining `f'` as the residual merely moves the content into its force-class membership and its link to `F`. |
| c8 `sobolev` | Per-time datum existence now holds at all available `m≤q+1`. Continuous word paths are proved, but continuity in the order-`m` angular datum norm still needs a norm bridge. Also need compatible all-order paths on one horizon and the larger `Ico 0 T` domain. |
| c9 `pressure_gradient` | Align Helmholtz `L²` gradient with the solution's pressure gradient. |
| `hslice` | B1 must supply this identity for its actual jointly smooth field. It cannot be discharged by citing an unrelated per-slice representative. |
| (v) datum / force | Prove membership and the actual input-output links, including global force-domain regularity. `MemL1Hm` is in `A04/Forcing.lean:110`. |

For reference, `smoothAngularDatum_isSobolevDatum` is at `D01/SmoothDatum.lean:287`,
and the consumer-side `isSobolevDatum_ordinary_of_hslice` is at
`A01/SliceWiring.lean:157`.

A per-time `Classical.choose` is not itself a mathematical obstruction to joint
regularity: uniqueness can relate the choices, as the word-path proof does.
However, neither vendor representative theorem alone supplies the required joint
`C∞` statement. Do not confuse continuity in time with a time derivative.

## 4. Next work and verification

The independent remaining carrier piece is c6 divergence descent. Row (v)'s force
bridge and the Duhamel/bootstrap campaign remain substantive work. The finite-order
word continuity proved here does not settle them or the constructor.

Axiom and top-order zero-instance probe: `research/A01/axioms_constructor_pieces.lean`
(`q=6`, `m=7`). The assigned Luna compiler passed the module, both non-vacuity consumers,
the D01/A02 compatibility probe, and the full-target consumer probe. All audited
declarations use only `propext`, `Classical.choice`, `Quot.sound`; exact logs and
historical failed attempts are in `ATTEMPTS_CONSTRUCTOR.md`.
