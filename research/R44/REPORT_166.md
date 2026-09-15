# Lane 166-R44-split report

## 1. Theorems proved

Three new theorems in namespace `NSFormalization.Section4.R44`:

1. `exists_rcritical2_constants`: from positive universal nonlinear/embedding
   constants and `0 ≤ C₂`, chooses universal `theta,c,C>0`, with one `theta`
   satisfying both the `J`-energy and C01 absorption shrinkings,
   `C₃*c² < theta²/4`, and `C=C₂+1`.
2. `radius_forces_gronwall_small`: proves that the manuscript radius
   `c*ν^(3/2 : ℝ)*exp (-(C₂+1)*ν*S)` implies the strict scalar Grönwall
   smallness bound.  This includes the real-`rpow` square calculation and the
   exponential decay calculation.
3. `criticalSquaredNormBound_radius`: from the conditional
   eq:Rcritical2-shaped inequality, a prefix bound on `∫B²`, and the radius
   inequality, proves `Y(t) ≤ theta*ν/2` throughout `[0,T]`.  It reuses
   `A04.gronwall_deriv` and `Paper1.continuous_bootstrap` for the genuine
   first-exit argument.

The identical power spelling and C01 gate rows are not duplicated:
`R43.enorm_npow_two_eq_rpow_two` and `R43.criticalL3_gate_enorm` are imported
and exercised by the conformance file.

## 2. What is in Lean now

`formalization/NSFormalization/Section4/R44/Pieces.lean` contains the complete
constant selection, exact radius scaling, linear Grönwall improvement, and
first-crossing closure for R44, conditional on the analytic PDE inequality
supplied by one interval-integrable derivative function, the real `H^{-1/2}`
force-square prefix bound, and a globally continuous `Y` (or a continuous
extension of the PDE norm path from the closed window).

`research/R44/axioms_r44_pieces.lean` prints the axioms of all three new
declarations and the two reused R43 declarations.  Every line is exactly
`[propext, Classical.choice, Quot.sound]`; concrete non-vacuity examples
instantiate all five results.

`research/R44/R44_SPLIT.md` records the six proof rows, exact Lean shapes,
registered contract IDs/versions, owners, sizes, dependencies, and separate
stating/proving blockers.  The audit found that the comparison's old D01
registration gap is already closed by `D01.datum_lemmas_v2` V2.

## 3. Gaps

| gap | size | blocker |
|---|---:|---|
| D01 G1: define `J`, prove exact `H^(3/2)` weight identity and negative-order duality | M | canonical PDE-level S1 statement and proof |
| R44 G2: differentiate/pair the PDE and prove eq:Rcritical2 | L | main a-priori estimate; depends on G1 and A05 V2 |
| C01/D01 G3: `H^(-1/2)` force slice with continuity/integrability and prefix-integral/time-norm identity | M | applying the now-proved scalar bootstrap |
| A05 V2 critical `L³` embeddings | M–L | nonlinear estimate and C01 gate input |
| C01 V4 eq:RH1, Fourier inequality, zero-datum `H²` assembly | M+M | finite continuation integral |
| R44 G4 maximal-endpoint gluing | M | pass fixed-horizon C01 estimates to a hypothetical finite maximal endpoint |
| A04 V3 `extendsBeyond` | M+S proof and registration (no `extendsBeyond` theorem on this branch) | strict lifespan conclusion |
| A02/A01 transitive discharge | upstream | registered A02 V2 maximal existence still takes the local-solution clause explicitly |

Nothing blocks stating the reconciled nine-field R44 API.  G1/G3 block clean
canonical statements of internal analytic rows; all listed items block proving
and binding the final API.  The `ℕ`-power/rpow bridge, absorption-gate arithmetic,
universal constants, radius formula arithmetic, and scalar first-exit bootstrap
are closed.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, from `verification/`,
with `LEAN_NUM_THREADS=6` where applicable.

```text
lake build NSFormalization.Section4.R44.Pieces
  exit 0; Build completed successfully; no warnings

lake env lean ../formalization/NSFormalization/Section4/R44/Pieces.lean
  exit 0; 0 bytes output

lake env lean ../research/R44/axioms_r44_pieces.lean
  exit 0; five declarations printed exactly
  [propext, Classical.choice, Quot.sound]; all examples typechecked

make check
  exit 0; plan check, contract architecture/policy tests, and work-queue check passed

git diff --check
  exit 0

forbidden-token/options scan over the two new Lean files
  no hits
```
