# Lane 178-A01-b1-ladder-r3 report

## 1. Theorems and ranges

The finite arbitrary-order R3 theorem is
`NSFormalization.Section4.A01.datumPath_contDiffOn`.  For `6 ≤ q` and

```lean
max 6 m + 2 * j ≤ q + 1
```

it assumes the order-`q+1` Duhamel carrier `u`, its ordinary descent `U`, angle
invariance, and

```lean
hfs : ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc 0 S)
```

and proves exactly

```lean
∃ G : ℝ → RealVectorSobolev (m : ℝ),
  ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
  ∀ t : Icc (0 : ℝ) S,
    IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1).
```

This is the range of the current all-`j` implementation, not a claim of the sharp
mathematical range for `m < 6`.  The proof works at the single order `k = max 6 m` and
then lowers to `m`: each time derivative reads the Laplacian from two orders higher,
while the floor at six is where the repository's complete cylinder Sobolev product is
available.  A sharper mixed-order induction would have to form the nonlinear residual
at order six and then lower it inside the induction; that is beyond the range-only fix.

`datumPath_contDiffOn_one` is the unconditional theorem for the original Horizon force
input.  It needs no `hfs`: the already bundled continuous force path suffices.  Its range is

```lean
m + 2 ≤ q + 1
```

and its conclusion is the same display with `ContDiffOn ℝ 1`.  This range is sharp for
the existing R2 derivative: the Laplacian consumes exactly two spatial orders, while no
product differentiation is needed.  In particular `q = 6, m = 0` now compiles.  Together
with R1's `C⁰` theorem for every `m ≤ q+1`, this is the full range justified by Horizon's
stated time-continuity hypothesis alone.

`datumPath_contDiffOn_all_orders` proves the requested `∀ j m` conclusion under a named
`hall` supply hypothesis.  For every `q ≥ 6`, `hall` provides a smooth order-`q` force
path, an order-`q+1` exact Duhamel carrier, angle invariance, and realization of the same
ordinary path `U`.  The proof chooses `q = max 6 m + 2*j`.  This is intentionally stronger
and more honest than `∀ q, HasAprioriBound`: the latter predicate contains neither a
smooth cylinder force bridge nor cross-order compatibility of the resulting ordinary paths.

`residualPath_hasDerivAt` covers `k ≥ 6` with `k+4 ≤ q+1`.  Given continuous order-`k`
datum selections `R,D` for the projected residual and the ordinary descent of its computed
derivative, it proves at every `t ∈ Ioo 0 S`

```lean
HasDerivAt (extendPath S hS.le R)
  (D ⟨t, ht.1.le, ht.2.le⟩) t.
```

The computed cylinder derivative is definitionally the path

```text
ν Δu_t + P(f_t - B(u_t,u) - B(u,u_t)).
```

`reducedResidualPath_hasDerivWithinAt` proves this formula on the closed interval,
including one-sided endpoint derivatives.  The spatial loss is four orders because
differentiating `Δu` requires the velocity derivative at order `k+2`.

Supporting results include `cylinderPath_contDiffOn` (`k ≥ 6`, `k+2*j ≤ q+1`) and
`exists_contDiff_datumPath_of_cylinder`, the general descent of a `C^j` invariant order-`p`
cylinder path to its unique order-`p` angular datum path.

## 2. Files

- `formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean` — new R3 proof module,
  with 18 audited declarations.
- `research/A01/axioms_b1_r3.lean` — all declarations printed with exactly
  `[propext, Classical.choice, Quot.sound]`; includes the explicit `u := 0`, `U := 0`
  non-vacuity example.
- `research/A01/ATTEMPTS_B1_R3.md` — proof route, rejected alternatives, mandated search,
  and force/all-order gap record.
- `research/A01/B1_LADDER.md` — R3 finite/conditional ranges marked DONE and R4 inputs
  updated to use the compatible all-order supply theorem.
- `research/A01/REPORT_178.md` — this report.
- `research/A01/probes/rev178_*.lean` — retained reviewer probes, including the
  minimal-range regression at `q = 6, m = 0` and the expected-failure `C³` mutation.

No pre-existing Lean module other than this lane's own `DatumPathSmooth.lean` was edited.

## 3. Residual gaps and error text

There is no remaining Lean error in the delivered module, conformance file, or positive
reviewer probes.  `rev178_negative_c3.lean` remains an intentionally failing mutation:
it asks the unchanged `C²` witness to prove `C³` without two more spatial orders.

The remaining mathematical interface gap is precise.  `forcePath_of_memForceR` gives the
physical carrier `C01.forcePath hf` and continuity of every spatial jet.  `MemForceR` gives
a `C∞` angular datum path at every order.  The mandated `grep -rn` search over
`Section4/{D01,A03,A04,A01,C01}`, `Source/`, `Paper1/`, `Paper3/`, the vendor tree, and
`FormalPatched/` found no theorem converting those facts into

```lean
ContDiffOn ℝ ∞
  (extendPath S hS.le (sobolevPath (C01.forcePath hf) hF q)) (Icc 0 S).
```

It also found no theorem deriving compatible carriers for one fixed `U` solely from a family
of fixed-order `HasAprioriBound` hypotheses.  Therefore the arbitrary-`j` finite theorem
exposes `hfs`, and the all-order theorem exposes the stronger compatibility supply `hall`.

The only non-clean output in the gates is pre-existing repository output, not an error:
`make check` reports the copied-source token

```text
formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90: token "sorry"
```

and `source_hashes_match: false`.  The command nevertheless exits 0.  The new Lean files
contain none of `sorry`, `admit`, `axiom`, or `native_decide`.

## 4. Commands and results

All `lake` commands were run from `verification/` after sourcing `scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.A01.DatumPathSmooth` — exit 0; the target rebuilt
  successfully.  The displayed warnings were replayed from pre-existing dependencies.
- `lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean` — exit 0,
  zero output.
- `lake env lean ../research/A01/axioms_b1_r3.lean` — exit 0; all 18 declarations printed
  exactly `[propext, Classical.choice, Quot.sound]`, and the zero example elaborated.
- `lake env lean` on `rev178_sharp_c1.lean`, `rev178_range_repro.lean`,
  `rev178_zero_j2.lean`, and `rev178_hall_zero.lean` — exit 0 for every positive probe.
  The range regression confirms that `q = 6, m = 0` now reaches `C¹`.
- `lake env lean ../research/A01/probes/rev178_negative_c3.lean` — expected nonzero exit at
  line 40: the available `ContDiffOn ℝ 2` proof does not have the requested
  `ContDiffOn ℝ 3` type.
- `make check` from the worktree root — exit 0; all invoked checks completed successfully,
  with the pre-existing architecture notices quoted above.
