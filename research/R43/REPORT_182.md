# Lane 182-R43-s1b-trilinear report

Date: 2026-09-15. Branch: `erenup/182-R43-s1b-trilinear`.

## 1. Theorems, exact statements, and constants

The shifted-data constant and final trilinear constant are

```lean
def derivativeCriticalConst : ℝ :=
  4 * NSFormalization.Section4.A05.criticalL3Const

def trilinearConst : ℝ :=
  NSFormalization.Section4.A05.criticalL3Const *
    derivativeCriticalConst * derivativeCriticalConst

theorem trilinearConst_eq :
    trilinearConst =
      16 * NSFormalization.Section4.A05.criticalL3Const ^ 3

theorem derivativeCriticalConst_pos : 0 < derivativeCriticalConst
theorem trilinearConst_pos : 0 < trilinearConst
```

For supplied physical shifted carriers, the derivative embedding is

```lean
theorem derivativeCriticalL3 {v : SpatialField}
    (hv : MemHInfty v) {Z : RealVectorSobolev (3 / 2)}
    (hshift : ShiftedCriticalData v Z) :
    eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume +
        eLpNorm hshift.lambda 3 volume ≤
      ENNReal.ofReal derivativeCriticalConst * ‖Z‖ₑ
```

The datum-level three-factor Hölder theorem is

```lean
theorem lintegral_enorm_mul_three_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G]
    {f : Space → E} {g : Space → F} {h : Space → G}
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ * ‖h x‖ₑ ∂volume ≤
      eLpNorm f 3 volume * eLpNorm g 3 volume * eLpNorm h 3 volume
```

Its physical advection specialization is

```lean
theorem criticalAdvectionHolder (v lambda : SpatialField)
    (hv : NSFormalization.Section4.A05.SmoothL2 v)
    (hlambda : MemHInfty lambda) :
    ENNReal.ofReal
        |∫ x : Space, (inner ℝ
          (advection (NSFormalization.Section4.C01.lift v) 0 x)
          (lambda x) : ℝ)| ≤
      eLpNorm v 3 volume *
        eLpNorm (NSFormalization.Section4.A05.gradTensor v) 3 volume *
          eLpNorm lambda 3 volume
```

The assembled result, with the exact carrier boundary made explicit, is

```lean
theorem criticalTrilinearEstimate_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf)
    (hbridge : CriticalAdvectionLpBridge hcrit) :
    CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit
```

Thus the energy-row corollary is

```lean
theorem rcritical1_of_hcrit
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} (hf : MemForceR f)
    (hcrit : CriticalDatumPath w hf)
    (hbridge : CriticalAdvectionLpBridge hcrit) :
    (∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => criticalNormAt w.velocity r ^ 2)
        (criticalEnergyDerivative hcrit t) t) ∧
      ∀ t ∈ Ioo (0 : ℝ) T,
        criticalEnergyDerivative hcrit t / 2 +
            (ν - trilinearConst * criticalNormAt w.velocity t) *
              criticalDissipationAt w.velocity t ^ 2
          ≤ criticalForceAt f t * criticalNormAt w.velocity t
```

Every audited declaration prints exactly
`[propext, Classical.choice, Quot.sound]`.

## 2. Files

- `formalization/NSFormalization/Section4/R43/CriticalPairing.lean` restores
  the accepted lane-175 prerequisite byte-for-byte from commit `a6fac76`; it
  was absent from both this lane's starting `HEAD` and
  `origin/erenup/integration`.
- `formalization/NSFormalization/Section4/R43/Trilinear.lean` contains the
  Riesz-coordinate multiplier bound, shifted critical embedding,
  three-factor Hölder estimate, physical advection estimate, explicit
  constants, conditional assembly, and energy corollary.
- `research/R43/ATTEMPTS_S1B.md` records the base-state discrepancy, complete
  mandated tree search, interface analysis, residual bridge, and resolved
  elaborator diagnostics.
- `research/R43/axioms_s1b.lean` audits ten declarations and constructs the
  full bridge and final estimate for the genuine zero solution as the required
  non-vacuity example.
- `research/R43/R43_SPLIT.md` now marks S1b's inequality layer proved and names
  the remaining carrier boundary.
- `research/R43/REPORT_182.md` is this handoff report.

## 3. Gap and exact resolved error text

The requested unconditional theorem

```lean
∀ hcrit, CriticalTrilinearEstimate (C₀ := trilinearConst) hcrit
```

is not derivable from the currently exported `CriticalDatumPath` interface.
The proved theorem additionally assumes `CriticalAdvectionLpBridge hcrit`.
For each interior time this structure supplies a physical `Λu` realization,
the three derivative half-order data with exact symbols
`(i ξ_j / |ξ|) Z_i`, and the Parseval identity identifying the datum pairing
with the physical trilinear integral. It contains no `L³` estimate or
trilinear inequality.

Before isolating this hypothesis, the prescribed `grep -rn` search covered
all of `Section4/{A05,B02,D01,A03,C01,R43}`, `Source/`, and `Paper1/`. It found
no physical `Λu` constructor, homogeneous derivative-datum constructor,
`IsRieszPower`, U8 wrapper, or fractional Parseval bridge. Constructing `shifted` requires the unexported A05 U4/U8 carriers (plus `MemHInfty` closure for `Λu`), while `pairing_identity` is a separate fractional Parseval/duality obligation. The zero-solution construction proves that the interface is
inhabited and consistent.

There is no remaining compiler error in the conditional theorem. The exact
diagnostics encountered during development and resolved were:

```text
Unknown identifier `mul_le_mul_left'`
```

```text
⊢ eLpNorm (fun x => ‖f x‖ₑ) 3 volume * ... =
    eLpNorm f 3 volume * ...
```

```text
(div_le_one hnorm).mpr hcoord
has type |ξ j| / ‖ξ‖ ≤ 1
but is expected to have type |ξ j| / |‖ξ‖| ≤ 1
```

They were resolved respectively with `mul_le_mul'`, `eLpNorm_enorm`, and
normalization by `abs_of_pos hnorm`.

## 4. Commands and results

Run from `verification/` after `. ../scripts/lean-env.sh` unless stated:

```text
LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.Trilinear
```

Exit 0; only pre-existing dependency warnings were replayed.

```text
LEAN_NUM_THREADS=6 lake env lean \
  ../formalization/NSFormalization/Section4/R43/Trilinear.lean
```

Exit 0 with zero output.

```text
LEAN_NUM_THREADS=6 lake env lean ../research/R43/axioms_s1b.lean
```

Exit 0; all ten declarations printed exactly
`[propext, Classical.choice, Quot.sound]`, and the non-vacuity example checked.

```text
make check
```

Run from the worktree root; exit 0.

```text
git diff --check
```

Exit 0.
