# Lane 158 resumed: source review

## What is proved

The new argument removes the three-order loss in the earlier constructor piece.
For an angle-invariant cylinder element of order `q+1`, its ordinary carrier has
weak derivatives and a Sobolev datum through order `q+1`. Every spatial derivative
word of an available order also has a continuous ordinary `L²` path.

## Why the statements match the intended piece

- The induction keeps the exact order budget `n+m ≤ q+1`. Its step uses
  `word_descent_ae_top` at `n+1` and the existing translation-to-weak-pairing lemma.
  It neither assumes a smooth representative nor assumes a classical solution.
- The datum theorem retains angular invariance, lift compatibility and the a.e.
  velocity identity. Only the old `m+3 ≤ q+1` restriction is strengthened to
  `m ≤ q+1`.
- The path theorem reflects continuity through the isometric `ordinaryLift`.
  It proves `L²` continuity of individual words, not time differentiability or
  continuity in the angular datum norm.
- The order-7 datum witness at `q=6` exercises the new endpoint order, which the
  earlier statement did not admit.

## Remaining obligations

This is a constructor component. Joint smoothness, a common all-order horizon,
the datum-norm continuity bridge, divergence/pressure assembly, and identification
of the original datum and forcing remain open. The corrected split document must
keep these obligations explicit. Choosing a number `T>S` does not construct a
solution on that interval.

## Verification boundary

This review checks the source argument and its scope. Lean compilation and the
transitive-axiom checks are assigned to the separate Luna high agent; their final
results are recorded in the session validation report.

Luna subsequently compiled the module and all three A01 probe files successfully.
The four implementation exports, both top-order consumers, the historical datum
probe and `rows_from_constructor_full` report only the standard logical axioms.
