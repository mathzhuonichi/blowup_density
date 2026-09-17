# T10 canonical-module attempts

## Missing bridge file named by the brief

The checkout has no `verification/Bindings/Data.lean`.  The first lookup
reported exactly:

```text
wc: verification/Bindings/Data.lean: No such file or directory
```

A direct read likewise reported:

```text
sed: can't read verification/Bindings/Data.lean: No such file or directory
```

Resolution: use the actual distributed bridges in `Bindings/Packet.lean`,
`Bindings/DatumLemmas.lean`, `Bindings/Correction.lean`, and
`Bindings/Uniqueness.lean`, together with the canonical-module allowlist in
`experiments/check_contracts.py`.  No repository file was changed to paper over
the mismatch.

## First `torusLift` alias spelling

The first draft used the unconstrained declaration
`abbrev torusLift := NSFormalization.Paper1.torusLift`.  The initial module build
failed with this exact primary diagnostic and its downstream cascade:

```text
error: NSFormalization/Section3/T10/PeriodicData.lean:41:20: don't know how to synthesize implicit argument `E`
  @Paper1.torusLift ?m.3
context:
⊢ Type ?u.2
error: NSFormalization/Section3/T10/PeriodicData.lean:41:7: Failed to infer type of definition `torusLift`
error: NSFormalization/Section3/T10/PeriodicData.lean:102:36: Unknown identifier `torusLift`
error: NSFormalization/Section3/T10/PeriodicData.lean:118:23: Unknown identifier `torusLift`
error: NSFormalization/Section3/T10/PeriodicData.lean:165:36: Unknown identifier `torusLift`
error: NSFormalization/Section3/T10/PeriodicData.lean:243:23: Unknown identifier `torusLift`
error: NSFormalization/Section3/T10/PeriodicData.lean:284:11: Function expected at
  torusLift
but this term has type
  ?m.89
error: NSFormalization/Section3/T10/PeriodicData.lean:295:27: Unknown identifier `ClassicalSolutionT`
error: NSFormalization/Section3/T10/PeriodicData.lean:299:29: Unknown identifier `ClassicalSolutionT`
error: NSFormalization/Section3/T10/PeriodicData.lean:321:22: Unknown identifier `torusLift`
error: NSFormalization/Section3/T10/PeriodicData.lean:327:16: Unknown identifier `torusLift`
Some required targets logged failures:
- NSFormalization.Section3.T10.PeriodicData
error: build failed
```

Resolution: retain a reducible alias but spell out the source function's exact
polymorphic arguments and result type.  The probe checks the resulting function
equals `NSFormalization.Paper1.torusLift` by `rfl`.

## Lake discovery

No discovery failure occurred.  The existing unrestricted
`[[lean_lib]] name = "NSFormalization"` entry in `formalization/lakefile.toml`
picked up the new `NSFormalization/Section3/T10` module without a lakefile edit.
The long explicit `roots` list in that file belongs only to the separate
vendored `Formal` library; Section 4 modules are found by the same unrestricted
`NSFormalization` library entry used here.
