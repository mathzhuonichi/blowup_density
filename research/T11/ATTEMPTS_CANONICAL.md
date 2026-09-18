# T11 canonical-module attempts

No Lean elaboration, build, or gate attempt failed while creating the canonical
module and API probe.

The initial source inventory queried the not-yet-created T11 module directory.
That `rg` subcommand emitted exactly:

```text
rg: formalization/NSFormalization/Section3/T11: No such file or directory (os error 2)
```

This was an existence check before the directory was added, not a Lean failure.

The first module build replayed pre-existing dependency linter warnings, but
completed successfully; those warnings were not errors and the required direct
`lake env lean` checks produced zero output.
