# Contributing

Thanks for helping improve `sos`.

## Development Setup

Install Lean through `elan`, then from the repository root run:

```bash
lake exe cache get
lake test
```

`lake test` is the primary check. It builds `SOSTest`, including examples that call CSDP through the `lean-csdp` FFI, so running individual test files with `lake env lean` is not equivalent for `by sos` examples.

## Pull Requests

- Keep changes focused and include a regression example when fixing tactic behavior.
- Prefer examples in `SOSTest/Examples.lean` for user-facing coverage, `SOSTest/Harrison.lean` for ports of Harrison examples, and `SOSTest/Internal.lean` for pure helper invariants.
- Avoid adding `sorry` or `axiom` to `SOS/`; CI checks for both.
- Document known search limitations as comments near disabled examples rather than silently deleting them.

## Dependencies

The package is pinned by `lake-manifest.json`. If dependency revisions change, include the manifest update and mention why the bump is needed.
