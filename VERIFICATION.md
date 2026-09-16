# Verification record for JSP-000572

## Pinned environment

- Lean: `v4.20.0`
- mathlib: `c211948581bde9846a99e32d97a03f0d5307c31e`
- Project manifest: `lake-manifest.json`
- Main theorem: `Problem572.erdos_sos_singleton_intersection`
- Local verification date: 2026-09-16

## Reproduction commands

From this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
lake env lean Audit.lean
```

For the complete scripted check, run `./verify.sh` on a Unix-like system or
`./verify.ps1` in PowerShell.

The environment variable skips mathlib's optional precompiled-cache download,
which depends on GitHub Releases. It does not skip compilation or the Lean
kernel check performed by `lake build`.

## Local results

`lake build` completed successfully. `lake env lean Audit.lean` printed the
fully elaborated theorem and reported:

```text
'Problem572.erdos_sos_singleton_intersection' depends on axioms: [propext, Classical.choice, Quot.sound]
'Problem572.singleton_free_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Problem572.fixed_pair_sharpness' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A source scan found no `sorry`, `admit`, `native_decide`, or project-level
`axiom` declaration. The listed dependencies are standard Lean/mathlib
logical axioms. This record reports submitter-produced checks and is not an
independent verifier or Prize Operator certification.

## Review scope requested

The designated verifier is requested to:

1. reproduce the build in a clean, isolated environment using the pinned
   toolchain and manifest;
2. inspect `Audit.lean` and independently repeat the axiom audit;
3. compare the theorem with the 1977 source as documented in `STATEMENT.md`;
4. review the definitions for vacuity and confirm that `Finset` cardinalities
   encode the intended finite-set statement;
5. confirm priority and attribution for the disclosed joint formalization;
6. determine whether this package belongs at the proposed `submissions/`
   path or should be moved to another official intake location; and
7. clarify the applicable formalizer allocation for a problem solved before
   its addition to the registry, given Selection Rules section 5 and the
   founder's public letter.

No candidate record, catalog eligibility flag, award tier, claimant status,
or payment entitlement is asserted by this submission.
