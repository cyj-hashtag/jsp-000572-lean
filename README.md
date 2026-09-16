# JSP-000572 Lean formalization

This package formalizes the singleton-intersection theorem proved by Peter
Frankl in *On families of finite sets no two of which intersect in a
singleton*, Bulletin of the Australian Mathematical Society 17 (1977),
125-134.

The Lean formalization was completed jointly by cyj-hashtag (GitHub:
cyj-hashtag) and ChatGPT 6 Astra.

This submission claims the Lean formalization contribution only. The
underlying mathematical result and proof route are attributed to Peter
Frankl. AI assistance and contribution are disclosed above; cyj-hashtag is
the human submitter and prospective claimant for the formalization work,
subject to the Prize Operator's attribution, eligibility, and KYC review.

## Main theorem

The entry point is `Problem572/Main.lean`. The top-level theorem is:

```lean
Problem572.erdos_sos_singleton_intersection
```

Its type is:

```lean
forall k : Nat, 4 <= k ->
  exists N : Nat, forall n : Nat, N <= n ->
    forall F : Finset (Finset (Fin n)),
      (forall A in F, A.card = k) ->
      Nat.choose (n - 2) (k - 2) < F.card ->
      exists A in F, exists B in F,
        A != B /\ (A intersect B).card = 1
```

The actual Lean source uses the corresponding Unicode notation. `Fin n` is
an `n`-element ground set, and the outer `Finset` makes the family a set of
distinct members.

The development supplies an explicit, deliberately non-optimal threshold
`Problem572.theoremThreshold k`. It also proves the contrapositive extremal
bound and constructs the fixed-pair family attaining the bound. It does not
claim the equality-case classification.

See [STATEMENT.md](STATEMENT.md) for the comparison with Frankl's statement
and [VERIFICATION.md](VERIFICATION.md) for the audit record.

## Reproduction

The project pins Lean 4.20.0 and mathlib commit
`c211948581bde9846a99e32d97a03f0d5307c31e`.

On Linux or macOS with `elan`, `lake`, `git`, and network access:

```sh
./verify.sh
```

On PowerShell:

```powershell
powershell -ExecutionPolicy Bypass -File ./verify.ps1
```

The scripts fetch the pinned dependencies when needed, build every module,
reject placeholder proof commands and project-declared axioms, and run the
Lean axiom audit in `Audit.lean`.

Expected axiom output for the main theorem is:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean/mathlib's standard logical axioms. The project introduces no
additional mathematical axiom and contains no `sorry`, `admit`, or
`native_decide`.

## Source and licensing

The original paper is cited by DOI rather than redistributed:
<https://doi.org/10.1017/S0004972700025521>.

The Lean source and verification scripts in this directory are offered under
the MIT License in [LICENSE](LICENSE). Submission prose follows the parent
repository's content licensing terms. See [NOTICE](NOTICE) for attribution.

`submissions/jsp-000572-cyj-hashtag/` is used as a proposed intake location
because the official repository does not currently publish a dedicated Lean
submission directory or template. Maintainers may relocate the package while
preserving its contents and history.
