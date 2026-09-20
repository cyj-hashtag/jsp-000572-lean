# lean-verify report for JSP-000572

> **Overall verdict: Verification passed.**
>
> The submission at proof commit
> `527bfcac522f9edf120301f63a0c7672d691f651` fully solves the original
> JSP-000572 problem. The formal theorem matches Frankl's general `k >= 4`,
> sufficiently-large-`n` statement, the unmodified pinned project builds, every
> listed target and the independent statement bridge check, and the checked
> declarations depend only on Lean's standard logical axioms.

This is a submitter-requested pre-submission self-check using the
`lean-verify` workflow from TheJustinSunPrize/awards. It is evidence for
maintainer review, not an award decision or a claim of Prize Operator
certification. The evidence was committed after the proof commit; all results
below concern the unchanged proof commit named above.

## Required judgments

| Required question | Judgment | Decisive evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | **Yes.** | The theorem has the original `forall k >= 4, exists N, forall n >= N` scope, the same strict binomial bound, and the same distinct singleton-intersection conclusion. |
| Did the specified commit actually pass verification? | **Yes.** | Clean builds, direct source checks, both automated targets, and matching `lean4checker` replay all exited 0 at `527bfcac522f9edf120301f63a0c7672d691f651`. |
| Does it fully solve the original problem? | **Yes.** | Every obligation in the original eventual-`n`, general-`k` theorem is covered; no extra premise, missing case, placeholder, or custom axiom enters the target. |
| Does it meet the Lean completeness requirements for this verification? | **Meets.** | The checked target and bridge use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, `native_decide`, or project axiom was found. |

Verification levels completed: source and semantic review, actual Lean checks,
Lean kernel checking during compilation, matching `lean4checker` replay, and an
independently transcribed statement bridge. No extended trust such as native
computation is used.

## Pinned evidence

- Awards PR: [TheJustinSunPrize/awards#79](https://github.com/TheJustinSunPrize/awards/pull/79).
- PR snapshot reviewed before this evidence update: base
  `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`, head
  `8d4b4554fe207758bd411c07d4f64470c9775bab` on branch
  `cyj-hashtag:submit-jsp-000572-cyj-hashtag`.
- Proof repository: <https://github.com/cyj-hashtag/jsp-000572-lean>.
- Submitted branch and commit: `main` at
  `527bfcac522f9edf120301f63a0c7672d691f651`. The commit existed in `main`
  when checked on 2026-09-20 UTC.
- Main declaration:
  [`Problem572.erdos_sos_singleton_intersection`](https://github.com/cyj-hashtag/jsp-000572-lean/blob/527bfcac522f9edf120301f63a0c7672d691f651/Problem572/Main.lean#L35).
- Original sources: [Erdos Problems #702](https://www.erdosproblems.com/702)
  and Peter Frankl, *On families of finite sets no two of which intersect in a
  singleton*, Bull. Austral. Math. Soc. 17 (1977), 125-134,
  [DOI](https://doi.org/10.1017/S0004972700025521). The statement appears on
  page 125 of the paper.
- The audit manifest is [`targets.json`](targets.json). Its normalized public
  copy differs from the executed manifest only in replacing the local absolute
  project path with `.`. The executed manifest SHA-256 was
  `4a93b4c6535e7aa23119faa9ca8639fc4f9d88722b9e61ac413878d81e9d68b2`.
- The automated result SHA-256 was
  `56a6561c09255e88c93b07e4edf74e07e50d7fbc99e6934fa1d89149cf3bef32`.
- The container log SHA-256 was
  `ec4195417bbbf23042e3716c3842868dac51e05eaa2802dde0745eb3c7a2cda4`.

## Statement and coverage

Frankl proves that for every integer `k >= 4`, there is a threshold depending
only on `k` such that, whenever `n` exceeds that threshold, every family `F` of
`k`-subsets of an `n`-element set with

```text
|F| > choose(n - 2, k - 2)
```

contains two distinct members whose intersection has cardinality one.

The checked Lean declaration states:

```lean
forall k : Nat, 4 <= k ->
  exists N : Nat, forall n : Nat, N <= n ->
    forall F : Finset (Finset (Fin n)),
      (forall A in F, A.card = k) ->
      Nat.choose (n - 2) (k - 2) < F.card ->
      exists A in F, exists B in F,
        A != B /\ (A intersect B).card = 1
```

| Original requirement | Lean representation | Coverage |
| --- | --- | --- |
| Every integer `k >= 4` | `forall k : Nat, 4 <= k` | Full |
| A threshold depending only on `k`, then every sufficiently large `n` | `exists N, forall n, N <= n` | Full; choosing `N = n0(k) + 1` converts the paper's strict threshold convention |
| A family of distinct `k`-subsets of an `n`-element ground set | `F : Finset (Finset (Fin n))` and `forall A in F, A.card = k` | Full |
| Strict size bound | `Nat.choose (n - 2) (k - 2) < F.card` | Full |
| Two distinct members with intersection size one | Membership witnesses, `A != B`, and `(A intersect B).card = 1` | Full |

`Fin n` is an `n`-element set, and both levels of `Finset` are duplicate-free.
The theorem adds no combinatorial assumption. Its explicit threshold is larger
than necessary, which still proves the existential eventual statement. The
original problem does not require equality-case classification.

The separately written [`AuditBridge.lean`](AuditBridge.lean) transcribes all
five requirements without using the project's helper definitions and proves
that transcription directly from the submitted theorem. It compiled and its
axioms were checked.

## Environment and execution

| Item | Observed value and result |
| --- | --- |
| Primary host | Windows 11 amd64, build 26200; isolated audit checkout outside the author working tree |
| Container cross-check | Docker Engine 29.6.1; Ubuntu amd64 image `ubuntu@sha256:008173c23f95b170204355c12626cb5a965d779a7e1283b09e9cffbb1bf33ca3`; 8 GiB RAM, 4 CPUs, 512 PIDs; no host credentials mounted |
| Toolchain | `leanprover/lean4:v4.20.0`; Lean commit `77cfc4d1a4f6`; Lake 5.0.0 |
| Dependencies | All nine checked-out SHAs matched `lake-manifest.json`; mathlib `c211948581bde9846a99e32d97a03f0d5307c31e`; official mathlib binary cache used only for dependencies |
| Unmodified clean build | `lake build`, exit 0; all 15 project modules compiled; host clean-build time 674.899 seconds; the container repeated the clean project build successfully |
| Main target | `lake build +Problem572.Main` and `lake env lean Problem572/Main.lean`, both exit 0 |
| Author audit | `lake env lean Audit.lean`, exit 0 |
| Independent bridge | `lake build +Problem572.AuditBridge` and direct source/axiom checks, all exit 0 |
| Automated workflow | `mechanical_status: standard_axioms_only`, exit 0, two targets checked, inputs stable |
| External replay | `lean4checker` tag `v4.20.0`, commit `aeaca0f19e8ff3ab8e0c98a52985cba7dcfb2234`; main replay exit 0 in 69.733 seconds; bridge replay exit 0 in 66.768 seconds; the container independently rebuilt the checker and replayed `Problem572.Main` successfully |
| Post-run source state | Proof HEAD remained the selected SHA. The only added audit source was the bridge in the isolated checkout; the submitted proof tree was unchanged. |

The container reproduction script is preserved as
[`container-verify.sh`](container-verify.sh). It clones the exact public proof
commit, checks the actual mathlib SHA, obtains the official dependency cache,
confirms that no project `.olean` exists before the build, rebuilds the project,
runs the source and axiom checks, builds the matching checker, and replays the
main module. It completed at `2026-09-20T15:08:27Z` with exit code 0.

## Proof dependencies

The complete observed axiom lists were:

```text
'Problem572.erdos_sos_singleton_intersection' depends on axioms:
[propext, Classical.choice, Quot.sound]

'AuditBridge.intended' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The same standard list was reported for the supporting declarations
`Problem572.singleton_free_bound` and `Problem572.fixed_pair_sharpness`.
These are the ordinary classical Lean/mathlib foundations accepted by the
verification workflow. The target does not depend on `sorryAx`, a project
axiom, or native evaluation.

## Findings and limitations

No defect was found in the submitted proof or its statement. An early audit
attempt placed the bridge outside the module search path; moving that audit-only
file into the isolated project and correcting its transcription resolved the
audit setup. The proof source did not change, so this diagnostic event does not
qualify the pass.

The `lean-verify` automation unit suite had three Windows-specific errors:
creation of a privileged symbolic link, use of POSIX-only `os.killpg`, and
timeout-child cleanup. These are maintenance-test portability issues. They did
not occur in, skip, or alter the target audit, which completed with exit 0; the
separate Linux container reproduction also passed.

This report determines formal correctness and coverage at the selected commit.
It does not determine contribution priority, identity, award eligibility,
merging, or payment. Related public work is disclosed in
[Issue #16](https://github.com/TheJustinSunPrize/awards/issues/16) and
[PR #754](https://github.com/TheJustinSunPrize/awards/pull/754).

## Reproduction

From a clean checkout of the selected commit, run the submitted checks:

```sh
lake update
lake build
lake build +Problem572.Main
lake env lean Problem572/Main.lean
lake env lean Audit.lean
```

To repeat the independent bridge, copy `AuditBridge.lean` to
`Problem572/AuditBridge.lean` in an audit-only checkout and run:

```sh
lake build +Problem572.AuditBridge
lake env lean Problem572/AuditBridge.lean
```

The exact container sequence and external replay are in
`container-verify.sh`. Local raw outputs were retained under
`C:\Users\Smnue\tmp\lean-verify-jsp572-20260920`; the public files in this
directory contain no credentials or private identity material.
