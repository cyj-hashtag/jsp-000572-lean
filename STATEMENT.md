# Statement correspondence for JSP-000572

## Bibliographic source

Peter Frankl, *On families of finite sets no two of which intersect in a
singleton*, Bulletin of the Australian Mathematical Society 17 (1977),
125-134, DOI: <https://doi.org/10.1017/S0004972700025521>.

The paper states that if `X` is an `n`-element set, `F` is a family of
`k`-subsets of `X`, `n > n_0(k)`, `k >= 4`, and

```text
|F| > choose(n - 2, k - 2),
```

then two distinct members `A, B` of `F` satisfy `|A intersect B| = 1`.

## Lean statement

The theorem `Problem572.erdos_sos_singleton_intersection` states:

```lean
forall k : Nat, 4 <= k ->
  exists N : Nat, forall n : Nat, N <= n ->
    forall F : Finset (Finset (Fin n)),
      (forall A in F, A.card = k) ->
      Nat.choose (n - 2) (k - 2) < F.card ->
      exists A in F, exists B in F,
        A != B /\ (A intersect B).card = 1
```

The source file uses Lean's Unicode notation for quantifiers, inequalities,
conjunction, non-equality, and intersection.

## Premise-by-premise comparison

| Paper | Lean | Assessment |
| --- | --- | --- |
| Integer `k >= 4` | `k : Nat`, `4 <= k` | Equivalent in scope. |
| A sufficiently large `n` depending only on `k` | `exists N, forall n, N <= n` | Equivalent. Taking `N = n_0(k) + 1` converts the paper's strict threshold to this form. The proof gives an explicit larger threshold. |
| An `n`-element set `X` | `Fin n` | Every finite set of cardinality `n` is equivalent to `Fin n`; the theorem is invariant under relabeling. |
| A family of `k`-subsets | `F : Finset (Finset (Fin n))` and `forall A in F, A.card = k` | Equivalent. Both the members and the family are duplicate-free. Membership in `Finset (Fin n)` supplies containment in the ground set. |
| `|F| > choose(n-2,k-2)` | `Nat.choose (n - 2) (k - 2) < F.card` | Identical inequality. |
| Two members intersect in a singleton | `exists A in F, exists B in F, A != B /\ (A intersect B).card = 1` | Equivalent, with distinctness explicit. |

No additional combinatorial premise appears in the top-level theorem. In
particular, callers do not assume a kernel lemma, an intersecting link, an
asymptotic estimate, or a classification of equality cases.

## Proof organization

The formal proof follows Frankl's kernel and deletion strategy, with two
explicit reorganizations:

1. Kernel richness is represented by `Rich r F B`. Finite blocker and cover
   arguments establish the required counting bounds directly.
2. The final block count is replaced by a minimum-degree argument using the
   Erdos-Ko-Rado bound formalized in `IntersectingBound.lean`.

The explicit threshold is intentionally generous. Strengthening the
existential threshold does not weaken or otherwise change the theorem being
formalized.
