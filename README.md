# Reachability

Decidable reachability and shortest walks in finite directed graphs, in Lean 4 + Mathlib.

- `AdjList V := V → Finset V` — adjacency lists, with `FullWalk` (a `List.IsChain` of the adjacency relation) and `transGen_iff_exists_fullWalk`.
- `reachableWithin` — layered breadth-first search, proved to compute exactly the vertices reachable in fewer than `k` steps.
- A `Decidable (Relation.TransGen r a b)` instance (and `ReflTransGen`) for any decidable relation on a `Fintype` with `DecidableEq`, so plain `decide` works.
- `shortest` — a shortest walk (for `LinearOrder V`), proved minimal against every walk.
- `Reachability.Digraph` — bridges to Mathlib's `Digraph`.

Extracted from a personal experiments monorepo with history intact.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.34.1`, managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```
