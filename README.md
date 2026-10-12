# Reachability

[![CI](https://github.com/Arrow7000/reachability/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Arrow7000/reachability/actions/workflows/lean_action_ci.yml)

Verified, kernel-reducible reachability and shortest walks for finite directed graphs, in Lean 4
and Mathlib.

Graphs are adjacency lists, `AdjList V := V → Finset V`. Reachability is Mathlib's own
`Relation.TransGen`, and it is decided by a breadth-first search that is proved correct. The
search is plain structural recursion, so `decide` works on concrete graphs with no
`native_decide` needed. The same instance also covers the transitive closure of any decidable
relation on a finite type.

```lean
import Reachability

open Relation

/-- 0 → 1 → 2 → 0, and separately 3 → 4. -/
def g : AdjList (Fin 5)
  | 0 => {1} | 1 => {2} | 2 => {0} | 3 => {4} | 4 => ∅

example : TransGen g.Adj 0 2 := by decide
example : ¬TransGen g.Adj 0 3 := by decide

-- Any decidable relation on a finite type works, not just `AdjList`s.
example : ReflTransGen (fun a b : Fin 10 => b.val = a.val + 3) 1 7 := by decide

#eval g.shortest 0 2  -- some [1]
#eval g.shortest 0 3  -- none
```

## Main results

### Definitions

- `AdjList V := V → Finset V`: a directed graph, given by each vertex's out-neighbours.
- `g.FullWalk a b segs`: a walk from `a` to `b` through the intermediate vertices `segs`.
- `g.reaches a b : Bool`: breadth-first search for `b` from `a`.
- `g.shortest a b : Option (List V)`: the intermediate vertices of a shortest walk from `a` to `b`
  (needs `[LinearOrder V]`).

### Theorems

```lean
theorem AdjList.reaches_iff : g.reaches a b ↔ TransGen g.Adj a b

theorem AdjList.shortest_fullWalk (h : g.shortest a b = some p) : g.FullWalk a b p
theorem AdjList.shortest_le (h : g.shortest a b = some p) (w : g.FullWalk a b s) :
    p.length ≤ s.length
theorem AdjList.shortest_eq_none_iff : g.shortest a b = none ↔ ∀ s, ¬g.FullWalk a b s
```

### Instances

`Decidable (TransGen r a b)` and `Decidable (ReflTransGen r a b)` for any `[DecidableRel r]` on
a type with `[Fintype V] [DecidableEq V]`, computed by `reaches`.

`Reachability.Digraph` adds conversions to and from Mathlib's `Digraph`. Every result depends only
on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Design

`AdjList.reachableWithin g a k`, the set of vertices reachable in at most `k` steps, is defined
the simple way: expand everything found so far, `k` times. All the proofs are about this
definition. The efficient searches, `searchFrom` and `searchLayers`, are each related to it by a
single lemma. Searching `Fintype.card V` layers deep is enough, because a walk that repeats no
vertex has fewer than `card V` intermediate vertices.

`shortest` records each layer as the search runs, then rebuilds the walk backwards from `b`. At
each step it picks the least predecessor in the next layer down, which is why it needs
`LinearOrder V`: it makes the choice deterministic. So the walk returned is canonical, not
merely some shortest walk.

Vertex sets are Mathlib `Finset`s, which are lists with duplicates removed. That keeps everything
kernel-reducible, but `#eval` on graphs with thousands of vertices will be slow.

## Installation

Add the library to your `lakefile.toml`, pinned to a release tag:

```toml
[[require]]
name = "Reachability"
git = "https://github.com/Arrow7000/reachability"
rev = "v0.1.0"
```

Then run `lake update Reachability` and `import Reachability`.

Each release is built against one Lean and Mathlib version, and your project should use the
same ones:

| Release | Lean / Mathlib |
|---|---|
| `v0.1.0` | `v4.34.1` |

## Building

```bash
lake exe cache get   # download prebuilt Mathlib oleans
lake build
```
