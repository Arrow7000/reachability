# Reachability

[![CI](https://github.com/Arrow7000/reachability/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Arrow7000/reachability/actions/workflows/lean_action_ci.yml)

Verified, kernel-reducible reachability and shortest walks for finite directed graphs, in Lean 4
and Mathlib.

Graphs are adjacency lists, `AdjList V := V → Finset V`. Reachability is Mathlib's own
`Relation.TransGen`, and it is decided by a breadth-first search that is proved correct. The
search is plain structural recursion, so `decide` works on small concrete graphs with no
`native_decide` needed (see [Performance](#performance)). The same instance also covers the transitive closure of any decidable
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

## Algorithm

`reaches` is a breadth-first search that expands only the newly reached vertices each round, and
stops as soon as `b` is found or a round reaches nothing new. `shortest` runs the same search,
remembering each round's vertices, then traces a walk back from `b`, picking the least
predecessor at each step (hence `LinearOrder V`).

Vertex sets are Mathlib `Finset`s, which are lists underneath, so set operations take linear
rather than constant time, and the worst case is `O(V · E)` rather than `O(V + E)`. In exchange,
the kernel can evaluate the search, which is what makes `decide` work.

## Performance

Representative timings on an Apple M4 Pro, from the benchmarks in [`bench/`](bench/Bench). They
double as tests, so `lake test` runs them all, printing each one's time.

Compiled code (`#eval`, `#guard`), from [`Bench/Eval.lean`](bench/Bench/Eval.lean):

| Graph | Vertices | Edges | Query | Time |
|---|---|---|---|---|
| path | 1,000 | 999 | reachable, 999 steps | 1.6 s |
| path | 1,000 | 999 | unreachable, whole path explored | 1.6 s |
| grid | 2,500 | 9,800 | corner to corner | 1.2 s |
| sparse random | 5,000 | ≈15,000 | reachable | 0.9 s |
| dense DAG | 1,000 | ≈500,000 | reachable, direct edge | 60 ms |
| dense DAG | 300 | ≈45,000 | unreachable, everything explored | 0.9 s |
| dense DAG | 1,000 | ≈500,000 | unreachable, everything explored | 34 s † |
| grid | 900 | 3,480 | `shortest`, corner to corner | 0.8 s |

Kernel proofs (`decide +kernel`), from [`Bench/Kernel.lean`](bench/Bench/Kernel.lean):

| Graph | Vertices | Query | Time |
|---|---|---|---|
| sparse random | 100 | reachable | 80 ms |
| grid | 100 | corner to corner | 2.7 s |
| path | 100 | reachable, 99 steps | 6.4 s |
| path | 200 | reachable, 199 steps | ≈ 4 min † |

† Too slow to run as a test, so recorded in a comment rather than run.

Kernel proofs work for graphs up to about a hundred vertices, and get slow quickly on long
walks. Plain `decide` first evaluates the instance during elaboration, which hits `maxRecDepth`
beyond a few dozen vertices; `decide +kernel` skips that step.

## Installation

Add the library to your `lakefile.toml`, pinned to a release tag:

```toml
[[require]]
name = "Reachability"
git = "https://github.com/Arrow7000/reachability"
rev = "v0.1.1"
```

Then run `lake update Reachability` and `import Reachability`.

Each release is built against one Lean and Mathlib version, and your project should use the
same ones:

| Release | Lean / Mathlib |
|---|---|
| `v0.1.1` | `v4.34.1` |
| `v0.1.0` | `v4.34.1` |

## Building

```bash
lake exe cache get   # download prebuilt Mathlib oleans
lake build
lake test            # run the benchmarks in bench/
```
