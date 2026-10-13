/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/
import Reachability
import Bench.Time

/-!
# Graph families for the benchmarks

Neighbours are computed directly rather than by filtering `Finset.univ`, as a real user's graph
would be.
-/

namespace Bench

/-- The vertices among `ks` that are in range. -/
def ofNats (n : ℕ) (ks : List ℕ) : Finset (Fin n) :=
  (ks.filterMap fun k => if h : k < n then some ⟨k, h⟩ else none).toFinset

/-- `0 → 1 → ⋯ → n - 1`. -/
def path (n : ℕ) : AdjList (Fin n) := fun i => ofNats n [i.val + 1]

/-- A `w × w` grid, with edges to the up to four orthogonal neighbours. -/
def grid (w : ℕ) : AdjList (Fin (w * w)) := fun i =>
  let i := i.val
  let r := i / w
  let c := i % w
  ofNats (w * w) <|
    (if r + 1 < w then [i + w] else []) ++ (if 0 < r then [i - w] else []) ++
    (if c + 1 < w then [i + 1] else []) ++ (if 0 < c then [i - 1] else [])

/-- Every edge `i → j` with `i < j`. -/
def dag (n : ℕ) : AdjList (Fin n) := fun i => ofNats n (List.range' (i.val + 1) (n - i.val - 1))

/-- `d` pseudo-random out-neighbours per vertex (a linear congruential generator). -/
def random (n d seed : ℕ) : AdjList (Fin n) := fun i =>
  ofNats n <| (List.range d).map fun j => (seed + 1103515245 * (i.val * d + j) + 12345) % 2147483648 % n

end Bench
