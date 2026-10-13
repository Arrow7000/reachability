import Bench.Graphs

/-!
# Compiled-code benchmarks

Checks run by the interpreter, as `#eval` or `#guard` would in a user's file. Each `#time` reports
its wall-clock time when this file is built (`lake build Bench.Eval`); the comments record the
times on an Apple M4 Pro.
-/

open Relation Bench

set_option Elab.async false

/-! ### Paths: one long chain, so `card V` rounds with a frontier of one vertex each -/

#time #guard decide (TransGen (path 300).Adj 0 299)  -- 60 ms
#time #guard decide (TransGen (path 1000).Adj 0 999)  -- 1.6 s
-- Unreachable: the whole path is explored before giving up.
#time #guard !decide (TransGen (path 1000).Adj 1 0)  -- 1.6 s
-- Unreachable, but `0` has no out-neighbours, so the search stops at once.
#time #guard !decide (TransGen (path 1000).Adj 999 0)  -- < 5 ms
#time #guard ((path 300).shortest 0 299).map List.length == some 298  -- 0.4 s

/-! ### Grids: many short walks, frontiers growing then shrinking -/

#time #guard decide (TransGen (grid 30).Adj 0 899)  -- 0.1 s
#time #guard decide (TransGen (grid 50).Adj 0 2499)  -- 1.2 s
#time #guard ((grid 30).shortest 0 899).map List.length == some 57  -- 0.8 s

/-! ### Dense DAGs: `n²/2` edges, but the target is found in the first round -/

#time #guard decide (TransGen (dag 300).Adj 0 299)  -- < 10 ms
#time #guard decide (TransGen (dag 1000).Adj 0 999)  -- 60 ms
-- Unreachable: every vertex after `1` is expanded, each adding up to `n` neighbours to a
-- list-based `Finset`. This is the worst case; at `n = 1000` it takes about 34 s.
#time #guard !decide (TransGen (dag 300).Adj 1 0)  -- 0.9 s

/-! ### Sparse random graphs: three pseudo-random out-neighbours per vertex -/

#time #guard decide (TransGen (random 1000 3 0).Adj 0 999)  -- 0.1 s
#time #guard decide (TransGen (random 5000 3 0).Adj 0 4999)  -- 0.9 s
#time #guard ((random 1000 3 0).shortest 0 999).map List.length == some 7  -- 0.3 s

/-! ### Arbitrary relations, through `AdjList.ofRel` (each vertex's neighbours found by
filtering all of `V`) -/

#time #guard decide (TransGen (fun a b : Fin 300 => b.val = a.val + 1) 0 299)  -- 80 ms
#time #guard decide (TransGen (fun a b : Fin 300 => b.val = 2 * a.val % 300) 1 256)  -- < 10 ms
