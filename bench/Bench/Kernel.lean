/-
Copyright (c) 2025 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/
import Bench.Graphs

/-!
# Kernel benchmarks

Proofs by `decide`, which the kernel checks by evaluating the search itself. This is far slower
than compiled code: the kernel evaluates lazily, without compiled data structures, so it pays for
every `Finset` operation symbolically.

Plain `decide` also evaluates the search during elaboration first, which hits `maxRecDepth` on
graphs of more than a few dozen vertices; `decide +kernel` skips that step. Each `#time` reports
its wall-clock time when this file is built (`lake build Bench.Kernel`); the comments record the
times on an Apple M4 Pro.
-/

open Relation Bench

set_option Elab.async false

#time example : TransGen (path 30).Adj 0 29 := by decide  -- 0.4 s
#time example : TransGen (grid 5).Adj 0 24 := by decide  -- 0.3 s

#time example : TransGen (path 50).Adj 0 49 := by decide +kernel  -- 0.8 s
-- Kernel time grows steeply along long paths: `path 200` takes about 4 minutes.
#time example : TransGen (path 100).Adj 0 99 := by decide +kernel  -- 6.4 s
#time example : ¬TransGen (path 100).Adj 99 0 := by decide +kernel  -- < 10 ms
#time example : TransGen (grid 6).Adj 0 35 := by decide +kernel  -- 0.2 s
#time example : TransGen (grid 10).Adj 0 99 := by decide +kernel  -- 2.7 s
#time example : TransGen (random 100 3 0).Adj 0 99 := by decide +kernel  -- 80 ms
#time example : TransGen (dag 300).Adj 0 299 := by decide +kernel  -- 5.7 s
#time example : (grid 5).shortest 0 24 = some [1, 2, 3, 4, 9, 14, 19] := by decide +kernel  -- 0.2 s
