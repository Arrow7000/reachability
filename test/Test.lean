import Bench.Graphs

/-!
# Tests

Small, fast correctness checks, run by `lake test`. The larger timed examples are in `bench/`.
-/

open Relation Bench

/-- 0 → 1 → 2 → 0, and separately 3 → 4. -/
def g : AdjList (Fin 5)
  | 0 => {1} | 1 => {2} | 2 => {0} | 3 => {4} | 4 => ∅

/-! ### Kernel proofs -/

example : TransGen g.Adj 0 2 := by decide
example : TransGen g.Adj 2 2 := by decide
example : ¬TransGen g.Adj 0 3 := by decide
example : ¬TransGen g.Adj 4 3 := by decide
example : ReflTransGen g.Adj 3 3 := by decide
example : ReflTransGen (fun a b : Fin 10 => b.val = a.val + 3) 1 7 := by decide
example : ¬TransGen (fun a b : Fin 10 => b.val = a.val + 3) 7 1 := by decide
example : TransGen (path 30).Adj 0 29 := by decide
example : TransGen (grid 6).Adj 0 35 := by decide +kernel
example : ¬TransGen (path 50).Adj 49 0 := by decide +kernel
example : (grid 5).shortest 0 24 = some [1, 2, 3, 4, 9, 14, 19] := by decide +kernel

/-! ### Compiled code -/

#guard g.shortest 0 2 == some [1]
#guard g.shortest 2 2 == some [0, 1]
#guard g.shortest 0 3 == none
#guard decide (TransGen (path 200).Adj 0 199)
#guard !decide (TransGen (path 200).Adj 1 0)
#guard decide (TransGen (grid 15).Adj 0 224)
#guard !decide (TransGen (dag 50).Adj 1 0)
#guard decide (TransGen (random 300 3 0).Adj 0 299)
#guard ((path 200).shortest 0 199).map List.length == some 198
#guard ((grid 15).shortest 0 224).map List.length == some 27
#guard (dag 50).shortest 0 49 == some []
