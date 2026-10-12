import Mathlib.Combinatorics.Digraph.Basic
import Experiments.AbstractWalk

variable {V : Type}

def Digraph.toAdjList [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] : V → Finset V :=
  fun v => Finset.univ.filter (fun w => G.Adj v w)


def hasPath [Fintype V] [DecidableEq V]
    (yourAlgo : (V → Finset V) → V → V → Bool)
    (G : Digraph V) [DecidableRel G.Adj] (start finish : V) : Bool :=
  yourAlgo (G.toAdjList) start finish


theorem hasPathWithProof
  [Fintype V] [DecidableEq V]
  (yourAlgo : (V → Finset V) → V → V → Bool)
  (sound : ∀ (adjList : V → Finset V) (a b : V),
    yourAlgo adjList a b = true →
    Walk adjList a b)
  (complete : ∀ (adjList : V → Finset V) (a b : V),
    Walk adjList a b →
    yourAlgo adjList a b = true)
  (G : Digraph V) [DecidableRel G.Adj] (a b : V) :
  yourAlgo G.toAdjList a b = true ↔ Walk G.toAdjList a b :=
  ⟨sound (G.toAdjList) a b, complete (G.toAdjList) a b⟩





/-- Make a Digraph from a function that takes a vertex and returns all adjacent vertices -/
def Digraph.mkFromAdjList (adjList : V → Finset V) : Digraph V :=
  Digraph.mk (λ a b ↦ b ∈ adjList a)


def Digraph.mkFromRel (r : V → V → Prop)  : Digraph V :=
  Digraph.mk r


def Digraph.FullWalk_producible
  [Fintype V] [DecidableEq V] [LinearOrder V]
  (G : Digraph V)
  [DecidableRel G.Adj]
  (a b : V) : Producible (FullWalk G.toAdjList a b) :=
  FullWalk.producible G.toAdjList a b
