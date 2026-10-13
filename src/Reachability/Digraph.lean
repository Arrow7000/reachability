/-
Copyright (c) 2025 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/
import Mathlib.Combinatorics.Digraph.Basic
import Reachability

variable {V : Type*}

/-- The digraph whose edges are those of an adjacency list. -/
def Digraph.ofAdjList (g : AdjList V) : Digraph V := ⟨g.Adj⟩

@[simp] theorem Digraph.ofAdjList_adj (g : AdjList V) : (Digraph.ofAdjList g).Adj = g.Adj := rfl

variable [Fintype V]

/-- The adjacency list of a finite digraph with decidable adjacency. -/
def Digraph.toAdjList (G : Digraph V) [DecidableRel G.Adj] : AdjList V := AdjList.ofRel G.Adj

@[simp] theorem Digraph.toAdjList_adj (G : Digraph V) [DecidableRel G.Adj] :
    G.toAdjList.Adj = G.Adj :=
  AdjList.ofRel_adj _

/-- Reachability in a finite digraph is decidable, via `Relation.instDecidableTransGen`. -/
example [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (a b : V) :
    Decidable (Relation.TransGen G.Adj a b) :=
  inferInstance

/-- A shortest walk in a finite digraph, see `AdjList.shortest`. -/
def Digraph.shortestWalk [LinearOrder V] (G : Digraph V) [DecidableRel G.Adj] (a b : V) :
    Option (List V) :=
  G.toAdjList.shortest a b
