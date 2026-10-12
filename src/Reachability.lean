import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation

/-!
# Walks in finite graphs given by adjacency lists

A directed graph on `V` is presented by its successor function `g : V → Finset V`
(`AdjList V`). A walk from `a` to `b` is `Relation.TransGen g.Adj a b`; a walk that records its
intermediate vertices is `g.FullWalk a b segs`, which unfolds to `List.IsChain g.Adj` on the
vertex sequence `a :: segs ++ [b]`.

## Main results

* `AdjList.instDecidableTransGen`: reachability in an `AdjList` is decidable, by depth-first search.
* `Relation.instDecidableTransGen`: more generally, the transitive closure of any decidable
  relation on a finite type is decidable.
* `AdjList.shortest`: computes a shortest walk, see `shortest_fullWalk`, `shortest_le` and
  `shortest_isSome_iff`.
-/

open Relation

variable {V : Type*}

/-- A directed graph on `V`, presented by the function sending each vertex to its
out-neighbours. -/
abbrev AdjList (V : Type*) := V → Finset V

namespace AdjList

variable (g : AdjList V)

/-- There is an edge from `a` to `b`. -/
def Adj (a b : V) : Prop := b ∈ g a

@[simp] theorem adj_iff {a b : V} : g.Adj a b ↔ b ∈ g a := Iff.rfl

instance [DecidableEq V] : DecidableRel g.Adj := fun a b => inferInstanceAs (Decidable (b ∈ g a))

/-- A walk from `a` to `b` whose intermediate vertices, excluding both endpoints, are `segs`. -/
def FullWalk (a b : V) (segs : List V) : Prop := List.IsChain g.Adj (a :: segs ++ [b])

variable {g}

namespace FullWalk

@[simp] theorem nil_iff {a b : V} : g.FullWalk a b [] ↔ g.Adj a b := List.isChain_pair

@[simp] theorem cons_iff {a b c : V} {segs : List V} :
    g.FullWalk a c (b :: segs) ↔ g.Adj a b ∧ g.FullWalk b c segs :=
  List.isChain_cons_cons

theorem direct {a b : V} (h : g.Adj a b) : g.FullWalk a b [] := nil_iff.mpr h

theorem cons {a b c : V} {segs : List V} (h : g.Adj a b) (w : g.FullWalk b c segs) :
    g.FullWalk a c (b :: segs) :=
  cons_iff.mpr ⟨h, w⟩

/-- A walk through `b` is exactly a walk to `b` followed by a walk from `b`. -/
theorem append_iff {a b c : V} {s₁ s₂ : List V} :
    g.FullWalk a c (s₁ ++ b :: s₂) ↔ g.FullWalk a b s₁ ∧ g.FullWalk b c s₂ := by
  simp only [FullWalk, List.append_assoc, List.cons_append]
  exact List.isChain_cons_split

theorem append {a b c : V} {s₁ s₂ : List V} (w₁ : g.FullWalk a b s₁) (w₂ : g.FullWalk b c s₂) :
    g.FullWalk a c (s₁ ++ b :: s₂) :=
  append_iff.mpr ⟨w₁, w₂⟩

theorem snoc {a b c : V} {s : List V} (w : g.FullWalk a b s) (h : g.Adj b c) :
    g.FullWalk a c (s ++ [b]) :=
  w.append (direct h)

/-- Split a walk at its `i`th intermediate vertex. -/
theorem split_getElem {a b : V} {s : List V} (w : g.FullWalk a b s) (i : ℕ) (hi : i < s.length) :
    g.FullWalk a s[i] (s.take i) ∧ g.FullWalk s[i] b (s.drop (i + 1)) := by
  apply append_iff.mp
  rwa [List.getElem_cons_drop, List.take_append_drop]

theorem transGen {a b : V} {s : List V} (w : g.FullWalk a b s) : TransGen g.Adj a b := by
  induction s generalizing a with
  | nil => exact .single (nil_iff.mp w)
  | cons x s ih =>
    obtain ⟨h, w⟩ := cons_iff.mp w
    exact .head h (ih w)

/-- Every walk can be replaced by one of minimal length. -/
theorem exists_shortest {a b : V} {s : List V} (w : g.FullWalk a b s) :
    ∃ s', g.FullWalk a b s' ∧ ∀ s'', g.FullWalk a b s'' → s'.length ≤ s''.length := by
  classical
  have hP : ∃ n, ∃ s', s'.length = n ∧ g.FullWalk a b s' := ⟨_, s, rfl, w⟩
  obtain ⟨s', hlen, w'⟩ := Nat.find_spec hP
  exact ⟨s', w', fun s'' w'' => hlen ▸ Nat.find_min' hP ⟨s'', rfl, w''⟩⟩

/-- A shortest walk visits no vertex twice. -/
theorem nodup_of_shortest {a b : V} {s : List V} (w : g.FullWalk a b s)
    (hmin : ∀ s', g.FullWalk a b s' → s.length ≤ s'.length) :
    (a :: s).Nodup ∧ (b :: s).Nodup := by
  have hs : s.Nodup := by
    rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj heq
    have hi : i < s.length := hij.trans hj
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, Option.some_inj] at heq
    have := hmin _ ((w.split_getElem i hi).1.append (heq ▸ (w.split_getElem j hj).2))
    simp at this
    omega
  have ha : a ∉ s := fun hmem => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    have := hmin _ (w.split_getElem i hi).2
    simp at this
    omega
  have hb : b ∉ s := fun hmem => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    have := hmin _ (w.split_getElem i hi).1
    simp at this
    omega
  exact ⟨List.nodup_cons.mpr ⟨ha, hs⟩, List.nodup_cons.mpr ⟨hb, hs⟩⟩

/-- Every walk can be replaced by one that repeats no vertex. -/
theorem exists_nodup {a b : V} {s : List V} (w : g.FullWalk a b s) :
    ∃ s', (a :: s').Nodup ∧ (b :: s').Nodup ∧ g.FullWalk a b s' := by
  obtain ⟨s', w', hmin⟩ := w.exists_shortest
  exact ⟨s', (w'.nodup_of_shortest hmin).1, (w'.nodup_of_shortest hmin).2, w'⟩

end FullWalk

theorem transGen_iff_exists_fullWalk {a b : V} : TransGen g.Adj a b ↔ ∃ s, g.FullWalk a b s := by
  refine ⟨fun h => ?_, fun ⟨_, w⟩ => w.transGen⟩
  induction h using TransGen.head_induction_on with
  | single h => exact ⟨[], .direct h⟩
  | head h _ ih =>
    obtain ⟨s, w⟩ := ih
    exact ⟨_, .cons h w⟩

/-! ### Deciding reachability -/

section Reachable

variable [DecidableEq V]

/-- The vertices reachable from `a` by a walk of between `1` and `k` edges, computed
breadth-first. -/
def reachableWithin (g : AdjList V) (a : V) : ℕ → Finset V
  | 0 => ∅
  | k + 1 => g a ∪ (g.reachableWithin a k).biUnion g

theorem mem_reachableWithin {a x : V} {k : ℕ} :
    x ∈ g.reachableWithin a k ↔ ∃ s, g.FullWalk a x s ∧ s.length < k := by
  induction k generalizing x with
  | zero => simp [reachableWithin]
  | succ k ih =>
    simp only [reachableWithin, Finset.mem_union, Finset.mem_biUnion, ih]
    constructor
    · rintro (hx | ⟨y, ⟨s, w, hs⟩, hx⟩)
      · exact ⟨[], .direct hx, by simp⟩
      · exact ⟨s ++ [y], w.snoc hx, by simp; omega⟩
    · rintro ⟨s, w, hs⟩
      rcases s.eq_nil_or_concat' with rfl | ⟨s, y, rfl⟩
      · exact .inl (FullWalk.nil_iff.mp w)
      · obtain ⟨w, hy⟩ := FullWalk.append_iff.mp w
        exact .inr ⟨y, ⟨s, w, by simp at hs; omega⟩, FullWalk.nil_iff.mp hy⟩

variable [Fintype V]

/-- A repetition-free walk has fewer than `card V` intermediate vertices, so it suffices to search
`card V` layers deep. -/
theorem transGen_iff_mem_reachableWithin {a b : V} :
    TransGen g.Adj a b ↔ b ∈ g.reachableWithin a (Fintype.card V) := by
  rw [mem_reachableWithin, transGen_iff_exists_fullWalk]
  refine ⟨fun ⟨s, w⟩ => ?_, fun ⟨s, w, _⟩ => ⟨s, w⟩⟩
  obtain ⟨s, -, hb, w⟩ := w.exists_nodup
  have := hb.length_le_card
  exact ⟨s, w, by simp at this; omega⟩

instance instDecidableTransGen (a b : V) : Decidable (TransGen g.Adj a b) :=
  decidable_of_iff _ transGen_iff_mem_reachableWithin.symm

/-- The adjacency list of a decidable relation on a finite type. -/
def ofRel (r : V → V → Prop) [DecidableRel r] : AdjList V := fun a => Finset.univ.filter (r a)

omit [DecidableEq V] in
@[simp] theorem ofRel_adj (r : V → V → Prop) [DecidableRel r] : (ofRel r).Adj = r := by
  ext a b
  simp [ofRel]

end Reachable

/-! ### Shortest walks -/

section Shortest

variable [LinearOrder V]

/-- A walk from `a` to `x` of fewer than `k` edges, given by its intermediate vertices, provided
`x ∈ g.reachableWithin a k`. Built backwards, choosing the least predecessor one layer closer
to `a` at each step. -/
def pathTo (g : AdjList V) (a : V) : ℕ → V → List V
  | 0, _ => []
  | k + 1, x =>
    if x ∈ g a then []
    else if h : ((g.reachableWithin a k).filter (x ∈ g ·)).Nonempty then
      g.pathTo a k (((g.reachableWithin a k).filter (x ∈ g ·)).min' h) ++
        [((g.reachableWithin a k).filter (x ∈ g ·)).min' h]
    else []

theorem pathTo_spec {a x : V} {k : ℕ} (hx : x ∈ g.reachableWithin a k) :
    g.FullWalk a x (g.pathTo a k x) ∧ (g.pathTo a k x).length < k := by
  induction k generalizing x with
  | zero => simp [reachableWithin] at hx
  | succ k ih =>
    simp only [pathTo]
    split_ifs with hxa h
    · exact ⟨.direct hxa, by simp⟩
    · have hy := Finset.mem_filter.mp (Finset.min'_mem _ h)
      obtain ⟨w, hlen⟩ := ih hy.1
      exact ⟨w.snoc hy.2, by simp; omega⟩
    · simp only [reachableWithin, Finset.mem_union, Finset.mem_biUnion] at hx
      obtain hx | ⟨y, hy, hxy⟩ := hx
      · exact absurd hx hxa
      · exact absurd ⟨y, Finset.mem_filter.mpr ⟨hy, hxy⟩⟩ h

variable [Fintype V]

/-- A shortest walk from `a` to `b`, given by its intermediate vertices, or `none` if there is no
walk. -/
def shortest (g : AdjList V) (a b : V) : Option (List V) :=
  if h : b ∈ g.reachableWithin a (Fintype.card V) then
    some (g.pathTo a (Nat.find (p := (b ∈ g.reachableWithin a ·)) ⟨_, h⟩) b)
  else none

theorem shortest_fullWalk {a b : V} {p : List V} (h : g.shortest a b = some p) :
    g.FullWalk a b p := by
  unfold shortest at h
  split_ifs at h with hb
  obtain rfl := Option.some_inj.mp h
  have hex : ∃ k, b ∈ g.reachableWithin a k := ⟨_, hb⟩
  exact (pathTo_spec (Nat.find_spec hex)).1

/-- `shortest` returns a walk no longer than any other. -/
theorem shortest_le {a b : V} {p s : List V} (h : g.shortest a b = some p)
    (w : g.FullWalk a b s) : p.length ≤ s.length := by
  unfold shortest at h
  split_ifs at h with hb
  obtain rfl := Option.some_inj.mp h
  have hex : ∃ k, b ∈ g.reachableWithin a k := ⟨_, hb⟩
  have h₁ := (pathTo_spec (Nat.find_spec hex)).2
  have h₂ := Nat.find_min' hex (mem_reachableWithin.mpr ⟨s, w, Nat.lt_succ_self _⟩)
  omega

theorem shortest_isSome_iff {a b : V} : (g.shortest a b).isSome ↔ ∃ s, g.FullWalk a b s := by
  rw [← transGen_iff_exists_fullWalk, transGen_iff_mem_reachableWithin]
  unfold shortest
  split_ifs with hb <;> simp [hb]

theorem shortest_eq_none_iff {a b : V} : g.shortest a b = none ↔ ∀ s, ¬g.FullWalk a b s := by
  rw [← Option.not_isSome_iff_eq_none, shortest_isSome_iff, not_exists]

end Shortest

end AdjList

namespace Relation

variable [Fintype V] [DecidableEq V] (r : V → V → Prop) [DecidableRel r]

instance (priority := low) instDecidableTransGen (a b : V) : Decidable (TransGen r a b) :=
  decidable_of_iff (TransGen (AdjList.ofRel r).Adj a b) (by rw [AdjList.ofRel_adj])

instance (priority := low) instDecidableReflTransGen (a b : V) : Decidable (ReflTransGen r a b) :=
  decidable_of_iff (b = a ∨ TransGen r a b) reflTransGen_iff_eq_or_transGen.symm

end Relation
