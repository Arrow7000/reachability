import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Data.List.MinMax
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

section Reaches

variable [DecidableEq V]

/-- Depth-first search for `dest` from `current`, never re-entering a vertex in `seen`.
Returns `true` iff `dest` is reachable from `current` in zero or more steps
(see `reaches_sound` and `reaches_complete`). -/
def reaches [Fintype V] (g : AdjList V) (current dest : V) (seen : Finset V) : Bool :=
  if current = dest then true
  else if _h : current ∈ seen then false
  else decide (∃ child ∈ g current, reaches g child dest (insert current seen) = true)
termination_by Fintype.card V - seen.card
decreasing_by
  all_goals
    rw [Finset.card_insert_of_notMem _h]
    have := Finset.card_lt_univ_of_notMem _h
    omega

variable [Fintype V]

theorem reaches_self {a : V} {seen : Finset V} : g.reaches a a seen = true := by
  rw [reaches]
  simp

theorem reaches_sound {current dest : V} {seen : Finset V}
    (h : g.reaches current dest seen = true) : ReflTransGen g.Adj current dest := by
  fun_induction reaches g current dest seen with
  | case1 => exact .refl
  | case2 => contradiction
  | case3 current seen _ _ ih =>
    simp only [decide_eq_true_eq] at h
    obtain ⟨child, hchild, hrec⟩ := h
    exact .head hchild (ih child hrec)

/-- The search succeeds whenever there is a repetition-free walk that avoids `seen`. -/
theorem reaches_complete {current dest : V} {seen : Finset V} {post : List V}
    (w : g.FullWalk current dest post) (hnodup : (current :: post).Nodup)
    (hdisj : ∀ x ∈ current :: post, x ∉ seen) : g.reaches current dest seen = true := by
  fun_induction reaches g current dest seen generalizing post with
  | case1 => rfl
  | case2 current seen _ hin => exact absurd hin (hdisj current (by simp))
  | case3 current seen _ _ ih =>
    simp only [decide_eq_true_eq]
    cases post with
    | nil => exact ⟨dest, FullWalk.nil_iff.mp w, reaches_self⟩
    | cons x t =>
      obtain ⟨hx, w⟩ := FullWalk.cons_iff.mp w
      obtain ⟨hcurr, hnodup⟩ := List.nodup_cons.mp hnodup
      refine ⟨x, hx, ih x w hnodup fun y hy => ?_⟩
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hcurr (h ▸ hy), hdisj y (List.mem_cons_of_mem _ hy)⟩

theorem transGen_iff_exists_reaches {a b : V} :
    TransGen g.Adj a b ↔ ∃ c ∈ g a, g.reaches c b ∅ = true := by
  constructor
  · intro h
    obtain ⟨s, w⟩ := transGen_iff_exists_fullWalk.mp h
    obtain ⟨s, -, hb, w⟩ := w.exists_nodup
    cases s with
    | nil => exact ⟨b, FullWalk.nil_iff.mp w, reaches_self⟩
    | cons c s =>
      obtain ⟨hac, w⟩ := FullWalk.cons_iff.mp w
      exact ⟨c, hac, reaches_complete w (List.nodup_cons.mp hb).2 (by simp)⟩
  · rintro ⟨c, hc, h⟩
    exact .head' hc (reaches_sound h)

instance instDecidableTransGen (a b : V) : Decidable (TransGen g.Adj a b) :=
  decidable_of_iff _ transGen_iff_exists_reaches.symm

/-- The adjacency list of a decidable relation on a finite type. -/
def ofRel (r : V → V → Prop) [DecidableRel r] : AdjList V := fun a => Finset.univ.filter (r a)

omit [DecidableEq V] in
@[simp] theorem ofRel_adj (r : V → V → Prop) [DecidableRel r] : (ofRel r).Adj = r := by
  ext a b
  simp [ofRel]

end Reaches

/-! ### Shortest walks -/

section Shortest

variable [LinearOrder V]

/-- Search for a shortest continuation to `dest` of a walk that has just reached `current`, and
whose intermediate vertices so far are `pre`. Returns the intermediate vertices of the whole
walk. -/
def shortestAux [Fintype V] (g : AdjList V) (current dest : V) (pre : List V) : Option (List V) :=
  if current = dest then some pre
  else if _h : current ∈ pre then none
  else
    ((g current).sort (· ≤ ·)).filterMap (fun child => shortestAux g child dest (pre ++ [current]))
      |>.argmin List.length
termination_by Fintype.card V - pre.toFinset.card
decreasing_by
  all_goals
    have h' : current ∉ pre.toFinset := by simpa using _h
    have : (pre ++ [current]).toFinset = insert current pre.toFinset := by ext; simp
    rw [this, Finset.card_insert_of_notMem h']
    have := Finset.card_lt_univ_of_notMem h'
    omega

variable [Fintype V]

theorem shortestAux_self {a : V} {pre : List V} : g.shortestAux a a pre = some pre := by
  rw [shortestAux]
  simp

theorem shortestAux_sound {a current dest : V} {pre p : List V} (hw : g.FullWalk a current pre)
    (h : g.shortestAux current dest pre = some p) : g.FullWalk a dest p := by
  fun_induction shortestAux g current dest pre with
  | case1 =>
    cases h
    exact hw
  | case2 => contradiction
  | case3 current pre _ _ ih =>
    obtain ⟨child, hchild, hrec⟩ := List.mem_filterMap.mp (List.argmin_mem h)
    exact ih child (hw.snoc ((Finset.mem_sort _).mp hchild)) hrec

theorem shortestAux_complete {current dest : V} {pre post : List V}
    (w : g.FullWalk current dest post) (hnodup : (current :: post).Nodup)
    (hdisj : ∀ x ∈ current :: post, x ∉ pre) :
    ∃ p, g.shortestAux current dest pre = some p ∧ p.length ≤ pre.length + post.length + 1 := by
  fun_induction shortestAux g current dest pre generalizing post with
  | case1 => exact ⟨_, rfl, by omega⟩
  | case2 current pre _ hin => exact absurd hin (hdisj current (by simp))
  | case3 current pre _ _ ih =>
    -- the candidate continuation through the next vertex of `post`
    obtain ⟨q, hq, hqlen⟩ : ∃ q ∈ ((g current).sort (· ≤ ·)).filterMap
        (fun child => g.shortestAux child dest (pre ++ [current])),
        q.length ≤ pre.length + post.length + 1 := by
      cases post with
      | nil =>
        refine ⟨pre ++ [current], List.mem_filterMap.mpr ⟨dest, ?_, shortestAux_self⟩, by simp⟩
        exact (Finset.mem_sort _).mpr (FullWalk.nil_iff.mp w)
      | cons x t =>
        obtain ⟨hx, w⟩ := FullWalk.cons_iff.mp w
        obtain ⟨hcurr, hnodup⟩ := List.nodup_cons.mp hnodup
        obtain ⟨q, hq, hqlen⟩ := ih x w hnodup fun y hy => by
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hdisj y (List.mem_cons_of_mem _ hy), fun h => hcurr (h ▸ hy)⟩
        refine ⟨q, List.mem_filterMap.mpr ⟨x, (Finset.mem_sort _).mpr hx, hq⟩, ?_⟩
        simp at hqlen ⊢
        omega
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp
      (mt (List.argmin_eq_none (f := List.length)).mp (List.ne_nil_of_mem hq))
    exact ⟨p, hp, (List.le_of_mem_argmin hq hp).trans hqlen⟩

/-- A shortest walk from `a` to `b`, given by its intermediate vertices, or `none` if there is no
walk. -/
def shortest (g : AdjList V) (a b : V) : Option (List V) :=
  ((g a).sort (· ≤ ·)).filterMap (fun c => g.shortestAux c b []) |>.argmin List.length

theorem shortest_fullWalk {a b : V} {p : List V} (h : g.shortest a b = some p) :
    g.FullWalk a b p := by
  obtain ⟨c, hc, hrec⟩ := List.mem_filterMap.mp (List.argmin_mem h)
  exact shortestAux_sound (.direct ((Finset.mem_sort _).mp hc)) hrec

/-- Some candidate is at least as short as any given walk. -/
private theorem exists_candidate_le {a b : V} {s : List V} (w : g.FullWalk a b s) :
    ∃ q ∈ ((g a).sort (· ≤ ·)).filterMap (fun c => g.shortestAux c b []),
      q.length ≤ s.length := by
  obtain ⟨s', w', hmin⟩ := w.exists_shortest
  have hnodup := (w'.nodup_of_shortest hmin).1
  suffices ∃ q ∈ ((g a).sort (· ≤ ·)).filterMap (fun c => g.shortestAux c b []),
      q.length ≤ s'.length by
    obtain ⟨q, hq, hle⟩ := this
    exact ⟨q, hq, hle.trans (hmin s w)⟩
  cases s' with
  | nil =>
    refine ⟨[], List.mem_filterMap.mpr ⟨b, ?_, shortestAux_self⟩, le_rfl⟩
    exact (Finset.mem_sort _).mpr (FullWalk.nil_iff.mp w')
  | cons c t =>
    obtain ⟨hac, w'⟩ := FullWalk.cons_iff.mp w'
    obtain ⟨q, hq, hqlen⟩ := shortestAux_complete (pre := []) w' (List.nodup_cons.mp hnodup).2
      (by simp)
    exact ⟨q, List.mem_filterMap.mpr ⟨c, (Finset.mem_sort _).mpr hac, hq⟩, by simpa using hqlen⟩

/-- `shortest` returns a walk no longer than any other. -/
theorem shortest_le {a b : V} {p s : List V} (h : g.shortest a b = some p)
    (w : g.FullWalk a b s) : p.length ≤ s.length := by
  obtain ⟨q, hq, hqlen⟩ := exists_candidate_le w
  exact (List.le_of_mem_argmin hq h).trans hqlen

theorem shortest_isSome_iff {a b : V} : (g.shortest a b).isSome ↔ ∃ s, g.FullWalk a b s := by
  refine ⟨fun h => ⟨_, shortest_fullWalk (Option.some_get h).symm⟩, fun ⟨s, w⟩ => ?_⟩
  obtain ⟨q, hq, -⟩ := exists_candidate_le w
  exact Option.isSome_iff_ne_none.mpr (mt (List.argmin_eq_none (f := List.length)).mp (List.ne_nil_of_mem hq))

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
