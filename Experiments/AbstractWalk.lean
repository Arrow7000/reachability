import Experiments.Producible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Lattice

section List

@[simp]
def List.dropEnd (l : List α) (n : Nat) := l.reverse.drop n |>.reverse



@[simp high]
theorem List.dropEnd_dropEnd {l : List α} : (l.dropEnd i).dropEnd j = l.dropEnd (i+j) := by simp


@[grind →] theorem List.rev_pigeonhole_principle {l : List Nat}
    (nodup : l.Nodup)
    (heach : ∀ item ∈ l, item < n)
    (hitemlen : item < n)
    (hitemin : item ∉ l)
    : l.length < n := by
  let s : Finset Nat := Finset.mk l nodup
  have hs1 (x) : x ∈ l ↔ x ∈ s := Iff.rfl
  have hs2 : l.length = s.card := rfl
  simp only [hs1, implies_true, hs2] at *
  have : s ⊂ Finset.range n := by
    constructor
    · intro a ha
      simp_all
    · intro hs
      exact hitemin (hs (by simpa using hitemlen))
  simpa using Finset.card_lt_card this


@[grind →]
theorem List.nodup_lte_fintype_mem [Fintype V]
  {list : List V}
  (seensNodup : list.Nodup)
  (hin : newItem ∉ list)
  : Fintype.card V - (list.length + 1) < Fintype.card V - list.length := by
  have hcons : (newItem :: list).Nodup := List.nodup_cons.mpr ⟨hin, seensNodup⟩
  have hlen : (newItem :: list).length ≤ Fintype.card V := List.Nodup.length_le_card hcons
  simp only [List.length_cons] at hlen
  omega


end List









@[grind →] theorem Finset.rev_pigeonhole_principle {s : Finset Nat}
    (heach : ∀ item ∈ s, item < n)
    (hitemlen : item < n)
    (hitemin : item ∉ s)
    : s.card < n := by
  have : s ⊂ Finset.range n := by
    constructor
    · intro a ha
      simp_all
    · intro hs
      exact hitemin (hs (by simpa using hitemlen))
  simpa using Finset.card_lt_card this



@[grind →] theorem Finset.rev_pigeonhole_principle2 {s : Finset Nat}
    (heach : ∀ item ∈ s, item < n)
    (hitemlen₁ : item₁ < n)
    (hitemin₁ : item₁ ∉ s)
    (hitemlen₂ : item₂ < n)
    (hitemin₂ : item₂ ∉ s)
    (hneq : item₁ ≠ item₂)
    : s.card + 1 < n := by
  have : insert item₁ s ⊂ Finset.range n := by
    constructor
    · intro a ha
      simp_all
      grind
    · intro hs
      have := hs (by simpa using hitemlen₂)
      refine hitemin₂ ?_
      simp [*] at this
      simp [*] at *

  have : s ⊂ insert item₁ s := by grind
  have := Finset.card_lt_card this
  grind








variable {V : Type} [Fintype V] [DecidableEq V]

namespace LocalDefs

/-- A graph is defined abstractly as a function that given a node ID returns the set of connected nodes it points to -/
abbrev Graph (V:=V) := V → Finset V

end LocalDefs
export LocalDefs (Graph)



section Walk



instance : Membership V { list : List V // list.Nodup } where
  mem l node := node ∈ l.val


/-- Node `v` directly references node `u`. Because `u` is in the set of nodes that `v` connects to. -/
@[reducible, simp]
def DirectRef (graph : Graph) (v : V) (u : V) := u ∈ graph v



/-- `origin` leads to `dest`, either directly or indirectly -/
@[grind cases]
inductive Walk (graph : Graph) : (origin dest : V) → Prop
  | direct :
    DirectRef graph origin dest →
    Walk graph origin dest

  | tail :
    DirectRef graph a b →
    (walk : Walk graph b c) →
    Walk graph a c





/-- If a thing only has a single ref and that ref is back to itself, it cannot lead to anywhere else -/
@[grind =>]
theorem Walk.selfRef_nwalk_elsewhere {graph : Graph} (h : graph current = {current}) : ∀ dest ≠ current, ¬Walk graph current dest := by
  intro dest destneq walk
  induction walk with
  | direct hh =>
    simp at hh
    rw [h] at hh
    simp at hh
    contradiction
  | tail dref walk ih =>
    simp at dref
    rw [h] at dref
    simp at dref
    subst_eqs
    rw [h] at ih
    simp at ih
    subst_eqs
    contradiction





@[grind =>] theorem Walk.leaf_no_walk {graph : Graph} (h : graph a = ∅) : ∀ {b}, ¬Walk graph a b := by
  intro b nwalk
  induction nwalk
  · simp [*] at *
  · grind



/-- Glue together two FullWalks that share a common intermediate node.
This replaces the `.indirect` constructor from the original definition. -/
theorem Walk.append
    (walk₁ : Walk graph a b)
    (walk₂ : Walk graph b c)
    : Walk graph a c := by
  induction walk₁ generalizing c with
  | direct hdref =>
    exact .tail hdref walk₂
  | tail hdref _ ih =>
    exact .tail hdref (ih walk₂)





/-- Walk containing all traversed nodes -/
@[grind cases]
inductive FullWalk (graph : Graph) : (origin dest : V) → (segments : List V) → Prop where
  | direct :
    DirectRef graph origin dest →
    FullWalk graph origin dest []

  | tail :
    DirectRef graph a b →
    (walk : FullWalk graph b c segments) →
    FullWalk graph a c (b :: segments)




@[grind →]
theorem FullWalk.toWalk : FullWalk graph origin dest segments → Walk graph origin dest := by
  intro fw
  induction fw
  · expose_names
    refine .direct h
  · expose_names
    exact Walk.tail h walk_ih


@[grind →]
theorem Walk.toFullWalk : Walk graph origin dest → ∃ segments, FullWalk graph origin dest segments := by
  intro walk
  induction walk
  · expose_names
    exists []
    refine .direct h
  · expose_names
    obtain ⟨segments,fw⟩ := walk_ih
    exists b :: segments
    refine .tail h fw




@[grind .]
theorem FullWalk.not_Walk : (∀ segments, ¬FullWalk ctx origin dest segments) → ¬Walk ctx origin dest := by grind


@[grind =>]
theorem Walk.not_FullWalk : ¬Walk ctx origin dest → ∀ segments, ¬FullWalk ctx origin dest segments := by grind









/-- Append a direct reference to the end of a walk -/
theorem FullWalk.snoc
    (hwalk : FullWalk graph origin bum segments)
    (hdref : DirectRef graph bum dest)
    : FullWalk graph origin dest (segments ++ [bum]) := by
  induction hwalk generalizing dest with
  | direct hdref' =>
    simp
    exact .tail hdref' (.direct hdref)
  | tail hdref' _ ih =>
    simp
    exact .tail hdref' (ih hdref)


/-- Glue together two FullWalks that share a common intermediate node.
This replaces the `.indirect` constructor from the original definition. -/
theorem FullWalk.append
    (walk₁ : FullWalk graph a b segments₁)
    (walk₂ : FullWalk graph b c segments₂)
    : FullWalk graph a c (segments₁ ++ [b] ++ segments₂) := by
  induction walk₁ generalizing c segments₂ with
  | direct hdref =>
    simp
    exact .tail hdref walk₂
  | tail hdref _ ih =>
    simp only [List.cons_append]
    exact .tail hdref (ih walk₂)


@[grind =>]
theorem FullWalk.ref_self_no_dest {graph : Graph}
  (h : graph a = {a})
  (hneq : a ≠ dest)
  : ∀ {segments}, ¬FullWalk graph a dest segments := by grind







/-- lemma for proving that a thing either links directly or links to the first  -/
@[grind →]
lemma FullWalk.segments_structure
  (fw : FullWalk graph origin dest segments)
  : (segments = [] ∧ DirectRef graph origin dest)
    ∨ ∃ b tailSegs, segments = b :: tailSegs ∧
                     DirectRef graph origin b ∧
                     FullWalk graph b dest tailSegs := by
  induction fw with
  | direct dref =>
    left
    exact ⟨rfl, dref⟩
  | tail dref walk ih => tauto


@[grind .]
theorem FullWalk.ref_iff_dest
  (fw : FullWalk graph origin dest segments)
  (h : graph origin = {b})
  : b = dest ∨ ∃ tailSegs, ∃ (_segPrf : segments = b :: tailSegs), FullWalk graph b dest tailSegs := by
  -- Apply the segments_structure lemma
  have struct := FullWalk.segments_structure fw
  cases struct with
  | inl direct_case =>
    -- segments = [] ∧ DirectRef ctx (ctx[origin]) dest
    obtain ⟨hsegs, dref⟩ := direct_case
    -- We have DirectRef ctx (.ref b) dest, which means b = dest
    -- rw [h] at dref
    simp at dref
    rw [h] at dref
    simp [*] at dref ⊢
    tauto
  | inr exists_first =>
    -- ∃ b' tailSegs, segments = b' :: tailSegs ∧ DirectRef ctx (ctx[origin]) b' ∧ FullWalk ctx b' dest tailSegs
    obtain ⟨b', tailSegs, segs_eq, dref, walk⟩ := exists_first
    simp [*] at dref ⊢
    subst_eqs
    simp [*]














/-- Type-valued induction principle for `Finset` that processes elements in order using `min'`.
For a `Prop`-valued version, see `Finset.induction_on`. -/
@[elab_as_elim]
def Finset.minRecOn {α : Type*} [DecidableEq α] [LinearOrder α] {motive : Finset α → Sort*}
    (s : Finset α)
    (empty : motive ∅)
    (insert_min : ∀ (a : α) (s : Finset α), a ∉ s → (∀ x ∈ s, a < x) → motive s → motive (insert a s))
    : motive s :=
  if h : s.Nonempty then
    let m := s.min' h
    have hmem : m ∈ s := s.min'_mem h
    have hlt : ∀ x ∈ s.erase m, m < x := fun x hx => by
      have hxs : x ∈ s := Finset.mem_of_mem_erase hx
      have hne : x ≠ m := Finset.ne_of_mem_erase hx
      exact lt_of_le_of_ne (s.min'_le x hxs) hne.symm
    have hnotmem : m ∉ s.erase m := Finset.notMem_erase m s
    have : (s.erase m).card < s.card := Finset.card_erase_lt_of_mem hmem
    (s.insert_erase hmem) ▸ insert_min m (s.erase m) hnotmem hlt (Finset.minRecOn (s.erase m) empty insert_min)
  else
    have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    this ▸ empty
termination_by s.card

section MinRecOnExamples

-- Example 1: Construct a list from a finset (Sort-valued elimination with induction tactic)
example (s : Finset ℕ) : List ℕ := by
  induction s using Finset.minRecOn with
  | empty => exact []
  | insert_min a s' _ _ ih => exact a :: ih

-- Example 2: A simple Prop proof using the induction tactic
example (s : Finset ℕ) : s.card = s.card := by
  induction s using Finset.minRecOn with
  | empty => rfl
  | insert_min a s' ha_notin _ ih => rfl

-- Example 3: Direct term-mode usage (not using induction tactic)
def Finset.sumViaMinRec (s : Finset ℕ) : ℕ :=
  Finset.minRecOn s
    0  -- empty case
    (fun a _ _ _ acc => a + acc)  -- insert_min case

lemma Finset.sumViaMinRec_example : Finset.sumViaMinRec {3, 1, 4, 1, 5, 9, 2, 6} = 30 := by native_decide

-- Example 4: Construct a sorted list (showing the key advantage: elements come out in order)
def Finset.toAscList (s : Finset ℕ) : List ℕ :=
  Finset.minRecOn s
    []
    (fun a _ _ _ rest => a :: rest)

lemma Finset.toAscList_example : Finset.toAscList {5, 3, 8, 1, 9} = [1, 3, 5, 8, 9] := by native_decide

-- Example 5: Demonstrate access to the ordering hypothesis in a proof
example (s : Finset ℕ) : True := by
  induction s using Finset.minRecOn with
  | empty => trivial
  | insert_min a s' ha_notin hlt ih => trivial

-- Example 6: Build a witness that uses the ordering
def Finset.headIfNonempty (s : Finset ℕ) : Option ℕ :=
  Finset.minRecOn s
    none
    (fun a _ _ _ _ => some a)

lemma Finset.headIfNonempty_example : Finset.headIfNonempty {5, 3, 8} = some 3 := by native_decide
lemma Finset.headIfNonempty_empty : Finset.headIfNonempty ∅ = none := by native_decide

end MinRecOnExamples







omit [Fintype V] [DecidableEq V] in
/-- A walk's origin always links directly to its first path segment -/
@[grind .]
theorem FullWalk.ref_segment_cons {tail : List V}
  (h : FullWalk ctx origin dest segments)
  (hsegeq : segments = head :: tail)
  : DirectRef ctx origin head := by
  induction h generalizing tail head with
  | direct h => simp at hsegeq
  | tail dref walk ih => grind




/-- A walk's last segment always links directly to its destination -/
@[grind →]
theorem FullWalk.ref_segment_arse
  (h : FullWalk graph origin dest segments)
  (hsegeq : segments = body ++ [bum])
  : DirectRef graph bum dest := by
  induction h generalizing body bum with
  | direct h => simp at hsegeq
  | tail dref walk ih =>
    expose_names
    cases segments_1 using List.reverseRecOn with
    | nil =>
      have : body = [] := by
        cases body with
        | nil => rfl
        | cons _ _ => simp at hsegeq
      rw [this] at hsegeq
      simp at hsegeq
      subst_eqs
      simp at ih
      cases walk
      trivial
    | append_singleton body' bum' =>
      have : b :: (body' ++ [bum']) = (b :: body') ++ [bum'] := by grind
      rw [this] at hsegeq
      have : b :: body' = body := List.append_inj_left' hsegeq rfl
      subst_eqs
      simp at hsegeq
      subst_eqs
      exact ih rfl





omit [Fintype V] [DecidableEq V] in
/-- If path traverses through at least one segment, given a walk, return a new walk with the origin snipped off the start -/
@[grind →]
theorem FullWalk.cons_head_segment {tail : List V}
  (h : FullWalk ctx origin dest segments)
  (hsegeq : segments = head :: tail)
  : FullWalk ctx head dest tail := by grind



/-- If path traverses through at least one segment, given a walk, return a new walk with the dest snipped off the end -/
@[grind →]
theorem FullWalk.snoc_arse_segment
  (h : FullWalk ctx origin dest segments)
  (hsegeq : segments = body ++ [bum])
  : FullWalk ctx origin bum body := by
  induction h generalizing body with
  | direct h => simp at hsegeq
  | tail dref walk ih =>
    expose_names
    induction segments_1 using List.reverseRecOn with
    | nil =>
      have : body = [] := by
        cases body with
        | nil => rfl
        | cons _ _ => simp at hsegeq
      subst_eqs
      refine .direct dref
    | append_singleton body' bum' ih' =>
      have : b :: (body' ++ [bum']) = (b :: body') ++ [bum'] := by grind
      rw [this] at hsegeq
      have : b :: body' = body := List.append_inj_left' hsegeq rfl
      subst_eqs
      simp at hsegeq
      subst_eqs
      refine .tail dref (ih rfl)

omit [Fintype V] [DecidableEq V] in
/-- Reverse induction principle for `FullWalk`. Like `List.reverseRecOn`, this lets you do induction
from the back of the walk, peeling off the last segment at each step.

To prove a property about an arbitrary `FullWalk graph origin dest segments`, it suffices to prove:
1. The base case for direct walks (empty segments)
2. The inductive case: if it holds for a walk from `origin` to `penult` with segments `init`,
   and there's a direct reference from `penult` to `dest`,
   then it holds for the walk from `origin` to `dest` with segments `init ++ [penult]`.
-/
@[elab_as_elim]
theorem FullWalk.snoc_induction
    {motive : ∀ (origin dest : V) (segments : List V), FullWalk graph origin dest segments → Prop}
    {origin dest : V} {segments : List V}
    (h : FullWalk graph origin dest segments)
    (direct : ∀ {origin} {dest} (hdref : DirectRef graph origin dest),
              motive origin dest [] (.direct hdref))
    (snoc : ∀ {origin} {bum} {dest} {body}
              (hbody : FullWalk graph origin bum body)
              (hdirect : DirectRef graph bum dest),
              motive origin bum body hbody →
              motive origin dest (body ++ [bum])
                (hbody.snoc hdirect))
    : motive origin dest segments h := by
  induction segments using List.reverseRecOn generalizing dest with
  | nil =>
    cases h with
    | direct dref => exact direct dref
  | append_singleton init penult ih =>
    have hwalk : FullWalk graph origin penult init := h.snoc_arse_segment rfl
    have hdref : DirectRef graph penult dest := h.ref_segment_arse rfl
    have hmotive := snoc hwalk hdref (ih hwalk)
    have heq : h = hwalk.snoc hdref := by apply proof_irrel
    rw [heq]
    exact hmotive









@[grind →]
theorem FullWalk.from_seg_to_end
  (h : FullWalk ctx origin dest segments)
  (hindexa : Nat)
  (hindexalt : hindexa < segments.length)
  : FullWalk ctx segments[hindexa] dest (segments.drop (hindexa+1)) := by
  induction segments generalizing hindexa origin with
  | nil => grind
  | cons head tail ih =>
    cases hindexa with
    | zero => grind
    | succ hindexa' =>
      have := FullWalk.cons_head_segment h rfl
      simp [*]
      grind




@[grind →]
theorem FullWalk.from_start_to_seg
  (h : FullWalk ctx origin dest segments)
  (hindexb : Nat)
  (hindexblt : hindexb < segments.length)
  : FullWalk ctx origin segments[hindexb] (segments.take hindexb) := by
  induction segments using List.reverseRecOn generalizing hindexb dest with
  | nil => grind
  | append_singleton body bum ih =>
    have := h.snoc_arse_segment rfl
    rw [body.length_append] at hindexblt
    simp at hindexblt
    if hlen : hindexb = body.length then
      subst_eqs
      simpa using this
    else
      replace hindexblt : hindexb < body.length := by omega
      replace ih := ih this hindexb hindexblt
      simp [*]
      have := body.take_append_of_le_length (i:=hindexb) (by grind) (l₂:=[bum])
      rw [this]
      exact ih



@[grind →]
theorem FullWalk.from_start_to_seg'
  (h : FullWalk ctx origin dest segments)
  (hindexb : Nat)
  (hindexblt : hindexb < segments.length)
  : FullWalk ctx origin segments[hindexb] (segments.dropEnd (segments.length - hindexb)) := by
  induction segments using List.reverseRecOn generalizing hindexb dest with
  | nil => grind
  | append_singleton body bum ih =>
    have := h.snoc_arse_segment rfl
    rw [body.length_append] at hindexblt
    simp at hindexblt
    if hlen : hindexb = body.length then
      subst_eqs
      simpa using this
    else
      replace hindexblt : hindexb < body.length := by omega
      replace ih := ih this hindexb hindexblt
      simp [*] at ih ⊢
      have : (List.drop (body.length + 1 - hindexb) (bum :: body.reverse)).reverse = (List.drop (body.length - hindexb) body.reverse).reverse := by
        simp
        rw [Nat.sub_add_comm]
        rfl
        omega
      rw [this]
      exact ih












/-- If the origin is in the segments list, then it's possible to create a walk from origin to dest that's shorter in length and whose segments don't contain origin! -/
theorem FullWalk.get_orig_nin_segs
  (h : FullWalk ctx origin dest segments)
  : ∃ (removed : Nat), ∃ segs, ∃ (_prf : segs = segments.drop removed), origin ∉ segs ∧ FullWalk ctx origin dest segs := by
  have aux : ∀ (n : Nat) (origin' dest' : _) (segments' : List _),
      segments'.length ≤ n →
      FullWalk ctx origin' dest' segments' →
      ∃ (removed : Nat), ∃ segs, ∃ (_prf : segs = segments'.drop removed), origin' ∉ segs ∧ FullWalk ctx origin' dest' segs := by
    intro n
    induction n with
    | zero =>
      intro origin dest segments hlen h
      cases h with
      | direct dref =>
        exists 0, [], rfl
        simp
        exact .direct dref
      | tail _ _ =>
        simp at hlen
    | succ n ih =>
      intro origin dest segments hlen h
      cases h with
      | direct dref =>
        exists 0, [], rfl
        simp
        exact .direct dref
      | tail dref tail_walk =>
        rename_i b tail_segs
        if hin : origin ∈ b :: tail_segs then
          simp at hin
          rcases hin with heq | hin
          · -- origin = b, so tail_walk is a walk from origin to dest
            subst_eqs
            have hlt : tail_segs.length ≤ n := by simp at hlen; omega
            have ⟨removed, segs, hsegeq, nin, fw⟩ := ih origin dest tail_segs hlt tail_walk
            refine ⟨removed + 1, segs, ?_, ?_, ?_⟩
            · simp [hsegeq]
            · exact nin
            · exact fw
          · -- origin ∈ tail_segs, extract the suffix walk
            have ⟨i, hilen, heq⟩ := tail_segs.getElem_of_mem hin
            have sub_walk := tail_walk.from_seg_to_end i hilen
            rw [heq] at sub_walk
            -- sub_walk : FullWalk ctx origin dest (tail_segs.drop (i+1))
            have hlt : (tail_segs.drop (i + 1)).length ≤ n := by simp at hlen ⊢; omega
            have ⟨removed, segs, hsegeq, nin, fw⟩ := ih origin dest _ hlt sub_walk
            simp only [List.drop_drop] at hsegeq
            have hsegeq' : segs = (b :: tail_segs).drop (i + 1 + 1 + removed) := by
              grind
            refine ⟨i + 1 + 1 + removed, segs, hsegeq', ?_, ?_⟩
            · exact nin
            · exact fw
        else
          exists 0, b :: tail_segs, rfl
          simp [hin]
          exact .tail dref tail_walk
  exact aux segments.length origin dest segments (Nat.le_refl _) h








/-- If the dest is in the segments list, then it's possible to create a walk from origin to dest that's shorter in length and whose segments don't contain dest! -/
theorem FullWalk.get_dest_nin_segs
  (h : FullWalk ctx origin dest segments)
  : ∃ removed ≤ segments.length, ∃ segs, ∃ (_prf : segs = segments.dropEnd removed), dest ∉ segs ∧ FullWalk ctx origin dest segs := by
  cases h using FullWalk.snoc_induction with
  | direct dref =>
    simp
    refine .direct dref
  | snoc body dref =>
    expose_names
    clear h
    if hin : dest ∈ body_1 ++ [bum] then
      simp at hin
      rcases hin with hin | heq
      · have ⟨i,hilen,heq⟩ := body_1.getElem_of_mem hin
        have := body.from_start_to_seg' i hilen
        rw [heq] at this
        have ⟨removed, rmvlt, segs, hsegeq, nin, fw⟩ := this.get_dest_nin_segs

        simp only [List.dropEnd_dropEnd] at hsegeq
        -- hsegeq : segs = body_1.dropEnd ((body_1.length - i) + removed)
        -- We need: segs = (body_1 ++ [bum]).dropEnd total_removed
        -- Key: (body_1 ++ [bum]).dropEnd (k + 1) = body_1.dropEnd k
        -- So total_removed = (body_1.length - i) + removed + 1

        -- rmvlt : removed ≤ (body_1.dropEnd (body_1.length - i)).length
        -- The length of body_1.dropEnd (body_1.length - i) is i
        simp at rmvlt
        have hlen_dropEnd : body_1.length - (body_1.length - i) = i := by omega
        rw [hlen_dropEnd] at rmvlt
        -- Now rmvlt : removed ≤ i

        exists (body_1.length - i) + removed + 1, ?_, segs, ?_
        -- Goal 1: (body_1.length - i) + removed + 1 ≤ (body_1 ++ [bum]).length
        · simp
          -- Need: body_1.length - i + removed + 1 ≤ body_1.length + 1
          -- i.e., body_1.length - i + removed ≤ body_1.length
          -- Since removed ≤ i, this holds
          omega
        -- Goal 2: segs = (body_1 ++ [bum]).dropEnd ((body_1.length - i) + removed + 1)
        · rw [hsegeq]
          -- Need: body_1.dropEnd ((body_1.length - i) + removed) = (body_1 ++ [bum]).dropEnd ((body_1.length - i) + removed + 1)
          simp [List.dropEnd]
          -- This should follow from (l ++ [x]).dropEnd (k+1) = l.dropEnd k
        -- Goal 3: dest ∉ segs ∧ FullWalk ctx origin dest segs
        · tauto
      · -- Case: dest = bum (the last segment equals dest)
        subst_eqs
        -- body : FullWalk ctx origin dest body_1
        have ⟨removed, rmvlt, segs, hsegeq, nin, fw⟩ := body.get_dest_nin_segs
        -- hsegeq : segs = body_1.dropEnd removed
        -- We need: segs = (body_1 ++ [dest]).dropEnd total_removed
        -- Using (l ++ [x]).dropEnd (k+1) = l.dropEnd k, we need total_removed = removed + 1
        exists removed + 1, ?_, segs, ?_
        -- Goal 1: removed + 1 ≤ (body_1 ++ [dest]).length = body_1.length + 1
        · simp; omega
        -- Goal 2: segs = (body_1 ++ [dest]).dropEnd (removed + 1)
        · rw [hsegeq]
          simp [List.dropEnd]
        -- Goal 3: dest ∉ segs ∧ FullWalk ctx origin dest segs
        · tauto


    else
      exists 0, by simp, body_1++[bum], ?_
      simp
      have : body_1.reverse.length = body_1.length := by grind
      simp [*]
      refine .snoc body dref

  termination_by segments.length



omit [Fintype V] [DecidableEq V] in
/-- Split at any middle section – valuable theorem!! -/
@[grind →]
theorem FullWalk.split_by_segs {origin : V}
  (h : FullWalk ctx origin dest segments)
  (hsegs : segments = segs₁ ++ [middle] ++ segs₂)
  : FullWalk ctx origin middle segs₁ ∧ FullWalk ctx middle dest segs₂ := by
  have hindexblt : segs₁.length < segments.length := by simp [hsegs]
  have hmid : segments[segs₁.length] = middle := by simp [hsegs]
  have htake : segments.take segs₁.length = segs₁ := by simp [hsegs]
  have hdrop : segments.drop (segs₁.length + 1) = segs₂ := by simp [hsegs]
  constructor
  · have := h.from_start_to_seg segs₁.length hindexblt
    simp [hmid, htake] at this
    exact this
  · have := h.from_seg_to_end segs₁.length hindexblt
    simp [hmid, hdrop] at this
    exact this




-- Helper: if ¬Nodup, there exist distinct indices with equal elements
lemma List.exists_dup_indices {l : List α} (hdup : ¬l.Nodup) :
    ∃ i j, i < j ∧ j < l.length ∧ l[i]? = l[j]? := by
  rw [List.nodup_iff_getElem?_ne_getElem?] at hdup
  push_neg at hdup
  exact hdup

theorem FullWalk.exists_non_dup
  (h : FullWalk ctx current dest segments)
  : ∃ segs, ∃ (_ : (current :: segs).Nodup ∧ (dest :: segs).Nodup), FullWalk ctx current dest segs := by
  -- Check if we already have the desired properties
  if hnodup : (current :: segments).Nodup ∧ (dest :: segments).Nodup then
    exact ⟨segments, hnodup, h⟩
  else
    -- At least one of the Nodup conditions fails
    -- Case analysis on which condition fails
    if hcurr : current ∈ segments then
      -- current is in segments, use get_orig_nin_segs to get a shorter walk
      have ⟨removed, segs, hsegeq, nin, fw⟩ := h.get_orig_nin_segs
      -- removed > 0 because current ∈ segments but current ∉ segs
      have hremoved_pos : removed > 0 := by
        by_contra h
        simp at h
        rw [h] at hsegeq
        simp at hsegeq
        rw [hsegeq] at nin
        exact nin hcurr
      have hlen : segs.length < segments.length := by
        rw [hsegeq]
        simp only [List.length_drop]
        have : segments.length > 0 := List.length_pos_of_mem hcurr
        omega
      -- Recurse on the shorter walk
      exact fw.exists_non_dup
    else if hdest : dest ∈ segments then
      -- dest is in segments, use get_dest_nin_segs to get a shorter walk
      have ⟨removed, hrmv, segs, hsegeq, nin, fw⟩ := h.get_dest_nin_segs
      -- removed > 0 because dest ∈ segments but dest ∉ segs
      have hremoved_pos : removed > 0 := by
        by_contra h
        simp at h
        rw [h] at hsegeq
        simp at hsegeq
        rw [hsegeq] at nin
        exact nin hdest
      have hlen : segs.length < segments.length := by
        rw [hsegeq]
        simp only [List.dropEnd, List.length_reverse, List.length_drop]
        have : segments.length > 0 := List.length_pos_of_mem hdest
        omega
      -- Recurse on the shorter walk
      exact fw.exists_non_dup
    else
      -- current ∉ segments and dest ∉ segments, but one of the Nodup conditions fails
      -- This means segments itself is not Nodup (has internal duplicates)
      have hdup : ¬segments.Nodup := by
        -- hnodup says: ¬((current :: segments).Nodup ∧ (dest :: segments).Nodup)
        -- Since hcurr says current ∉ segments and hdest says dest ∉ segments,
        -- the only way hnodup can fail is if ¬segments.Nodup
        by_contra hnd
        apply hnodup
        constructor
        · rw [List.nodup_cons]; exact ⟨hcurr, hnd⟩
        · rw [List.nodup_cons]; exact ⟨hdest, hnd⟩
      -- Find the duplicate: there exist i < j with segments[i]? = segments[j]?
      have ⟨i, j, hij, hjlen, heq⟩ := List.exists_dup_indices hdup
      have hilen : i < segments.length := Nat.lt_trans hij hjlen
      -- Create a shorter walk by skipping from i to j
      -- Walk from current to segments[i]
      have walk1 := h.from_start_to_seg i hilen
      -- Walk from segments[j] to dest
      have walk2 := h.from_seg_to_end j hjlen
      -- Since segments[i]? = segments[j]?, we have segments[i] = segments[j]
      have heq' : segments[i] = segments[j] := by
        simp [hilen, hjlen] at heq
        exact heq
      rw [← heq'] at walk2
      -- Combine the walks
      have combined : FullWalk ctx current dest (segments.take i ++ [segments[i]] ++ segments.drop (j + 1)) :=
        walk1.append walk2
      -- This combined walk is shorter since i < j
      have hlen : (segments.take i ++ [segments[i]] ++ segments.drop (j + 1)).length < segments.length := by
        simp
        omega
      -- Recurse on the shorter walk
      exact combined.exists_non_dup

  termination_by segments.length












/-- Bool-valued implementation of decidable function for walks -/
def Walk.decideBool [Fintype V]
  (graph : Graph (V:=V))

  (origin : V) -- not in seens
  (current : V) -- is not `origin`
  (dest : V) -- not in seens

  (seenRefs : Finset V) :
  Bool :=
  if _heq : current = dest then
    true
  else
    if _hin : current ∈ seenRefs then
      false
    else
      let result := (graph current).image (λ child ↦ decideBool graph origin child dest (insert current seenRefs))
      result.filter (· = true) ≠ ∅

  termination_by (Fintype.card V - seenRefs.card)
  decreasing_by
    simp [*]
    apply Nat.sub_lt_sub_left
    · apply Finset.card_lt_univ_of_notMem _hin
    · simp









omit [Fintype V] in
/-- That if it returns `true` we can produce a `Walk` from `current` to `dest` -/
@[grind →]
theorem Walk.decideBool_sound [Fintype V] {current : V}
  (horigtocurr : Walk graph origin current)
  (h : Walk.decideBool graph origin current dest seenRefs = true)
  : Walk graph origin dest := by
  fun_induction Walk.decideBool graph origin current dest seenRefs with
  | case1 seenRefs => exact horigtocurr
  | case2 => contradiction
  | case3 current seenRefs hneq hcurrninseen result ih =>
    simp [result] at h ih
    obtain ⟨child,dref, prf⟩ := h
    exact ih child (horigtocurr.append (.direct dref)) prf







theorem FullWalk.decideBool_complete {current : V}
  (horigtocurr : Walk graph origin current)
  (hseenswalk : ∀ seen ∈ seenRefs, Walk graph seen current)
  (shortestWalk : FullWalk graph origin dest segments)
  (segsplit : segsprecurr ++ [current] ++ segspostcurr = segments)
  (noOverlap : ∀ seen ∈ seenRefs, seen ∉ current :: segspostcurr)
  (segsunique : (origin :: segments).Nodup ∧ (dest :: segments).Nodup)
  : Walk.decideBool graph origin current dest seenRefs = true := by
  fun_induction Walk.decideBool graph origin current dest seenRefs
    generalizing segments segsprecurr segspostcurr
  with
  | case1 => rfl
  | case2 current seenRefs hneqdest currninseen =>
    have := noOverlap current currninseen
    simp at this

  | @case3 current seenRefs currneqdest currninseen result ih =>
    simp [result, *] at segsunique ⊢
    obtain ⟨⟨orignseg,segnodup⟩,⟨destninseg,a⟩⟩ := segsunique
    clear a

    have ⟨origtocurr,currtodest⟩ := shortestWalk.split_by_segs (Eq.symm segsplit)

    cases hl : segspostcurr with
    | nil =>
      rw [hl] at currtodest
      cases currtodest with
      | direct dref =>
        exists dest,dref
        unfold Walk.decideBool
        simp
    | cons head tail =>
      rw [hl] at currtodest
      exists head, ref_segment_cons currtodest rfl
      have drefcurrtohead := currtodest.ref_segment_cons rfl
      have walkcurrtohead := Walk.direct drefcurrtohead

      apply ih head _ _ shortestWalk (segsprecurr:=segsprecurr++[current]) (segspostcurr:= tail) (by grind) _ (by grind)
      · refine horigtocurr.append walkcurrtohead
      · simp
        constructor
        · exact walkcurrtohead
        · intro seen seenin
          exact (hseenswalk seen seenin).append walkcurrtohead
      · intro seen seenin
        simp at seenin
        rcases seenin with seencurr | seenin
        · rw [seencurr]
          rw [← segsplit, hl] at segnodup
          simp at segnodup
          grind
        · grind














/-- The completeness theorem for the case where `seenRefs` is empty -/
theorem FullWalk.decideBool_fresh_complete_full_walk {current : V}
  (horigtocurr : Walk graph origin current)
  (shortestWalk : FullWalk graph origin dest segments)
  (segsplit : segsprecurr ++ [current] ++ segspostcurr = segments)
  (segsunique : (origin :: segments).Nodup ∧ (dest :: segments).Nodup)
  : Walk.decideBool graph origin current dest ∅ = true := by
  apply shortestWalk.decideBool_complete horigtocurr _ segsplit _ segsunique
  · simp
  · simp




omit [Fintype V] [DecidableEq V] in
/-- Just to point out that `Walk` is not a reflexive relation -/
theorem Walk.not_trivially_true {i : V} : ∃ graph, ¬Walk graph i i := by
  let graph : ∀ v : V, Finset V := λ _ ↦ ∅
  exists graph
  exact leaf_no_walk rfl





/-- !!!!!!!!! -/
instance Walk.decide [Fintype V]
  (graph : Graph)
  (origin : V)
  (dest : V)
  : Decidable (Walk graph origin dest)
  := by
  if hempty : graph origin = ∅ then
    refine .isFalse ?_
    exact leaf_no_walk hempty
  else
    by_cases hdirect : dest ∈ graph origin
    · refine .isTrue ?_
      refine .direct hdirect
    · let result := (graph origin).image (λ child ↦ decideBool graph origin child dest ∅)

      if hresult : true ∈ result then
        refine .isTrue ?_
        simp [result] at hresult
        obtain ⟨child, childin,prf⟩ := hresult
        exact Walk.decideBool_sound (.direct childin) prf

      else
        simp [result] at hresult
        refine .isFalse ?_
        intro contra
        have ⟨ segs, fw ⟩ := contra.toFullWalk
        have ⟨ segs, nodup, fw ⟩ := fw.exists_non_dup

        cases segs with
        | nil =>
          cases fw with
          | direct h =>
            absurd h
            exact hdirect
        | cons head tail =>
          have dref := fw.ref_segment_cons rfl
          have dec := hresult head dref
          absurd dec
          simp
          refine fw.decideBool_complete (seenRefs:=∅) (segsprecurr:=[]) (segspostcurr:=tail) (.direct dref) (by simp) (current:=head) (by simp) (by simp) ?_
          simpa using nodup







@[simp,reducible,grind]
def HasCycle ctx (i : V) := Walk ctx i i



instance HasCycle.decide (ctx : Graph) (i : V) :
  Decidable (HasCycle ctx i) :=
    Walk.decide ctx i i









-- def List.minBy [LinearOrder α] (l : List α) : Option α :=
--     match l with
--     | [] => none
--     | head :: tail => minBy' head tail
--   where
--   minBy' (minSoFar : α) : List α → α
--   | [] => minSoFar
--   | head :: tail => minBy' (min head minSoFar) tail




-- def List.minBy (comp : α → α → Ordering) (l : List α) : Option α :=
--     match l with
--     | [] => none
--     | head :: tail => minBy' head tail
--   where
--   minBy' (minSoFar : α) : List α → α
--   | [] => minSoFar
--   | head :: tail =>
--     let new :=
--       match comp minSoFar head with
--       | .lt => minSoFar
--       | .eq => minSoFar
--       | .gt => head

--     minBy' new tail



-- theorem List.minBy_min {l : List α} : l.minBy comp = some m → ∀ item ∈ l, comp m item ≠ Ordering.gt := by
--   intro prem
--   simp [minBy] at prem
--   -- induction l using minBy.minBy'.induct (comp:=comp) (α := α) with
--   cases l with
--   | nil => simp
--   | cons head tail =>
--     induction head, tail using minBy.minBy'.induct (comp:=comp) with
--     | case1 minSoFar =>
--       simp at prem ⊢
--       simp [minBy.minBy'] at prem
--       subst prem

--     -- simp
--     -- exact minBy.minBy'.induct (motive := fun head' tail' ↦ ∀ item ∈ head' :: tail', comp m item ≠ Ordering.gt) (comp := comp)
--     --   (case1 := by
--     --     simp at prem ⊢
--     --     intro minSoFar
--     --     unfold minBy.minBy' at prem
--     --     simp at prem

--     --     )
--     -- constructor
--     -- ·
--     --   simp at prem



--     -- sorry





def List.minBy (score : α → Nat) (l : List α) : Option α :=
    match l with
    | [] => none
    | head :: tail => minBy' head tail
  where
  minBy' (minSoFar : α) : List α → α
  | [] => minSoFar
  | head :: tail =>
    let new :=
      if score head < score minSoFar then head
      else minSoFar

    minBy' new tail



theorem List.minBy_min {l : List α} : l.minBy score = some m → ∀ item ∈ l, score m ≤ score item := by
  intro prem
  simp [minBy] at prem
  cases l with
  | nil => simp
  | cons head tail =>
    induction head, tail using minBy.minBy'.induct (score:=score) with
    | case1 minSoFar =>
      simp at prem ⊢
      simp [minBy.minBy'] at prem
      subst prem
      simp
    | case2 minSoFar head tail new ih =>
      simp at ih prem ⊢
      simp [minBy.minBy'] at prem
      have := ih prem
      grind


private theorem List.minBy_minBy'_mem {score : α → Nat} (a : α) (l : List α) :
    minBy.minBy' score a l ∈ a :: l := by
  induction l generalizing a with
  | nil => simp [minBy.minBy']
  | cons h t ih =>
    unfold minBy.minBy'
    have := ih (if score h < score a then h else a)
    simp only [List.mem_cons] at this ⊢
    rcases this with heq | hmem
    · rw [heq]; split <;> simp
    · right; right; exact hmem

theorem List.minBy_eq_none {l : List α} {score : α → Nat} (h : l.minBy score = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons a as => simp [minBy] at h

theorem List.minBy_mem {l : List α} {score : α → Nat} (h : l.minBy score = some m) : m ∈ l := by
  cases l with
  | nil => simp [minBy] at h
  | cons a as =>
    simp [minBy] at h
    subst h
    exact minBy_minBy'_mem a as




inductive FullWalkResult
  | noPath
  | hasPath (segments : List V)



def FullWalk.decideList [Fintype V] [LinearOrder V]
  (graph : Graph (V:=V))

  (origin : V) -- not in seens
  (current : V) -- is not `origin`
  (dest : V) -- not in seens

  (seenRefs : List V)
  (seenRefsNodup : seenRefs.Nodup) :
  FullWalkResult (V:=V) :=
  if _heq : current = dest then
    .hasPath seenRefs
  else
    if _hin : current ∈ seenRefs then
      .noPath
    else
      have nodup : (seenRefs ++ [current]).Nodup := by grind

      let filtered :=
        -- @TODO: get the shortest path by segment length. That way we should be able to create theorems that the returned path is a) the shortest, and b) contains no duplicate segments
        -- (graph current).sort ( · ≤ ·) |>.findSome? (λ child ↦
        --   match decideList graph origin child dest (seenRefs ++ [current]) nodup with
        --   | .noPath => none
        --   | .hasPath paths => some (child, paths))
        (graph current).sort ( · ≤ ·)
          |>.filterMap (λ child ↦
            match decideList graph origin child dest (seenRefs ++ [current]) nodup with
            | .noPath => none
            | .hasPath paths => some (child, paths))

      let shortest :=
        List.minBy (λ ⟨_,l⟩ ↦ l.length) filtered

      match shortest with
      | none => .noPath
      | some (_child, paths) => .hasPath paths


  termination_by (Fintype.card V - seenRefs.length)
  decreasing_by
    simp [*]
    exact List.nodup_lte_fintype_mem seenRefsNodup _hin






lemma FullWalk.decideList_if_not_path_no_path [LinearOrder V] : (∀ (paths : List V), ¬FullWalk.decideList graph origin head dest segments nodup = FullWalkResult.hasPath paths) → FullWalk.decideList graph origin head dest segments nodup = .noPath := by
  intro h
  cases result : FullWalk.decideList graph origin head dest segments nodup with
  | noPath => rfl
  | hasPath paths => exact absurd result (h paths)






theorem FullWalk.decideList_completeness [LinearOrder V] {current : V}
  (segsplit : segments = segsprecurr ++ [current] ++ segspostcurr)
  (segsunique : (origin :: segments).Nodup ∧ (dest :: segments).Nodup)
  (hseenswalk : FullWalk graph origin current seenRefs)
  (fw : FullWalk graph origin dest segments)
  (noOverlap : ∀ seen ∈ seenRefs, seen ∉ current :: segspostcurr)
  : ∃ segs, FullWalk.decideList graph origin current dest seenRefs seenNodup = .hasPath segs := by
  have hcurrinseg : current ∈ segments := by grind
  fun_induction FullWalk.decideList graph origin current dest seenRefs seenNodup generalizing segsprecurr segspostcurr segments with
  | case1 seenRefs seensNodup => exists seenRefs
  | case2 =>
    expose_names
    simp
    exact noOverlap current h_1 (List.Mem.head segspostcurr)

  | @case3 current seenRefs seenNodup hncurreqdest currninseens nodup filtered shortest hshortest ih =>
    have hfilt : filtered = [] := List.minBy_eq_none hshortest
    exfalso
    cases segspostcurr with
    | nil =>
      simp [segsplit] at hcurrinseg fw
      have destincurr : dest ∈ graph current := by grind
      have hdec : decideList graph origin dest dest (seenRefs ++ [current]) nodup = .hasPath (seenRefs ++ [current]) := by
        unfold decideList; simp
      have : (dest, seenRefs ++ [current]) ∈ filtered := by
        apply List.mem_filterMap.mpr
        exact ⟨dest, (Finset.mem_sort _).mpr destincurr, by simp [hdec]⟩
      rw [hfilt] at this
      simp at this
    | cons head tail =>
      have headincurr : head ∈ graph current := by
        rw [segsplit] at fw
        have := fw.from_seg_to_end segsprecurr.length (by grind)
        simp at this
        grind
      have ⟨segs, prf⟩ := ih (segsprecurr:=segsprecurr++[current]) (segspostcurr:=tail) head
        (by simp at segsplit ⊢; exact segsplit) segsunique
        (by simpa using hseenswalk.append (.direct headincurr)) fw (by grind) (by grind : head ∈ segments)
      have : (head, segs) ∈ filtered := by
        apply List.mem_filterMap.mpr
        exact ⟨head, (Finset.mem_sort _).mpr headincurr, by simp [prf]⟩
      rw [hfilt] at this
      simp at this
  | case4 => grind





@[grind →]
theorem FullWalk.decideList_completeness_fresh [LinearOrder V] {current : V}
  (segsplit : segments = [current] ++ segspostcurr)
  (segsunique : (origin :: segments).Nodup ∧ (dest :: segments).Nodup)
  (fw : FullWalk graph origin dest segments)
  : ∃ segs, FullWalk.decideList graph origin current dest ∅ (by simp) = .hasPath segs := by
  have hcurrinseg : current ∈ segments := by grind
  refine FullWalk.decideList_completeness (seenRefs:=∅) ?_ segsunique ?_ fw (by simp) (seenNodup:=by simp) (segspostcurr:=segspostcurr) (segsprecurr:=[])
  · grind
  · simp at segsplit
    have dref := fw.ref_segment_cons segsplit
    refine .direct dref










omit [Fintype V] [DecidableEq V] in
lemma findSome?_child_mem {l : List V} {f : V → FullWalkResult}
    {child : V} {paths : List V}
    (h : l.findSome? (fun c => match f c with
      | .noPath => none
      | .hasPath ps => some (c, ps)) = some (child, paths)) :
    child ∈ l := by
  have ⟨a, ha_mem, ha_eq⟩ := List.exists_of_findSome?_eq_some h
  match hfa : f a with
  | .noPath => simp [hfa] at ha_eq
  | .hasPath ps =>
    simp [hfa] at ha_eq
    obtain ⟨rfl, _⟩ := ha_eq
    exact ha_mem


@[grind →]
theorem FullWalk.decideList_sound [LinearOrder V] {current : V}
  (hseenswalk : FullWalk graph origin current seenRefs)
  (h : FullWalk.decideList graph origin current dest seenRefs seenNodup = .hasPath segments) : FullWalk graph origin dest segments
  := by
  fun_induction FullWalk.decideList graph origin current dest seenRefs seenNodup generalizing segments with
  | case1 =>
    simp at h
    subst_eqs
    exact hseenswalk

  | case2 => grind
  | case3 => grind
  | @case4 current seenRefs seenNodup hncurreqdest currninseens nodup filtered shortest child_v segs hshortest ih =>
    simp at h
    subst_eqs
    have hmem := List.minBy_mem hshortest
    obtain ⟨child', hchild_sort, hdl⟩ := List.mem_filterMap.mp hmem
    cases hresult : decideList graph origin child' dest (seenRefs ++ [current]) nodup with
    | noPath => simp [hresult] at hdl
    | hasPath p =>
      simp [hresult] at hdl
      obtain ⟨h1, h2⟩ := hdl
      subst h1; subst h2
      exact ih _ (by simpa using hseenswalk.append (.direct ((Finset.mem_sort _).mp hchild_sort))) hresult







/-- The shortest walk from `origin` to `dest`: returns the segments (excluding both
endpoints) of a shortest walk, or `none` if no walk exists.

If `dest` is directly reachable from `origin`, returns `some []`. Otherwise tries every
child of `origin` and picks the one yielding the shortest decideList path. -/
def FullWalk.shortest [LinearOrder V] (graph : Graph (V:=V)) (origin dest : V) : Option (List V) :=
  if dest ∈ graph origin then some [] else
    (graph origin).sort (· ≤ ·)
    |>.filterMap (fun child =>
        match decideList graph origin child dest [] (by simp) with
        | .noPath => none
        | .hasPath ps => some ps)
    |> List.minBy (·.length)


/-- Soundness: if `shortest` returns `some paths`, those segments form a valid walk. -/
theorem FullWalk.shortest_walk [LinearOrder V] {graph : Graph} {origin dest : V}
    {paths : List V} (h : FullWalk.shortest graph origin dest = some paths)
    : FullWalk graph origin dest paths := by
  unfold shortest at h
  split at h
  · rename_i hdirect
    simp at h
    subst h
    exact .direct hdirect
  · have hmem := List.minBy_mem h
    obtain ⟨child, hchild_sort, hmatch⟩ := List.mem_filterMap.mp hmem
    have dref : child ∈ graph origin := (Finset.mem_sort _).mp hchild_sort
    cases hres : decideList graph origin child dest [] (by simp) with
    | noPath => simp [hres] at hmatch
    | hasPath p =>
      simp [hres] at hmatch
      subst hmatch
      exact decideList_sound (.direct dref) hres


/-- Completeness: if any simple-path walk from `origin` to `dest` exists, `shortest`
returns some path. -/
theorem FullWalk.shortest_isSome_of_walk [LinearOrder V] {graph : Graph} {origin dest : V}
    {altSegments : List V}
    (fwAlt : FullWalk graph origin dest altSegments)
    (origin_nodup : (origin :: altSegments).Nodup)
    (dest_nodup : (dest :: altSegments).Nodup)
    : (FullWalk.shortest graph origin dest).isSome := by
  unfold shortest
  by_cases hdirect : dest ∈ graph origin
  · simp [hdirect]
  · simp only [hdirect, ↓reduceIte]
    cases altSegments with
    | nil =>
      cases fwAlt with
      | direct hd => exact absurd hd hdirect
    | cons head tail =>
      have dref : head ∈ graph origin := fwAlt.ref_segment_cons rfl
      have head_sort : head ∈ (graph origin).sort (· ≤ ·) := (Finset.mem_sort _).mpr dref
      have ⟨ps, hdec⟩ := fwAlt.decideList_completeness_fresh (current := head)
        (segspostcurr := tail) (by simp) ⟨origin_nodup, dest_nodup⟩
      have hdec' : decideList graph origin head dest [] (by simp) = .hasPath ps := hdec
      have hmem : ps ∈ ((graph origin).sort (· ≤ ·) |>.filterMap (fun child =>
          match decideList graph origin child dest [] (by simp) with
          | .noPath => none
          | .hasPath ps => some ps)) := by
        apply List.mem_filterMap.mpr
        refine ⟨head, head_sort, ?_⟩
        simp [hdec']
      cases hminby : ((graph origin).sort (· ≤ ·) |>.filterMap (fun child =>
          match decideList graph origin child dest [] (by simp) with
          | .noPath => none
          | .hasPath ps => some ps)) |> List.minBy (·.length) with
      | none =>
        have hempty := List.minBy_eq_none hminby
        rw [hempty] at hmem
        simp at hmem
      | some _ => simp


/-- `FullWalk.producible` produces a walk via `FullWalk.shortest`, so its returned path
is guaranteed to be shortest (see `producible_shortest`). -/
instance FullWalk.producible [LinearOrder V] (graph : Graph) (origin dest : V) :
    Producible (FullWalk graph origin dest) := by
  match h : FullWalk.shortest graph origin dest with
  | some paths => exact .possible paths (FullWalk.shortest_walk h)
  | none =>
    refine .impossible ?_
    intro segs fw
    obtain ⟨segs', ⟨origin_nodup, dest_nodup⟩, fw'⟩ := fw.exists_non_dup
    have hsome := FullWalk.shortest_isSome_of_walk fw' origin_nodup dest_nodup
    rw [h] at hsome
    simp at hsome



/-- decideList returns the shortest continuation: among all non-repeating walks from
`current` to `dest` that avoid both `seenRefs` and `origin`, the result has minimum
total segment count (bounded by `seenRefs.length + altPostcurr.length + 1`).

The `originNotInAlt` premise is needed because the proof reduces to calling
`decideList_completeness` on the combined walk `origin → seenRefs → current → altPostcurr → dest`,
whose nodup condition requires `origin` not to reappear in `altPostcurr`. The premise
also yields `origin ≠ head` for the recursive call. -/
theorem FullWalk.decideList_shortest [LinearOrder V] {current : V}
  (hseenswalk : FullWalk graph origin current seenRefs)
  (h : FullWalk.decideList graph origin current dest seenRefs seenNodup = .hasPath result)
  (fwAlt : FullWalk graph current dest altPostcurr)
  (altNoOverlap : ∀ seen ∈ seenRefs, seen ∉ current :: altPostcurr)
  (altNodupCurr : (current :: altPostcurr).Nodup)
  (altNodupDest : (dest :: altPostcurr).Nodup)
  (originNeqCurrent : origin ≠ current)
  (originNotSeen : origin ∉ seenRefs)
  (destNotSeen : dest ∉ seenRefs)
  (originNotInAlt : origin ∉ altPostcurr)
  : result.length ≤ seenRefs.length + altPostcurr.length + 1 := by
  fun_induction FullWalk.decideList graph origin current dest seenRefs seenNodup
    generalizing altPostcurr result
  with
  | case1 => simp at h; subst_eqs; omega
  | case2 => simp at h
  | case3 => simp at h
  | @case4 current seenRefs seenNodup hncurreqdest currninseens nodup filtered shortest
      child_v segs hshortest ih =>
    simp at h; subst_eqs
    cases hpc : altPostcurr with
    | nil =>
      rw [hpc] at fwAlt
      cases fwAlt with
      | direct dref =>
        have dest_sort : dest ∈ (graph current).sort (· ≤ ·) := (Finset.mem_sort _).mpr dref
        have hdec : decideList graph origin dest dest (seenRefs ++ [current]) nodup
            = .hasPath (seenRefs ++ [current]) := by unfold decideList; simp
        have hmem_filt : (dest, seenRefs ++ [current]) ∈ filtered :=
          List.mem_filterMap.mpr ⟨dest, dest_sort, by simp [hdec]⟩
        have := List.minBy_min hshortest _ hmem_filt
        simp at this
        omega
    | cons head tail =>
      have dref : DirectRef graph current head := fwAlt.ref_segment_cons hpc
      have head_sort : head ∈ (graph current).sort (· ≤ ·) := (Finset.mem_sort _).mpr dref
      have fwTail : FullWalk graph head dest tail := fwAlt.cons_head_segment hpc
      rw [hpc] at altNodupCurr altNodupDest altNoOverlap originNotInAlt
      have hcurr_nin : current ∉ head :: tail := (List.nodup_cons.mp altNodupCurr).1
      have hht_nodup : (head :: tail).Nodup := (List.nodup_cons.mp altNodupCurr).2
      have hdest_nin : dest ∉ head :: tail := (List.nodup_cons.mp altNodupDest).1
      have hhead_nin_tail : head ∉ tail := (List.nodup_cons.mp hht_nodup).1
      have htail_nodup : tail.Nodup := (List.nodup_cons.mp hht_nodup).2
      have hcurr_ne_head : current ≠ head := by
        rintro rfl; exact hcurr_nin (by simp)
      have hcurr_nin_tail : current ∉ tail := fun hc =>
        hcurr_nin (List.mem_cons_of_mem _ hc)
      have hdest_ne_head : dest ≠ head := by
        rintro rfl; exact hdest_nin (by simp)
      have hdest_nin_tail : dest ∉ tail := fun hd =>
        hdest_nin (List.mem_cons_of_mem _ hd)
      have horigin_ne_head : origin ≠ head := by
        rintro rfl; exact originNotInAlt (by simp)
      have horigin_nin_tail : origin ∉ tail := fun ho =>
        originNotInAlt (List.mem_cons_of_mem _ ho)
      have hhead_nin_seens : head ∉ seenRefs := fun hh =>
        altNoOverlap head hh (List.mem_cons_of_mem _ (by simp))
      have htail_disj_seens : ∀ x ∈ tail, x ∉ seenRefs := fun x hxt hxs =>
        altNoOverlap x hxs (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hxt))
      have tailNoOverlap : ∀ seen ∈ seenRefs ++ [current], seen ∉ head :: tail := by
        intro seen hseen hmem
        rw [List.mem_append, List.mem_singleton] at hseen
        rcases hseen with hseen | rfl
        · exact altNoOverlap seen hseen (List.mem_cons_of_mem _ hmem)
        · exact hcurr_nin hmem
      have tailNodupHead : (head :: tail).Nodup := hht_nodup
      have tailNodupDest : (dest :: tail).Nodup :=
        List.nodup_cons.mpr ⟨hdest_nin_tail, htail_nodup⟩
      have fwToHead : FullWalk graph origin head (seenRefs ++ [current]) := by
        simpa using hseenswalk.append (.direct dref)
      have fwFull : FullWalk graph origin dest (seenRefs ++ [current] ++ [head] ++ tail) :=
        fwToHead.append fwTail
      have inner_nodup : (seenRefs ++ [current] ++ [head] ++ tail).Nodup := by
        rw [show seenRefs ++ [current] ++ [head] ++ tail
            = (seenRefs ++ [current]) ++ (head :: tail) from by simp,
            List.nodup_append]
        refine ⟨nodup, hht_nodup, ?_⟩
        rintro a ha b hb rfl
        exact tailNoOverlap a ha hb
      have segsunique : (origin :: seenRefs ++ [current] ++ [head] ++ tail).Nodup
          ∧ (dest :: seenRefs ++ [current] ++ [head] ++ tail).Nodup := by
        refine ⟨List.nodup_cons.mpr ⟨?_, inner_nodup⟩, List.nodup_cons.mpr ⟨?_, inner_nodup⟩⟩
        · intro hin
          simp at hin
          rcases hin with hin | hin | hin | hin
          · exact originNotSeen hin
          · exact originNeqCurrent hin
          · exact horigin_ne_head hin
          · exact horigin_nin_tail hin
        · intro hin
          simp at hin
          rcases hin with hin | hin | hin | hin
          · exact destNotSeen hin
          · exact hncurreqdest hin.symm
          · exact hdest_ne_head hin
          · exact hdest_nin_tail hin
      have ⟨childResult, hchildDec⟩ :
          ∃ cr, decideList graph origin head dest (seenRefs ++ [current]) nodup = .hasPath cr :=
        decideList_completeness (seenRefs := seenRefs ++ [current])
          (segsprecurr := seenRefs ++ [current]) (segspostcurr := tail)
          (by simp) segsunique fwToHead fwFull tailNoOverlap
      have hmem_filt : (head, childResult) ∈ filtered :=
        List.mem_filterMap.mpr ⟨head, head_sort, by simp [hchildDec]⟩
      have hminBy := List.minBy_min hshortest _ hmem_filt
      simp at hminBy
      have hih := ih head fwToHead hchildDec fwTail
        tailNoOverlap tailNodupHead tailNodupDest horigin_ne_head
        (by simp; exact ⟨originNotSeen, originNeqCurrent⟩)
        (by simp; exact ⟨destNotSeen, Ne.symm hncurreqdest⟩)
        horigin_nin_tail
      simp at hih ⊢
      omega


/-- Clean outside-view version of `decideList_shortest`: when called with empty
`seenRefs`, `decideList`'s result is no longer than any simple-path walk from
`origin` to `dest` whose first intermediate node is `current`.

A "simple path" here means a walk whose intermediate segments don't repeat the
origin or the destination. The two `Nodup` hypotheses together state exactly that. -/
theorem FullWalk.decideList_shortest_fresh [LinearOrder V]
  {origin current dest : V} {altPostcurr result : List V}
  (h : FullWalk.decideList graph origin current dest [] (by simp) = .hasPath result)
  (fwAlt : FullWalk graph origin dest (current :: altPostcurr))
  (originNodup : (origin :: current :: altPostcurr).Nodup)
  (destNodup : (dest :: current :: altPostcurr).Nodup)
  : result.length ≤ (current :: altPostcurr).length := by
  have dref : DirectRef graph origin current := fwAlt.ref_segment_cons rfl
  have fwTail : FullWalk graph current dest altPostcurr := fwAlt.cons_head_segment rfl
  have hseenswalk : FullWalk graph origin current [] := .direct dref
  have origin_nin_full : origin ∉ current :: altPostcurr := (List.nodup_cons.mp originNodup).1
  have current_alt_nodup : (current :: altPostcurr).Nodup := (List.nodup_cons.mp originNodup).2
  have dest_nin_full : dest ∉ current :: altPostcurr := (List.nodup_cons.mp destNodup).1
  have alt_nodup : altPostcurr.Nodup := (List.nodup_cons.mp current_alt_nodup).2
  have originNeqCurrent : origin ≠ current := by
    rintro rfl; exact origin_nin_full (by simp)
  have originNotInAlt : origin ∉ altPostcurr := fun ho =>
    origin_nin_full (List.mem_cons_of_mem _ ho)
  have destAltNodup : (dest :: altPostcurr).Nodup :=
    List.nodup_cons.mpr ⟨fun hd => dest_nin_full (List.mem_cons_of_mem _ hd), alt_nodup⟩
  have bound := decideList_shortest hseenswalk h fwTail
    (by simp) current_alt_nodup destAltNodup originNeqCurrent
    (by simp) (by simp) originNotInAlt
  simp at bound ⊢
  omega




/-- Outside-view shortest theorem: the path returned by `shortest` is no longer than
any simple-path walk from `origin` to `dest`. -/
theorem FullWalk.shortest_le [LinearOrder V] {graph : Graph} {origin dest : V}
    {paths : List V} (h : FullWalk.shortest graph origin dest = some paths)
    {altSegments : List V}
    (fwAlt : FullWalk graph origin dest altSegments)
    (origin_nodup : (origin :: altSegments).Nodup)
    (dest_nodup : (dest :: altSegments).Nodup)
    : paths.length ≤ altSegments.length := by
  unfold shortest at h
  split at h
  · simp at h
    subst h
    simp
  · rename_i hdirect_neg
    cases altSegments with
    | nil =>
      cases fwAlt with
      | direct hd => exact absurd hd hdirect_neg
    | cons head tail =>
      have dref : head ∈ graph origin := fwAlt.ref_segment_cons rfl
      have head_sort : head ∈ (graph origin).sort (· ≤ ·) := (Finset.mem_sort _).mpr dref
      have ⟨ps, hdec⟩ := fwAlt.decideList_completeness_fresh (current := head)
        (segspostcurr := tail) (by simp) ⟨origin_nodup, dest_nodup⟩
      have hdec' : decideList graph origin head dest [] (by simp) = .hasPath ps := hdec
      have hmem : ps ∈ ((graph origin).sort (· ≤ ·) |>.filterMap (fun child =>
          match decideList graph origin child dest [] (by simp) with
          | .noPath => none
          | .hasPath ps => some ps)) := by
        apply List.mem_filterMap.mpr
        refine ⟨head, head_sort, ?_⟩
        simp [hdec']
      have hbound := List.minBy_min h _ hmem
      have hps_bound :=
        FullWalk.decideList_shortest_fresh hdec' fwAlt origin_nodup dest_nodup
      simp at hbound hps_bound ⊢
      omega


/-- The cleanest outside-view theorem: when `FullWalk.producible` yields a path,
that path is no longer than any simple-path alternative from `origin` to `dest`. -/
theorem FullWalk.producible_shortest [LinearOrder V] {graph : Graph} {origin dest : V}
    {paths : List V} {walk : FullWalk graph origin dest paths}
    (h : (FullWalk.producible graph origin dest : Producible _) = .possible paths walk)
    {altSegments : List V}
    (fwAlt : FullWalk graph origin dest altSegments)
    (origin_nodup : (origin :: altSegments).Nodup)
    (dest_nodup : (dest :: altSegments).Nodup)
    : paths.length ≤ altSegments.length := by
  have hsome : FullWalk.shortest graph origin dest = some paths := by
    unfold FullWalk.producible at h
    split at h
    · rename_i ps hs
      cases h
      exact hs
    · contradiction
  exact FullWalk.shortest_le hsome fwAlt origin_nodup dest_nodup


/-- For any walk, there exists a walk with the fewest segments possible -/
theorem FullWalk.exists_shortest
  (fw : FullWalk graph origin dest segments)
  : ∃ segments', FullWalk graph origin dest segments' ∧
    ∀ segments'', FullWalk graph origin dest segments'' → segments'.length ≤ segments''.length := by
  classical
  have hP : ∃ n, ∃ segs, segs.length = n ∧ FullWalk graph origin dest segs :=
    ⟨segments.length, segments, rfl, fw⟩
  obtain ⟨segs, hlen, fwSegs⟩ := Nat.find_spec hP
  exact ⟨segs, fwSegs, fun segs' fw' => by
    have : Nat.find hP ≤ segs'.length := Nat.find_min' hP ⟨segs', rfl, fw'⟩
    omega⟩


/-- A shortest walk has no repeated nodes: origin and dest don't appear in the
intermediate segments, and the segments themselves contain no duplicates. -/
theorem FullWalk.shortest_nodup
  (fw : FullWalk graph origin dest segments)
  (hshortest : ∀ segments', FullWalk graph origin dest segments' → segments.length ≤ segments'.length)
  : (origin :: segments).Nodup ∧ (dest :: segments).Nodup := by
  have hsegs_nodup : segments.Nodup := by
    by_contra hdup
    obtain ⟨i, j, hij, hjlen, heq⟩ := List.exists_dup_indices hdup
    have hilen : i < segments.length := Nat.lt_trans hij hjlen
    have heq' : segments[i] = segments[j] := by simp [hilen, hjlen] at heq; exact heq
    have walk1 := fw.from_start_to_seg i hilen
    have walk2 := fw.from_seg_to_end j hjlen
    rw [← heq'] at walk2
    have combined := walk1.append walk2
    have hle := hshortest _ combined
    simp at hle
    omega
  have horig : origin ∉ segments := by
    intro hmem
    obtain ⟨i, hilen, heq⟩ := segments.getElem_of_mem hmem
    have sub := fw.from_seg_to_end i hilen
    rw [heq] at sub
    have hle := hshortest _ sub
    simp at hle
    omega
  have hdest : dest ∉ segments := by
    intro hmem
    obtain ⟨i, hilen, heq⟩ := segments.getElem_of_mem hmem
    have sub := fw.from_start_to_seg i hilen
    rw [heq] at sub
    have hle := hshortest _ sub
    simp at hle
    omega
  exact ⟨List.nodup_cons.mpr ⟨horig, hsegs_nodup⟩, List.nodup_cons.mpr ⟨hdest, hsegs_nodup⟩⟩
