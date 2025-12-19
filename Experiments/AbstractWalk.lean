import Mathlib

section List

@[simp]
def List.dropEnd (l : List α) (n : Nat) := l.reverse.drop n |>.reverse



@[simp high]
theorem List.dropEnd_dropEnd {l : List α} : (l.dropEnd i).dropEnd j = l.dropEnd (i+j) := by simp

end List




inductive LeafOrRef
  | leaf : LeafOrRef
  | ref : Nat → LeafOrRef
  | refTwo : Nat → Nat → LeafOrRef
  deriving DecidableEq, BEq

@[simp,grind] instance instMembershipNatLeafOrRef : Membership Nat LeafOrRef where
  mem lor n :=
    match lor with
    | .leaf => False
    | .ref i => i = n
    | .refTwo i j => i = n ∨ j = n

@[simp,grind] instance instMembershipNatLeafOrRef.decide (i : Nat) (lor : LeafOrRef) : Decidable (i ∈ lor) := by
  match h : lor with
  | .leaf =>
    refine .isFalse ?_
    simp
  | .ref j =>
    if hh : j = i then
      refine .isTrue ?_
      simp
      trivial
    else
      refine .isFalse ?_
      simp
      trivial
  | .refTwo j k =>
    if hh : j = i ∨ k = i then
      refine .isTrue ?_
      simpa using hh
    else
      refine .isFalse ?_
      simpa using hh


@[simp,grind .] theorem LeafOrRef.not_in : ¬i ∈ LeafOrRef.leaf := by simp

@[simp,grind →] theorem LeafOrRef.in_is_ref {item : LeafOrRef} (h : i ∈ item) : item = .ref i ∨ ∃ j, item = .refTwo i j ∨ item = .refTwo j i := by
  cases item
  · simp at h
  · simp at h
    subst_eqs
    simp
  · cases h
    · subst_eqs
      simp
    · subst_eqs
      simp



@[simp,grind =>] theorem LeafOrRef.ref_is_in {item : LeafOrRef} (h : item = .ref i) : i ∈ item := by
  simp
  cases item
  · simp at h
  · simp at h
    subst_eqs
    rfl
  · simp at h


@[simp,grind =>] theorem LeafOrRef.refTwo_is_in_fst {item : LeafOrRef} (h : item = .refTwo a b) : a ∈ item := by
  simp
  cases item
  · simp at h
  · simp at h
  · simp
    grind


@[simp,grind =>] theorem LeafOrRef.refTwo_is_in_snd {item : LeafOrRef} (h : item = .refTwo a b) : b ∈ item := by
  simp
  cases item
  · simp at h
  · simp at h
  · simp
    grind


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


@[reducible]
def Ctx := List LeafOrRef







variable {V : Type} [Fintype V] [DecidableEq V]

namespace LocalDefs

/-- A graph is defined abstractly as a function that given a node ID returns the set of connected nodes it points to -/
abbrev Graph (V:=V) := V → Finset V

end LocalDefs
export LocalDefs (Graph)



section Walk






/-- Node `v` directly references node `u`. Because `u` is in the set of nodes that `v` connects to. -/
@[reducible, simp]
def DirectRef (graph : Graph) (v : V) (u : V) := u ∈ graph v



/-- `origin` leads to `dest`, either directly or indirectly -/
@[grind cases]
inductive Walk (graph : Graph) : (origin dest : V) → Prop
  | direct :
    DirectRef graph origin dest →
    Walk graph origin dest

  | indirect :
    (walk₁ : Walk graph a b) →
    (walk₂ : Walk graph b c) →
    Walk graph a c






/-- If a thing only has a single ref and that ref is back to itself, it cannot lead to anywhere else -/
@[grind =>]
theorem Walk.selfRef_nwalk_elsewhere {graph : Graph} (h : graph current = {current}) : ∀ dest ≠ current, ¬Walk graph current dest := by
  intro dest destneq walk
  induction walk with
  | direct hh => grind
  | indirect walka walkb aih bih => grind




@[grind =>] theorem Walk.leaf_no_walk {graph : Graph} (h : graph a = ∅) : ∀ {b}, ¬Walk graph a b := by
  intro b nwalk
  induction nwalk
  · grind
  · tauto








/-- Walk containing all traversed nodes -/
@[grind cases]
inductive FullWalk (graph : Graph) : (origin dest : V) → (segments : List V) → Prop where
  | direct :
    DirectRef graph origin dest →
    FullWalk graph origin dest []

  | indirect :
    (walk₁ : FullWalk graph a b segments₁) →
    (walk₂ : FullWalk graph b c segments₂) →
    combinedSegments = segments₁ ++ [b] ++ segments₂ →
    FullWalk graph a c combinedSegments



@[grind →]
theorem FullWalk.toWalk : FullWalk graph origin dest segments → Walk graph origin dest := by
  intro fw
  induction fw
  · expose_names
    refine .direct h
  · expose_names
    refine .indirect walk₁_ih walk₂_ih


@[grind →]
theorem Walk.toFullWalk : Walk graph origin dest → ∃ segments, FullWalk graph origin dest segments := by
  intro walk
  induction walk
  · expose_names
    exists []
    refine .direct h
  · expose_names
    obtain ⟨segments₁,fw₁⟩ := walk₁_ih
    obtain ⟨segments₂,fw₂⟩ := walk₂_ih
    exists segments₁ ++ [b] ++ segments₂
    refine .indirect fw₁ fw₂ rfl




@[grind .]
theorem FullWalk.not_Walk : (∀ segments, ¬FullWalk ctx origin dest segments) → ¬Walk ctx origin dest := by grind


@[grind =>]
theorem Walk.not_FullWalk : ¬Walk ctx origin dest → ∀ segments, ¬FullWalk ctx origin dest segments := by grind








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
  | indirect walka walkb combeq aih bih =>
    expose_names
    cases walka with
    | direct dref =>
      -- segments₁ = [], so combinedSegments = [b] ++ segments₂ = b :: segments₂
      right
      exists b, segments₂
    | indirect walka1 walka2 combeq1 =>
      -- walka is indirect, so segments₁ ≠ []
      -- Apply IH to walka to get the structure of segments₁
      have ih_result := aih
      cases ih_result with
      | inl h =>
        -- segments₁ = [] ∧ DirectRef ctx (ctx[a]) b
        -- But walka is indirect, so segments₁ = segments₁' ++ [x] ++ segments₂' for some x
        -- This contradicts segments₁ = []
        simp [combeq1] at h
      | inr exists_first =>
        -- ∃ b' tailSegs₁, segments₁ = b' :: tailSegs₁ ∧ DirectRef ctx (ctx[a]) b' ∧ FullWalk ctx b' b tailSegs₁
        obtain ⟨b', tailSegs₁, segs_eq, dref, walk_b'_to_b⟩ := exists_first
        right
        exists b', tailSegs₁ ++ [b] ++ segments₂
        constructor
        · rw [combeq, segs_eq]
          rfl
        · constructor
          · exact dref
          · exact .indirect walk_b'_to_b walkb rfl





omit [Fintype V] [DecidableEq V] in
/-- Induction principle for `FullWalk` that works by adding one segment at a time from the front.

To prove a property about an arbitrary `FullWalk ctx origin dest segments`,
it suffices to prove it for:
1. Direct walks (empty segments)
2. Show that if it holds for a walk from `head` to `dest` with segments `tail`,
   and there's a direct reference from `origin` to `head`,
   then it holds for the walk from `origin` to `dest` with segments `head :: tail`.
-/
-- @[elab_as_elim]
theorem FullWalk.cons_induction
    {motive : ∀ (graph : Graph) (origin dest : V) (segments : List V), FullWalk graph origin dest segments → Prop}
    (direct : ∀ {graph} {origin} {dest} (h : DirectRef graph origin dest),
              motive graph origin dest [] (.direct h))
    (cons : ∀ {graph} {origin} {head} {dest} {tail}
              (hdirect : DirectRef graph origin head)
              (htail : FullWalk graph head dest tail),
              motive graph head dest tail htail →
              motive graph origin dest (head :: tail)
                (.indirect (.direct hdirect) htail (by simp)))
    {graph origin dest segments}
    (h : FullWalk graph origin dest segments)
    : motive graph origin dest segments h := by
  induction segments generalizing origin with
  | nil =>
    cases h with
    | direct dref => exact @direct graph origin dest dref
    | indirect walka walkb combeq =>
      simp at combeq
  | cons head tail ih =>
    have hstruct := h.segments_structure
    rcases hstruct with ⟨hempty, _⟩ | ⟨head', tail', hsegeq, hdref, htailwalk⟩
    · simp at hempty
    · simp at hsegeq
      obtain ⟨rfl, rfl⟩ := hsegeq
      -- We need to show that h equals the reconstructed walk
      have htail_ih := ih htailwalk
      -- The tricky part: we need to show h = .indirect (.direct hdref) htailwalk (by simp)
      -- But we can't directly, so we use proof irrelevance for Prop
      have : h = .indirect (.direct hdref) htailwalk (by simp) := by
        apply proof_irrel
      rw [this]
      exact @cons graph origin head dest tail hdref htailwalk htail_ih



/-- Example 1: For any walk, the origin can reach the destination -/
example (h : FullWalk graph origin dest segments) : Walk graph origin dest := by
  induction h using FullWalk.cons_induction with
  | direct hdirect =>
    exact .direct hdirect
  | cons hdirect htail ih =>
    exact .indirect (.direct hdirect) ih

/-- Example 2: The destination can be reached from any segment in the walk -/
example (h : FullWalk graph origin dest segments) (hseg : seg ∈ segments) : ∃ segs, FullWalk graph seg dest segs := by
  induction h using FullWalk.cons_induction with
  | @direct ctx origin dest hdirect =>
    simp at hseg
  | @cons ctx origin head dest tail hdirect htail ih =>
    simp at hseg
    rcases hseg with rfl | hseg
    · exact ⟨tail, htail⟩
    · exact ih hseg

/-- Example 3: Non-empty segments implies origin is different from first segment
    (uses pattern matching after induction) -/
example (h : FullWalk ctx origin dest segments) (hne : segments ≠ []) :
    ∃ head tail, segments = head :: tail ∧ DirectRef ctx origin head := by
  induction h using FullWalk.cons_induction with
  | direct hdirect =>
    simp at hne
  | @cons ctx origin head dest tail hdirect htail ih =>
    exact ⟨head, tail, rfl, hdirect⟩







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
  | insert_min a s' ha_notin hlt ih =>
    -- Here we have access to:
    -- a : ℕ                        (the minimum element)
    -- s' : Finset ℕ                (the rest of the set)
    -- ha_notin : a ∉ s'            (a is not in s')
    -- hlt : ∀ x ∈ s', a < x        (a is smaller than everything in s')
    -- ih : True                    (induction hypothesis)
    trivial

-- Example 6: Build a witness that uses the ordering
def Finset.headIfNonempty (s : Finset ℕ) : Option ℕ :=
  Finset.minRecOn s
    none
    (fun a _ _ _ _ => some a)

lemma Finset.headIfNonempty_example : Finset.headIfNonempty {5, 3, 8} = some 3 := by native_decide
lemma Finset.headIfNonempty_empty : Finset.headIfNonempty ∅ = none := by native_decide

end MinRecOnExamples







/-- A walk's origin always links directly to its first path segment -/
@[grind .]
theorem FullWalk.ref_segment_cons
  (h : FullWalk ctx origin dest segments)
  (hsegeq : segments = head :: tail)
  : DirectRef ctx origin head := by
  induction h generalizing tail head with
  | direct h => simp at hsegeq
  | indirect walka walkb combeq aih bih =>
    expose_names
    simp [*] at *
    cases segments₁ with
    | nil => grind
    | cons head' tail' => grind




/-- A walk's last segment always links directly to its destination -/
@[grind →]
theorem FullWalk.ref_segment_arse
  (h : FullWalk graph origin dest segments)
  (hsegeq : segments = body ++ [bum])
  : DirectRef graph bum dest := by
  induction h generalizing body bum with
  | direct h => simp at hsegeq
  | indirect walka walkb combeq aih bih =>
    expose_names
    induction segments₂ using List.reverseRecOn with
    | nil =>
      simp [*] at *
      have : body = segments₁ := List.append_inj_left' combeq rfl
      have : bum = b := by simpa [this] using combeq
      subst_eqs
      cases walkb with
      | indirect _ _ h => simp at h
      | direct h => exact h
    | append_singleton body' bum' ih =>
      symm at combeq
      rw [hsegeq, ←List.append_assoc] at combeq
      have : [bum'].length = [bum].length := by simp
      have := List.append_inj_right' combeq this
      simp at this
      subst_eqs
      grind



/-- If path traverses through at least one segment, given a walk, return a new walk with the origin snipped off the start -/
@[grind →]
theorem FullWalk.cons_head_segment
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
  | indirect walka walkb combeq aih bih =>
    expose_names
    induction segments₂ using List.reverseRecOn with
    | nil =>
      simp [*] at *
      have : body = segments₁ := List.append_inj_left' combeq rfl
      have : bum = b := by simpa [this] using combeq
      subst_eqs
      cases walkb with
      | indirect _ _ h => simp at h
      | direct h => exact walka
    | append_singleton body' bum' ih =>
      rw [hsegeq, ←List.append_assoc] at combeq
      have : body = segments₁ ++ [b] ++ body' := List.append_inj_left' combeq rfl
      have : bum = bum' := by simpa [this] using combeq
      cases segments₁ using List.reverseRecOn with
      | nil =>
        simp [*] at *
        refine .indirect walka bih rfl
      | append_singleton body₁ bum₁ ih₁ =>
        simp [*] at *
        refine .indirect walka bih ?_
        simp

omit [Fintype V] [DecidableEq V] in
/-- Induction principle for `FullWalk` that works by adding one segment at a time from the back.

To prove a property about an arbitrary `FullWalk ctx origin dest segments`,
it suffices to prove it for:
1. Direct walks (empty segments)
2. Show that if it holds for a walk from `origin` to `bum` with segments `body`,
   and there's a direct reference from `bum` to `dest`,
   then it holds for the walk from `origin` to `dest` with segments `body ++ [bum]`.
-/
-- @[elab_as_elim]
theorem FullWalk.snoc_induction
    {motive : ∀ (graph : Graph) (origin dest : V) (segments : List V), FullWalk graph origin dest segments → Prop}
    (direct : ∀ {graph} {origin} {dest} (h : DirectRef graph origin dest),
              motive graph origin dest [] (.direct h))
    (snoc : ∀ {graph} {origin} {bum} {dest} {body}
              (hbody : FullWalk graph origin bum body)
              (hdirect : DirectRef graph bum dest),
              motive graph origin bum body hbody →
              motive graph origin dest (body ++ [bum])
                (.indirect hbody (.direct hdirect) (by simp)))
    {graph origin dest segments}
    (h : FullWalk graph origin dest segments)
    : motive graph origin dest segments h := by
  induction segments using List.reverseRecOn generalizing dest with
  | nil =>
    cases h with
    | direct dref => exact @direct graph origin dest dref
    | indirect walka walkb combeq =>
      simp at combeq
  | append_singleton body bum ih =>
    -- Get the "init" walk from origin to bum
    have hbody : FullWalk graph origin bum body := h.snoc_arse_segment rfl
    -- Get the direct reference from bum to dest
    have hdref := h.ref_segment_arse rfl
    -- Apply IH to the body walk
    have hbody_ih := ih hbody
    -- Use proof irrelevance to match the walk structure
    have : h = .indirect hbody (.direct hdref) (by simp) := by
      apply proof_irrel
    rw [this]
    exact @snoc graph origin bum dest body hbody hdref hbody_ih


-- Example usages of snoc_induction

/-- Example: For any walk, the origin can reach the destination (using snoc_induction) -/
example (h : FullWalk graph origin dest segments) : Walk graph origin dest := by
  induction h using FullWalk.snoc_induction with
  | direct hdirect =>
    exact .direct hdirect
  | snoc hbody hdirect ih =>
    exact .indirect ih (.direct hdirect)

/-- Example: The origin can reach any segment in the walk (dual of cons version) -/
example (h : FullWalk ctx origin dest segments) (hseg : seg ∈ segments) : ∃ segs, FullWalk ctx origin seg segs := by
  induction h using FullWalk.snoc_induction with
  | @direct graph origin dest hdirect =>
    simp at hseg
  | @snoc graph origin bum dest body hbody hdirect ih =>
    simp at hseg
    rcases hseg with hseg | rfl
    · exact ih hseg
    · exact ⟨body, hbody⟩

/-- Example: Non-empty segments implies last segment links to dest -/
example (h : FullWalk ctx origin dest segments) (hne : segments ≠ []) :
    ∃ body bum, segments = body ++ [bum] ∧ DirectRef ctx bum dest := by
  induction h using FullWalk.snoc_induction with
  | direct hdirect =>
    simp at hne
  | @snoc ctx origin bum dest body hbody hdirect ih =>
    exact ⟨body, bum, rfl, hdirect⟩





/-- Make a path from the origin to the first segment of the second one -/
@[grind →]
theorem FullWalk.cons_slice_head_of_h₂
  (h₁ : FullWalk ctx a b segments₁)
  (h₂ : FullWalk ctx b c (head₂ :: tail₂))
  : FullWalk ctx a head₂ (segments₁ ++ [b]) := by
  induction h₁ with
  | direct h =>
    simp
    expose_names
    refine .indirect (segments₁:=[]) (segments₂:=[]) (b:=dest) (.direct h) ?_ ?_
    · have := FullWalk.segments_structure h₂
      simp at this
      refine .direct this.left
    · simp
  | indirect walka walkb combeq aih bih =>
    expose_names
    have := bih h₂
    have := FullWalk.indirect (combinedSegments:=segments₁_1 ++ [b_1] ++ segments₂ ++ [c_1]) walka this (by simp)
    simp [*] at this ⊢
    exact this




/-- Make a path from the first segment of the first one to the end of the 2nd one -/
@[grind →]
theorem FullWalk.cons_slice_last_of_h₁
  (h₁ : FullWalk ctx a b (head₁ :: tail₁))
  (h₂ : FullWalk ctx b c segments₂)
  : FullWalk ctx head₁ c (tail₁ ++ [b] ++ segments₂) := by
  have := FullWalk.segments_structure h₂
  rcases this with ⟨heq,dref⟩ | ⟨b',tailSegs,segeq,dref⟩
  · subst_eqs
    simp [*]
    have := FullWalk.cons_head_segment h₁ rfl
    refine .indirect this h₂ ?_
    simp
  · have := FullWalk.cons_head_segment h₁ rfl
    refine .indirect this h₂ ?_
    simp






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
  cases h using FullWalk.cons_induction with
  | direct dref =>
    simp
    refine .direct dref
  | cons dref tail =>
    expose_names
    clear h
    if hin : origin ∈ head :: tail_1 then
      simp at hin
      rcases hin with heq | hin
      · subst_eqs
        have ⟨removed, segs, hsegeq, nin, fw⟩ := tail.get_orig_nin_segs
        exists removed+1,segs, (by simp [*])
      · have ⟨i,hilen,heq⟩ := tail_1.getElem_of_mem hin
        have := tail.from_seg_to_end i hilen
        rw [heq] at this
        have ⟨removed, segs, hsegeq, nin, fw⟩ := this.get_orig_nin_segs
        exists i+removed+1+1, segs, ?_
        · rw [hsegeq]; simp; grind
        · tauto

    else
      exists 0, head :: tail_1, rfl
      simp [*]
      refine .indirect (.direct dref) tail ?_
      simp

  termination_by segments.length



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
      refine .indirect body (.direct dref) ?_
      simp

  termination_by segments.length




/-- Split at any middle section -/
theorem FullWalk.split_by_segs
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
        .indirect walk1 walk2 rfl
      -- This combined walk is shorter since i < j
      have hlen : (segments.take i ++ [segments[i]] ++ segments.drop (j + 1)).length < segments.length := by
        simp
        omega
      -- Recurse on the shorter walk
      exact combined.exists_non_dup

  termination_by segments.length
















def Walk.getReachables [Fintype V]
  (graph : Graph (V:=V))
  (current : V)
  (seenRefs : Finset V) :
  Finset V :=
  if _hin : current ∈ seenRefs then
    seenRefs
  else
    let nodes := graph current
    nodes.biUnion (λ node ↦ insert node (getReachables graph node (insert current seenRefs)))

  termination_by (Fintype.card V - seenRefs.card)
  decreasing_by
    simp [*]
    apply Nat.sub_lt_sub_left
    · apply Finset.card_lt_univ_of_notMem _hin
    · simp




theorem FullWalk.getReachables_complete
  {current : V}
  (hseenswalk : ∀ seen ∈ seenRefs, Walk graph seen current)
  (shortestWalk : FullWalk graph current dest segments)
  (noOverlap : ∀ seen ∈ seenRefs, seen ∉ current :: segments)
  (segsunique : (current :: segments).Nodup ∧ (dest :: segments).Nodup)
  : dest ∈ Walk.getReachables graph current seenRefs := by
  fun_induction Walk.getReachables graph current seenRefs
    generalizing segments dest
  with
  | case1 current seenRefs hin => simpa using noOverlap _ hin
  | @case2 current seenRefs ninseen nodes ih =>
    simp at noOverlap
    -- have : dest ∉ seenRefs := by grind
    simp [*]
    cases shortestWalk using FullWalk.cons_induction with
    | direct dref =>
      exists dest, dref
      simp
    | cons dref walk₂ ih =>
      clear ih
      expose_names
      exists head, dref
      simp at segsunique
      simp [*]
      apply ih head _ walk₂ _ (by grind)
      · simp [*]
        constructor
        · refine .direct dref
        · intro seen seenin
          refine .indirect ?_ (.direct dref)
          refine hseenswalk _ seenin
      · simp [*]
        grind



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
    exact ih child (.indirect horigtocurr (.direct dref)) prf







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
      | indirect _ _ hh => simp at hh
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
      · refine .indirect horigtocurr walkcurrtohead
      · simp
        constructor
        · exact walkcurrtohead
        · intro seen seenin
          refine .indirect ?_ walkcurrtohead
          exact hseenswalk seen seenin
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
          | indirect _ _ h => simp at h
        | cons head tail =>
          have dref := fw.ref_segment_cons rfl
          have dec := hresult head dref
          absurd dec
          simp
          refine fw.decideBool_complete (seenRefs:=∅) (segsprecurr:=[]) (segspostcurr:=tail) (.direct dref) (by simp) (current:=head) (by simp) (by simp) ?_
          grind








@[simp,reducible,grind]
def HasCycle ctx (i : V) := Walk ctx i i



instance HasCycle.decide (ctx : Graph) (i : V) :
  Decidable (HasCycle ctx i) :=
    Walk.decide ctx i i
