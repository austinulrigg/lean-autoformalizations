import Page.Walk

namespace Page

variable {D : Type} [DecidableEq D]

/-- Extend the trail along an allowed turn, removing the used dart before the
recursive call. A prefix is emitted as soon as its closing turn is legal and
can still be extended to find longer trails. -/
def extendTrail (turn : D → D → Bool) (first : D) : Nat → D → List D → List (List D)
  | 0, current, _ => if turn current first then [[]] else []
  | k + 1, current, unused =>
    (if turn current first then [[]] else []) ++ unused.flatMap fun d =>
      if turn current d then
        (extendTrail turn first k d (unused.filter (· != d))).map (d :: ·)
      else []

theorem extendTrail_complete (turn : D → D → Bool) (first : D)
    (k : Nat) (current : D) (unused w : List D) (hn : w.Nodup)
    (ha : AllowedPath turn first current w) (hm : ∀ a ∈ w, a ∈ unused)
    (hl : w.length ≤ k) : w ∈ extendTrail turn first k current unused := by
  induction k generalizing current unused w with
  | zero =>
    have hw : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    simp [extendTrail, show turn current first = true from ha]
  | succ k ih =>
    rw [extendTrail, List.mem_append]
    cases w with
    | nil => exact Or.inl (by simp [show turn current first = true from ha])
    | cons d ds =>
      apply Or.inr
      refine List.mem_flatMap.mpr ⟨d, hm _ (by simp), ?_⟩
      rw [if_pos ha.1]
      refine List.mem_map.mpr ⟨ds, ih d _ ds (List.nodup_cons.mp hn).2 ha.2 ?_ ?_, rfl⟩
      · intro a has
        have hne : a ≠ d := fun e => (List.nodup_cons.mp hn).1 (e ▸ has)
        simp [hm _ (List.mem_cons_of_mem _ has), hne]
      · simpa using hl

theorem extendTrail_sound (turn : D → D → Bool) (first : D)
    (k : Nat) (current : D) (unused w : List D) (hw : w ∈ extendTrail turn first k current unused) :
    w.Nodup ∧ AllowedPath turn first current w ∧ ∀ a ∈ w, a ∈ unused := by
  induction k generalizing current unused w with
  | zero =>
    simp only [extendTrail] at hw
    split at hw
    next h =>
      have he : w = [] := by simpa using hw
      subst w
      exact ⟨by simp, h, by simp⟩
    next => simp at hw
  | succ k ih =>
    rw [extendTrail, List.mem_append] at hw
    rcases hw with hw | hw
    · split at hw
      next h =>
        have he : w = [] := by simpa using hw
        subst w
        exact ⟨by simp, h, by simp⟩
      next => simp at hw
    · obtain ⟨d, hd, hw⟩ := List.mem_flatMap.mp hw
      split at hw
      next legal =>
        obtain ⟨ds, hds, rfl⟩ := List.mem_map.mp hw
        obtain ⟨hn, hc, hm⟩ := ih _ _ _ hds
        have hnd : d ∉ ds := by
          intro hh
          have he := (List.mem_filter.mp (hm d hh)).2
          simp at he
        refine ⟨List.nodup_cons.mpr ⟨hnd, hn⟩, ⟨legal, hc⟩, ?_⟩
        intro a h
        rcases List.mem_cons.mp h with rfl | h
        · exact hd
        · exact (List.mem_filter.mp (hm _ h)).1
      next => simp at hw

theorem extendTrail_length (turn : D → D → Bool) (first : D) (k : Nat) (current : D)
    (unused w : List D) (hw : w ∈ extendTrail turn first k current unused) : w.length ≤ k := by
  induction k generalizing current unused w with
  | zero =>
    simp only [extendTrail] at hw
    split at hw <;> simp_all
  | succ k ih =>
    rw [extendTrail, List.mem_append] at hw
    rcases hw with hw | hw
    · split at hw <;> simp_all
    · obtain ⟨_, _, hw⟩ := List.mem_flatMap.mp hw
      split at hw
      · obtain ⟨tail, h, rfl⟩ := List.mem_map.mp hw
        exact Nat.succ_le_succ (ih _ _ tail h)
      · simp at hw

/-- Enumerate closed dart-simple trails of at most maxLength darts through the
required dart. Cyclic representatives remain distinct. -/
def boundedTrailPool (alphabet : List D) (turn : D → D → Bool) :
    Nat → D → List (List D)
  | 0, _ => []
  | k+1, required =>
    alphabet.flatMap fun first =>
      ((extendTrail turn first k first (alphabet.filter (· != first))).map (first :: ·)).filter
        (·.contains required)

/-- Every enumerated candidate obeys the length cap and is a genuine closed
directed trail, including the last-to-first adjacency. -/
theorem boundedTrailPool_sound (alphabet : List D) (turn : D → D → Bool)
    (maxLength : Nat) (required : D) (w : List D)
    (hw : w ∈ boundedTrailPool alphabet turn maxLength required) :
    w.length ≤ maxLength ∧ required ∈ w ∧ ∃ first path, w = first :: path ∧ w.Nodup ∧
      (∀ d ∈ w, d ∈ alphabet) ∧ AllowedPath turn first first path := by
  cases maxLength with
  | zero => simp [boundedTrailPool] at hw
  | succ k =>
    obtain ⟨first, hfirst, hh⟩ := List.mem_flatMap.mp hw
    obtain ⟨hs, ht⟩ := List.mem_filter.mp hh
    obtain ⟨path, hp, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hn, hl, hm⟩ := extendTrail_sound _ _ _ _ _ _ hp
    have hfirst' : first ∉ path := by
      intro hh
      have h := (List.mem_filter.mp (hm first hh)).2
      simp at h
    refine ⟨Nat.succ_le_succ (extendTrail_length _ _ _ _ _ _ hp), by simpa using ht,
      first, path, rfl, List.nodup_cons.mpr ⟨hfirst', hn⟩, ?_, hl⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hfirst
    · exact (List.mem_filter.mp (hm a ha)).1

/-- Every facial successor cycle within the bound occurs at every one of its
darts, with the same cyclic representative as the input word. -/
theorem boundedTrailPool_complete (alphabet : List D) (turn : D → D → Bool) (maxLength : Nat)
    (f : D → D) (legal : ∀ a, turn a (f a) = true) (first : D) (w : List D)
    (step : (first :: w).map f = w ++ [first])
    (mem : ∀ a ∈ first :: w, a ∈ alphabet) (simple : (first :: w).Nodup)
    (bound : (first :: w).length ≤ maxLength) {required : D}
    (hit : required ∈ first :: w) :
    first :: w ∈ boundedTrailPool alphabet turn maxLength required := by
  cases maxLength with
  | zero => simp at bound
  | succ k =>
    refine List.mem_flatMap.mpr ⟨first, mem _ (by simp), List.mem_filter.mpr ⟨?_, by simpa using hit⟩⟩
    refine List.mem_map.mpr ⟨w, ?_, rfl⟩
    apply extendTrail_complete _ _ _ _ _ _ (List.nodup_cons.mp simple).2
      (allowedPath_of_map _ f legal first first w step)
    · intro a ha
      have hne : a ≠ first := fun e => (List.nodup_cons.mp simple).1 (e ▸ ha)
      simp [mem _ (List.mem_cons_of_mem _ ha), hne]
    · simpa using bound

end Page
