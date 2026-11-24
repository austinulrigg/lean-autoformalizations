import Page.Generator
import Page.Rotation

namespace Page

/-- Decide if the first dart is the least one in the word. -/
def isCanonical {n : Nat} : List (Fin n) → Bool
  | [] => true
  | first :: tail => tail.all fun d => decide (first ≤ d)

private def least {n : Nat} (a : Fin n) : List (Fin n) → Fin n
  | [] => a
  | b :: bs => least (if a ≤ b then a else b) bs

private theorem least_spec {n : Nat} (a : Fin n) (xs : List (Fin n)) :
    least a xs ∈ a :: xs ∧ ∀ b ∈ a :: xs, least a xs ≤ b := by
  induction xs generalizing a with
  | nil => simp [least]
  | cons x xs ih =>
    by_cases h : a ≤ x
    · simp only [least, if_pos h]
      obtain ⟨hm, hb⟩ := ih a
      constructor
      · rcases List.mem_cons.mp hm with e | e <;> simp [e]
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hb _ (by simp)
        · rcases List.mem_cons.mp hd with rfl | hd
          · exact Nat.le_trans (hb a (by simp)) h
          · exact hb _ (List.mem_cons_of_mem _ hd)
    · simp only [least, if_neg h]
      obtain ⟨hm, hb⟩ := ih x
      exact ⟨List.mem_cons_of_mem _ hm, fun d hd => by
        rcases List.mem_cons.mp hd with rfl | hd
        · have := hb x (by simp); omega
        · exact hb _ hd⟩

private def least? {n : Nat} : List (Fin n) → Option (Fin n)
  | [] => none
  | a :: as => some (least a as)

private theorem least_none {n : Nat} {w : List (Fin n)} (h : least? w = none) : w = [] := by
  cases w <;> simp_all [least?]

private theorem least_some {n : Nat} {w : List (Fin n)} {a : Fin n} (h : least? w = some a) :
    a ∈ w ∧ ∀ b ∈ w, a ≤ b := by
  cases w with
  | nil => simp [least?] at h
  | cons x xs =>
    have eq := Option.some.inj h
    exact eq ▸ least_spec x xs

/-- Start each circular word at its least dart, preserving its orientation. -/
def canonicalWord {n : Nat} (w : List (Fin n)) : List (Fin n) :=
  match least? w with
  | none => []
  | some a => w.drop (w.idxOf a) ++ w.take (w.idxOf a)

private theorem splitAtLeast {n : Nat} {w : List (Fin n)} {a : Fin n}
    (ha : least? w = some a) :
    ∃ pre post, w = pre ++ a :: post ∧ canonicalWord w = a :: (post ++ pre) := by
  have hmem := (least_some ha).1
  have hi := List.idxOf_lt_length_of_mem hmem
  have he : w[w.idxOf a]'hi = a := by
    apply eq_of_beq
    exact List.findIdx_getElem (p := (· == a)) (w := hi)
  have hd := List.drop_eq_getElem_cons hi
  rw [he] at hd
  refine ⟨w.take (w.idxOf a), w.drop (w.idxOf a + 1), ?_, ?_⟩
  · rw [← hd, List.take_append_drop]
  · simp [canonicalWord, ha, hd]

theorem canonicalWord_perm {n : Nat} (w : List (Fin n)) : (canonicalWord w).Perm w := by
  cases h : least? w with
  | none => have he := least_none h; subst w; exact .nil
  | some a =>
    obtain ⟨pre, post, hw, hc⟩ := splitAtLeast h
    rw [hc, hw]
    exact (List.perm_append_comm (l₁ := a :: post) (l₂ := pre))

theorem canonicalWord_follows {n : Nat} (f : Fin n → Fin n) (w : List (Fin n)) (hf : Follows f w) :
    Follows f (canonicalWord w) := by
  cases h : least? w with
  | none =>
    have he := least_none h
    subst w
    contradiction
  | some a =>
    obtain ⟨pre, post, hw, hc⟩ := splitAtLeast h
    rw [hc]
    exact DartGraph.follows_rebase f a pre post (hw ▸ hf)

theorem canonicalWord_isCanonical {n : Nat} (w : List (Fin n)) : isCanonical (canonicalWord w) = true := by
  cases h : least? w with
  | none => simp [canonicalWord, h, isCanonical]
  | some a =>
    obtain ⟨pre, post, _, hc⟩ := splitAtLeast h
    rw [hc]
    simp only [isCanonical, List.all_eq_true, decide_eq_true_eq]
    intro d hd
    have hm : d ∈ canonicalWord w := hc ▸ List.mem_cons_of_mem a hd
    exact (least_some h).2 _ ((canonicalWord_perm w).subset hm)

theorem canonical_flatten {n : Nat} (fs : List (List (Fin n))) :
    (fs.map canonicalWord).flatten.Perm fs.flatten := by
  induction fs with
  | nil => exact .nil
  | cons w ws ih => exact (canonicalWord_perm w).append ih

/-- Generate each oriented closed trail from its smallest dart. A smaller dart
can never appear later, so those extensions are pruned before recursion. -/
def canonicalCatalog {n : Nat} (alphabet : List (Fin n)) (turn : Fin n → Fin n → Bool) :
    Nat → List (List (Fin n))
  | 0 => []
  | k+1 => alphabet.flatMap fun first =>
    (extendTrail turn first k first (alphabet.filter (first < ·))).map (first :: ·)

/-- Compute the catalogue once and index its trails by required dart. -/
def canonicalPool {n : Nat} (alphabet : List (Fin n)) (turn : Fin n → Fin n → Bool) (cap : Nat) :
    Fin n → List (List (Fin n)) :=
  let catalog := canonicalCatalog alphabet turn cap
  fun d => catalog.filter (·.contains d)

/-- Soundness of the canonical catalogue. Every candidate is a bounded, closed,
dart-simple trail through the required dart, starting at its minimum dart. -/
theorem canonicalPool_sound {n : Nat} (alphabet : List (Fin n)) (turn : Fin n → Fin n → Bool)
    (cap : Nat) (required : Fin n) (w : List (Fin n)) (hw : w ∈ canonicalPool alphabet turn cap required) :
    w.length ≤ cap ∧ required ∈ w ∧ isCanonical w = true ∧
      ∃ first path, w = first :: path ∧ w.Nodup ∧ (∀ a ∈ w, a ∈ alphabet) ∧
        AllowedPath turn first first path := by
  obtain ⟨hh, hit⟩ := List.mem_filter.mp hw
  cases cap with
  | zero => simp [canonicalCatalog] at hh
  | succ k =>
    obtain ⟨first, hfirst, hs⟩ := List.mem_flatMap.mp hh
    obtain ⟨path, hp, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hn, hl, hm⟩ := extendTrail_sound _ _ _ _ _ _ hp
    have larger (d : Fin n) (hd : d ∈ path) : first < d := by
      simpa using (List.mem_filter.mp (hm d hd)).2
    have hnd : first ∉ path := fun he => Nat.lt_irrefl _ (larger first he)
    refine ⟨Nat.succ_le_succ (extendTrail_length _ _ _ _ _ _ hp), by simpa using hit, ?_,
      first, path, rfl, List.nodup_cons.mpr ⟨hnd, hn⟩, ?_, hl⟩
    · simp only [isCanonical, List.all_eq_true, decide_eq_true_eq]
      exact fun a ha => Nat.le_of_lt (larger a ha)
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hfirst
      · exact (List.mem_filter.mp (hm a ha)).1

theorem canonicalPool_complete {n : Nat} (alphabet : List (Fin n)) (turn : Fin n → Fin n → Bool)
    (maxLength : Nat) (f : Fin n → Fin n) (legal : ∀ a, turn a (f a) = true) (first : Fin n)
    (w : List (Fin n)) (step : (first :: w).map f = w ++ [first])
    (mem : ∀ a ∈ first :: w, a ∈ alphabet) (simple : (first :: w).Nodup)
    (bound : (first :: w).length ≤ maxLength) {required : Fin n}
    (hit : required ∈ first :: w) (canonical : isCanonical (first :: w) = true) :
    first :: w ∈ canonicalPool alphabet turn maxLength required := by
  apply List.mem_filter.mpr
  refine ⟨?_, by simpa using hit⟩
  cases maxLength with
  | zero => simp at bound
  | succ k =>
    refine List.mem_flatMap.mpr ⟨first, mem _ (by simp), ?_⟩
    refine List.mem_map.mpr ⟨w, ?_, rfl⟩
    apply extendTrail_complete _ _ _ _ _ _ (List.nodup_cons.mp simple).2
      (allowedPath_of_map _ f legal first first w step)
    · intro a ha
      have hne : a ≠ first := fun e => (List.nodup_cons.mp simple).1 (e ▸ ha)
      have hle : first ≤ a := by
        simp only [isCanonical, List.all_eq_true, decide_eq_true_eq] at canonical
        exact canonical _ ha
      exact List.mem_filter.mpr ⟨mem _ (List.mem_cons_of_mem _ ha), by simpa using
        (show first < a by omega)⟩
    · simpa using bound

end Page
