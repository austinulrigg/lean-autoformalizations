import Page.Rotation
import Page.Walk

/-!
Local completion for PAGE's partial rotations. At each vertex, try to complete
the forced turns to one circular order on exactly the darts of that star.
This checks all vertex degrees and also keeps both occurrences of a bridge.
-/
namespace Page

private def finishCycle {D : Type} [DecidableEq D] (allow : D → D → Bool)
    (first : D) : Nat → D → List D → Bool
  | 0, current, remaining => remaining.isEmpty && allow current first
  | k+1, current, remaining =>
    remaining.any fun d =>
      allow current d && finishCycle allow first k d (remaining.erase d)

private theorem finishCycle_iff {D : Type} [DecidableEq D] (allow : D → D → Bool)
    (first : D) (k : Nat) (current : D) (remaining : List D) :
    finishCycle allow first k current remaining = true ↔
    ∃ path, path.Perm remaining ∧ path.length = k ∧ AllowedPath allow first current path := by
  induction k generalizing current remaining with
  | zero =>
    simp only [finishCycle, Bool.and_eq_true, List.isEmpty_iff, List.length_eq_zero_iff]
    constructor
    · rintro ⟨rfl, ha⟩
      exact ⟨[], .refl _, rfl, ha⟩
    · rintro ⟨_, hp, rfl, ha⟩
      exact ⟨List.perm_nil.mp hp.symm, ha⟩
  | succ k ih =>
    simp only [finishCycle, List.any_eq_true, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨a, ha, hc, path, hp, hk, hallow⟩
      exact ⟨a :: path, (hp.cons a).trans (List.perm_cons_erase ha).symm,
        by simp [hk], hc, hallow⟩
    · rintro ⟨path, hp, hk, hallow⟩
      cases path with
      | nil => simp at hk
      | cons a path =>
        have ha := hp.mem_iff.mp (List.mem_cons_self (a := a) (l := path))
        have he := hp.trans (List.perm_cons_erase ha)
        exact ⟨a, ha, hallow.1, path, he.cons_inv, by simpa using hk, hallow.2⟩

/-- A cyclic order of the entire star in which each successive transition is allowed.
An empty star has the unique empty order. -/
def HasAllowedCycle {D : Type} (allow : D → D → Bool) (star : List D) : Prop :=
  star = [] ∨ ∃ first path, (first :: path).Perm star ∧ AllowedPath allow first first path

private def canComplete {D : Type} [DecidableEq D] (allow : D → D → Bool) (star : List D) : Bool :=
  star.isEmpty || star.any fun a => finishCycle allow a (star.length - 1) a (star.erase a)

private theorem canComplete_iff {D : Type} [DecidableEq D] (allow : D → D → Bool) (star : List D) :
    canComplete allow star = true ↔ HasAllowedCycle allow star := by
  simp only [canComplete, HasAllowedCycle, Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true,
    finishCycle_iff]
  apply or_congr_right
  constructor
  · rintro ⟨a, ha, path, hp, _, hl⟩
    exact ⟨a, path, (hp.cons a).trans (List.perm_cons_erase ha).symm, hl⟩
  · rintro ⟨a, path, hp, hl⟩
    have ha := hp.mem_iff.mp (List.mem_cons_self (a := a) (l := path))
    have he := hp.trans (List.perm_cons_erase ha)
    have hlen := hp.length_eq
    simp only [List.length_cons] at hlen
    exact ⟨a, ha, path, he.cons_inv, by omega, hl⟩

namespace DartGraph

/-- Is x → y compatible with every turn already prescribed by a selected face?
A consecutive pair (a,b) in a facial walk forces the local turn rev(a) → b. -/
def allowsTurn (G : DartGraph) (picked : List (List G.Dart)) (x y : G.Dart) : Bool :=
  (picked.flatMap turnPairs).all fun ab => decide (G.rev ab.1 = x → ab.2 = y)

/-- Discard a prefix if a vertex's prescribed turns cannot be part of one cycle. -/
def viable (G : DartGraph) (picked : List (List G.Dart)) : Bool :=
  (List.finRange G.vertices).all fun v => canComplete (G.allowsTurn picked) (G.star v)

/-- Exact specification of the local feasibility test, including high-degree vertices. -/
theorem viable_iff (G : DartGraph) (picked : List (List G.Dart)) :
    G.viable picked = true ↔ ∀ v, HasAllowedCycle (G.allowsTurn picked) (G.star v) := by
  simp only [viable, List.all_eq_true, canComplete_iff, List.mem_finRange, true_implies]

/-- Every partial family of facial walks of a genuine rotation survives pruning. -/
theorem viable_of_rotation (G : DartGraph) (r : G.Dart → G.Dart)
    (hr : G.IsLocalRotation r) (picked : List (List G.Dart))
    (h : ∀ w ∈ picked, Follows (G.faceStep r) w) : G.viable picked = true := by
  have legal (x : G.Dart) : G.allowsTurn picked x (r x) = true := by
    simp only [allowsTurn, List.all_eq_true, decide_eq_true_eq]
    intro ab hab hx
    obtain ⟨w, hw, hm⟩ := List.mem_flatMap.mp hab
    rw [turnPairs_of_follows _ _ (h w hw)] at hm
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
    exact congrArg r hx
  apply (G.viable_iff picked).mpr
  intro v
  by_cases he : G.star v = []
  · exact Or.inl he
  · obtain ⟨w, hp, hf⟩ := G.local_word hr v he
    cases w with
    | nil => exact False.elim hf
    | cons a path => exact Or.inr ⟨a, path, hp, allowedPath_of_map _ r legal a a path hf⟩

end DartGraph
end Page
