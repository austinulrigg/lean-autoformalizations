import Std

namespace Page

/-- Try exact face counts n, n-1, ..., 0, stopping at the first success. -/
def descending {α : Type} (attempt : Nat → Option α) : Nat → Option α
  | 0 => attempt 0
  | n+1 => match attempt (n+1) with
    | some x => some x
    | none => descending attempt n

theorem descending_chosen {α : Type} (attempt : Nat → Option α) {n : Nat} {out : α}
    (h : descending attempt n = some out) : ∃ j ≤ n, attempt j = some out := by
  induction n with
  | zero => exact ⟨0, by omega, h⟩
  | succ n ih =>
    simp only [descending] at h
    split at h
    next x hx => exact ⟨n+1, by omega, hx.trans h⟩
    next => obtain ⟨j, hj, hx⟩ := ih h; exact ⟨j, by omega, hx⟩

theorem descending_dominates {α : Type} (attempt : Nat → Option α) {n k : Nat}
    (le : k ≤ n) (hit : ∃ x, attempt k = some x) :
    ∃ j x, k ≤ j ∧ attempt j = some x ∧ descending attempt n = some x := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    obtain ⟨x, hx⟩ := hit
    exact ⟨0, x, by omega, hx, hx⟩
  | succ n ih =>
    cases h : attempt (n+1) with
    | some x => exact ⟨n+1, x, le, h, by simp [descending, h]⟩
    | none =>
      have lt : k ≤ n := by
        by_cases heq : k = n+1
        · obtain ⟨x, hx⟩ := hit
          simp [heq, h] at hx
        · omega
      obtain ⟨j, x, hj, hx, ho⟩ := ih lt
      exact ⟨j, x, hj, hx, by simp [descending, h, ho]⟩

theorem length_le_flatten {α : Type} (fs : List (List α)) (hne : ∀ w ∈ fs, w ≠ []) :
    fs.length ≤ fs.flatten.length := by
  induction fs with
  | nil => simp
  | cons w ws ih =>
    have h := ih (fun x hx => hne x (by simp [hx]))
    have hw : 0 < w.length := List.length_pos_iff.mpr (hne w (by simp))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- Each remaining face must consume at least one still-unused dart. -/
def budget {α : Type} (darts target : Nat) (picked : List (List α)) : Bool :=
  decide (picked.length ≤ target ∧ target ≤ picked.length + (darts - picked.flatten.length))

theorem budget_safe {α : Type} {darts : List α} {rem picked target : List (List α)}
    (hc : target.flatten.Perm darts) (hn : ∀ w ∈ target, w ≠ [])
    (hp : (rem ++ picked).Perm target) : budget darts.length target.length picked = true := by
  have remaining := length_le_flatten rem (fun w hw => hn w (hp.subset (List.mem_append_left _ hw)))
  have faceCount := hp.length_eq
  have dartCount := (hp.flatten.trans hc).length_eq
  simp only [List.length_append, List.flatten_append] at faceCount dartCount
  apply decide_eq_true
  omega

end Page
