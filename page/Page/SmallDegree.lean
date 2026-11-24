import Page.Bounds

namespace Page.DartGraph

/-- The repaired degree-at-most-five argument. In a nonempty star of size
at most five a permutation avoiding both fixed points and transpositions
is a single cycle. The condition r(r(a)) ≠ a tests both obstructions. -/
theorem small_star_cycle {D : Type} [DecidableEq D] (r : D → D) (s : List D)
    (hne : s ≠ []) (size : s.length ≤ 5) (perm : (s.map r).Perm s)
    (noShort : ∀ a ∈ s, r (r a) ≠ a) : ∃ w, w.Perm s ∧ Follows r w := by
  obtain ⟨cycles, hp, follows⟩ := exists_cycle_partition r s perm
  have long (w : List D) (hm : w ∈ cycles) : 3 ≤ w.length := by
    have hw := follows w hm
    have inc : ∀ a ∈ w, a ∈ s := fun _ ha => hp.subset (List.mem_flatten_of_mem hm ha)
    cases w with
    | nil => exact False.elim hw
    | cons a as =>
      have ha := inc a (by simp)
      cases as with
      | nil =>
        have fixed : r a = a := by simpa [Follows] using hw
        exact False.elim (noShort a ha (by simp [fixed]))
      | cons b bs =>
        cases bs with
        | nil =>
          have pair : r a = b ∧ r b = a := by simpa [Follows] using hw
          exact False.elim (noShort a ha (by rw [pair.1, pair.2]))
        | cons c cs => simp
  have count := min_length_sum cycles 3 long
  rw [hp.length_eq] at count
  cases cycles with
  | nil =>
    have empty := hp.length_eq
    simp_all
  | cons w ws =>
    cases ws with
    | nil => exact ⟨w, by simpa using hp, follows w (by simp)⟩
    | cons t ts => simp only [List.length_cons] at count; omega

/-- For preprocessed graphs of degrees 3, 4 or 5, the no-short-cycle condition
suffices whenever the reconstructed successor permutes every star. -/
theorem low_degree_rotation (G : DartGraph) (r : G.Dart → G.Dart)
    (maxDegree : ∀ v, (G.star v).length ≤ 5)
    (perm : ∀ v, ((G.star v).map r).Perm (G.star v))
    (noShort : ∀ a, r (r a) ≠ a) : G.IsLocalRotation r := by
  apply (G.isLocalRotation_iff r).mpr
  intro v hne
  exact small_star_cycle r _ hne (maxDegree v) (perm v) (fun a _ => noShort a)

end Page.DartGraph
