import Page.OrbitCount
import Page.Rotation

namespace Page.DartGraph

/-- At the head of a dart, an immediate reversal is possible exactly when the
star has a single dart. This permits the forced reversal at a leaf. -/
def legalTurn (G : DartGraph) (a b : G.Dart) : Bool :=
  decide (G.tail b = G.tail (G.rev a) ∧
    (b ≠ G.rev a ∨ (G.star (G.tail b)).length = 1))

theorem degree_one_of_rotation_fixed (G : DartGraph) {r : G.Dart → G.Dart}
    (hr : G.IsLocalRotation r) (a : G.Dart) (hfix : r a = a) :
    (G.star (G.tail a)).length = 1 := by
  let star := G.star (G.tail a)
  have ha : a ∈ star := (G.mem_star _ _).mpr rfl
  have hne : star ≠ [] := by intro e; simp [e] at ha
  obtain ⟨w, hw, cycle⟩ := G.local_word hr (G.tail a) hne
  have singleton : Follows r [a] := by simp [Follows, hfix]
  have allEqual (b : G.Dart) (hb : b ∈ star) : b = a := by
    have hb' := cycle.same_darts singleton (hw.mem_iff.mpr ha) (by simp : a ∈ [a])
      (hw.mem_iff.mpr hb)
    simpa using hb'
  have nd : star.Nodup := G.darts_nodup.filter _
  change star.length = 1
  cases eq : star with
  | nil => exact False.elim (hne eq)
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hx := allEqual x (by simp [eq])
      have hy := allEqual y (by simp [eq])
      have neq : x ∉ y :: ys := (List.nodup_cons.mp (eq ▸ nd)).1
      exact False.elim (neq (by simp [hx, hy]))

/-- Every facial transition of every local rotation passes the concrete trail
generator's incidence and reversal filters. -/
theorem legal_faceStep (G : DartGraph) (r : G.Dart → G.Dart)
    (hr : G.IsLocalRotation r) (a : G.Dart) : G.legalTurn a (G.faceStep r a) = true := by
  apply decide_eq_true
  refine ⟨G.preserves_tail hr _, ?_⟩
  by_cases h : r (G.rev a) = G.rev a
  · exact Or.inr (by simpa [faceStep, h] using G.degree_one_of_rotation_fixed hr (G.rev a) h)
  · exact Or.inl h

end Page.DartGraph
