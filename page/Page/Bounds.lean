import Page.Turns

namespace Page.DartGraph

private def shortOne (G : DartGraph) := G.darts.any fun a => G.legalTurn a a

private def shortTwo (G : DartGraph) := G.darts.any fun a =>
  G.darts.any fun b => G.legalTurn a b && G.legalTurn b a

private def shortThree (G : DartGraph) := G.darts.any fun a =>
  G.darts.any fun b => G.legalTurn a b && G.darts.any fun c => G.legalTurn b c && G.legalTurn c a

/-- A lower bound on every facial length, obtained by looking for legal
closed walks of lengths 1, 2, and 3 in that order. -/
def minFaceLength (G : DartGraph) : Nat :=
  if G.shortOne then 1 else if G.shortTwo then 2 else if G.shortThree then 3 else 4

theorem minFaceLength_pos (G : DartGraph) : 0 < G.minFaceLength := by
  unfold minFaceLength
  repeat' split
  all_goals decide

theorem minFaceLength_le (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    {w : List G.Dart} (hw : Follows (G.faceStep r) w) : G.minFaceLength ≤ w.length := by
  have member (a : G.Dart) : a ∈ G.darts := List.mem_finRange _
  have turn {a b : G.Dart} (e : G.faceStep r a = b) : G.legalTurn a b = true :=
    e ▸ G.legal_faceStep r hr a
  cases w with
  | nil => contradiction
  | cons a as =>
    cases as with
    | nil =>
      have e : G.faceStep r a = a := by simpa [Follows] using hw
      have h : G.shortOne = true := List.any_eq_true.mpr ⟨a, member a, turn e⟩
      simp [minFaceLength, h]
    | cons b bs =>
      cases bs with
      | nil =>
        have e : G.faceStep r a = b ∧ G.faceStep r b = a := by simpa [Follows] using hw
        have h : G.shortTwo = true := List.any_eq_true.mpr ⟨a, member a, List.any_eq_true.mpr
          ⟨b, member b, Bool.and_eq_true_iff.mpr ⟨turn e.1, turn e.2⟩⟩⟩
        simp only [minFaceLength, h, if_true, List.length_cons, List.length_nil]
        split <;> decide
      | cons c cs =>
        cases cs with
        | nil =>
          have e : G.faceStep r a = b ∧ G.faceStep r b = c ∧ G.faceStep r c = a := by
            simpa [Follows] using hw
          have h : G.shortThree = true := List.any_eq_true.mpr ⟨a, member a, List.any_eq_true.mpr
            ⟨b, member b, Bool.and_eq_true_iff.mpr ⟨turn e.1, List.any_eq_true.mpr
              ⟨c, member c, Bool.and_eq_true_iff.mpr ⟨turn e.2.1, turn e.2.2⟩⟩⟩⟩⟩
          simp only [minFaceLength, h, if_true, List.length_cons, List.length_nil]
          repeat' split
          all_goals decide
        | cons d ds =>
          simp only [minFaceLength, List.length_cons]
          repeat' split
          all_goals omega

theorem min_length_sum {D : Type} (fs : List (List D)) (bound : Nat)
    (h : ∀ w ∈ fs, bound ≤ w.length) : fs.length * bound ≤ fs.flatten.length := by
  induction fs with
  | nil => simp
  | cons w ws ih =>
    have h0 := h w (by simp)
    have h1 := ih (fun x hx => h x (by simp [hx]))
    simp only [List.length_cons, Nat.succ_mul, List.flatten_cons, List.length_append]
    omega

/-- Every rotation's face partition satisfies the initial face-count bound. -/
theorem target_bound (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    {fs : List (List G.Dart)} (hp : fs.flatten.Perm G.darts)
    (hw : ∀ w ∈ fs, Follows (G.faceStep r) w) :
    fs.length ≤ G.darts.length / G.minFaceLength := by
  apply (Nat.le_div_iff_mul_le G.minFaceLength_pos).mpr
  rw [← hp.length_eq]
  exact min_length_sum fs _ (fun w m => G.minFaceLength_le hr (hw w m))

/-- Fuel limit for the individual trail generator at a fixed target face count.
Each of the other faces uses at least the lower bound in darts. -/
theorem face_length_bound (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    {fs : List (List G.Dart)} (hp : fs.flatten.Perm G.darts)
    (hw : ∀ w ∈ fs, Follows (G.faceStep r) w) {w : List G.Dart} (hm : w ∈ fs) :
    w.length ≤ G.darts.length - (fs.length - 1) * G.minFaceLength := by
  let rest := fs.erase w
  have arrange : fs.Perm (w :: rest) := List.perm_cons_erase hm
  have hrest := min_length_sum rest G.minFaceLength (fun v hv =>
    G.minFaceLength_le hr (hw v (arrange.symm.subset (List.mem_cons_of_mem w hv))))
  have hfaces : fs.length = rest.length + 1 := arrange.length_eq
  have hdarts := arrange.flatten.symm.trans hp
  have hlen : w.length + rest.flatten.length = G.darts.length := by
    simpa only [List.flatten_cons, List.length_append] using hdarts.length_eq
  rw [hfaces, Nat.add_sub_cancel]
  omega

end Page.DartGraph
