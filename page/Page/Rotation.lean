import Page.Orbits

namespace Page

/-- A graph represented by oriented edge ends. The head of a dart is the tail
of its reverse. A fixed-point-free involution pairs the two darts of each edge. -/
structure DartGraph where
  vertices : Nat
  edges : Nat
  tail : Fin (2 * edges) → Fin vertices
  rev : Fin (2 * edges) → Fin (2 * edges)
  rev_involutive : ∀ a, rev (rev a) = a
  rev_ne : ∀ a, rev a ≠ a

namespace DartGraph

abbrev Dart (G : DartGraph) := Fin (2 * G.edges)
def darts (G : DartGraph) := List.finRange (2 * G.edges)
def star (G : DartGraph) (v : Fin G.vertices) :=
  G.darts.filter (fun a => G.tail a == v)
def faceStep (G : DartGraph) (r : G.Dart → G.Dart) (a : G.Dart) := r (G.rev a)

private def orbitWord {D : Type} (r : D → D) (a : D) : Nat → List D
  | 0 => []
  | n+1 => a :: orbitWord r (r a) n

/-- For a nonempty star, following the successor from its first dart must list
each dart of the star exactly once and then return to the start. -/
def SingleOn {D : Type} (r : D → D) : List D → Prop
  | [] => True
  | a :: as =>
    let w := orbitWord r a (as.length+1)
    w.Perm (a :: as) ∧ Follows r w

instance {D : Type} [DecidableEq D] (r : D → D) (s : List D) : Decidable (SingleOn r s) := by
  cases s <;> unfold SingleOn <;> infer_instance

def IsLocalRotation (G : DartGraph) (r : G.Dart → G.Dart) : Prop :=
  ∀ v, SingleOn r (G.star v)

instance (G : DartGraph) (r : G.Dart → G.Dart) : Decidable (G.IsLocalRotation r) := by
  unfold IsLocalRotation; infer_instance

/-- The successive pairs include the turn from the last dart back to the first. -/
def turnPairs {D : Type} : List D → List (D × D)
  | [] => []
  | a :: as => (a :: as).zip (as ++ [a])

private def tableNext {D : Type} [DecidableEq D] (pairs : List (D × D)) (a : D) :=
  (pairs.lookup a).getD a

/-- If a face contains the consecutive darts (a,b), the local rotation must
send rev(a) to b. Duplicate entries are handled by the independent exact-cover check. -/
def reconstruct (G : DartGraph) (fs : List (List G.Dart)) (a : G.Dart) :=
  tableNext (fs.flatMap turnPairs) (G.rev a)

def Accept (G : DartGraph) (fs : List (List G.Dart)) : Prop :=
  fs.flatten.Perm G.darts ∧ G.IsLocalRotation (G.reconstruct fs) ∧
    ∀ w ∈ fs, Follows (G.faceStep (G.reconstruct fs)) w

instance (G : DartGraph) (fs : List (List G.Dart)) : Decidable (G.Accept fs) := by
  unfold Accept; infer_instance

private theorem zip_map_graph {D : Type} (f : D → D) (w : List D) :
    w.zip (w.map f) = w.map (fun x => (x,f x)) := by
  induction w <;> simp [*]

theorem turnPairs_of_follows {D : Type} (f : D → D) (w : List D)
    (h : Follows f w) : turnPairs w = w.map (fun x => (x, f x)) := by
  cases w with
  | nil => exact False.elim h
  | cons a as =>
    change (a :: as).map f = as ++ [a] at h
    exact (congrArg (List.zip (a :: as)) h.symm).trans (zip_map_graph _ _)

private theorem table_of_follows {D : Type} (f : D → D) (fs : List (List D))
    (h : ∀ w ∈ fs, Follows f w) :
    fs.flatMap turnPairs = fs.flatten.map (fun x => (x, f x)) := by
  induction fs with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.flatten_cons, List.map_append]
    rw [turnPairs_of_follows f w (h _ (by simp)), ih (fun t ht => h t (by simp [ht]))]

private theorem lookup_graph {D : Type} [DecidableEq D] (f : D → D) (xs : List D)
    (a : D) (ha : a ∈ xs) : (xs.map (fun x => (x, f x))).lookup a = some (f a) := by
  induction xs with
  | nil => simp at ha
  | cons b bs ih =>
    by_cases h : a = b
    · subst b; simp
    · simp [List.lookup_cons, beq_eq_false_iff_ne.mpr h, ih (by simpa [h] using ha)]

theorem reconstruct_eq (G : DartGraph) (fs : List (List G.Dart)) (r : G.Dart → G.Dart)
    (hp : fs.flatten.Perm G.darts) (ht : ∀ w ∈ fs, Follows (G.faceStep r) w) :
    G.reconstruct fs = r := by
  funext a
  have hm : G.rev a ∈ fs.flatten := hp.mem_iff.mpr (List.mem_finRange _)
  unfold reconstruct tableNext
  rw [table_of_follows _ _ ht, lookup_graph _ _ _ hm]
  simp [faceStep, G.rev_involutive]

/-- Terminal acceptance is equivalent to genuine realizability as a rotation
system. In particular the lookup procedure cannot manufacture a spurious rotation. -/
theorem accept_iff (G : DartGraph) (fs : List (List G.Dart)) :
    G.Accept fs ↔ fs.flatten.Perm G.darts ∧
      ∃ r, G.IsLocalRotation r ∧ ∀ w ∈ fs, Follows (G.faceStep r) w := by
  constructor
  · rintro ⟨hp, hr, hf⟩; exact ⟨hp, G.reconstruct fs, hr, hf⟩
  · rintro ⟨hp, r, hr, hf⟩
    unfold Accept
    rw [G.reconstruct_eq fs r hp hf]
    exact ⟨hp, hr, hf⟩


theorem local_word (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    (v : Fin G.vertices) (hne : G.star v ≠ []) :
    ∃ w, w.Perm (G.star v) ∧ Follows r w := by
  have hv := hr v
  cases he : G.star v with
  | nil => exact False.elim (hne he)
  | cons a as =>
    rw [he] at hv
    exact ⟨_, hv⟩

@[simp] theorem mem_star (G : DartGraph) (v : Fin G.vertices) (a : G.Dart) :
    a ∈ G.star v ↔ G.tail a = v := by simp [star, darts]

private theorem follows_perm {D : Type} {w : List D} {f : D → D} (hw : Follows f w) :
    (w.map f).Perm w := by
  cases w with
  | nil => simp
  | cons a as =>
    change (a :: as).map f = as ++ [a] at hw
    rw [hw]; exact List.perm_append_comm (l₂ := [a])

theorem star_perm (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    (v : Fin G.vertices) : ((G.star v).map r).Perm (G.star v) := by
  by_cases he : G.star v = []
  · simp [he]
  · obtain ⟨w, hp, hf⟩ := G.local_word hr v he
    exact (hp.map r).symm.trans ((follows_perm hf).trans hp)

theorem preserves_tail (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    (a : G.Dart) : G.tail (r a) = G.tail a := by
  apply (G.mem_star _ _).mp
  exact (G.star_perm hr _).subset (List.mem_map.mpr ⟨a, (G.mem_star _ _).mpr rfl, rfl⟩)

theorem darts_nodup (G : DartGraph) : G.darts.Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp [darts]
  omega

private theorem perm_of_cover_length {D : Type} [DecidableEq D] (xs ys : List D)
    (hn : ys.Nodup) (hl : xs.length = ys.length) (hc : ∀ a ∈ ys, a ∈ xs) :
    xs.Perm ys := by
  induction ys generalizing xs with
  | nil => simp_all
  | cons b bs ih =>
    have h := List.nodup_cons.mp hn
    have hb := hc b (by simp)
    have hp := List.perm_cons_erase hb
    refine hp.trans ((ih (xs.erase b) h.2 ?_ ?_).cons b)
    · have := hp.length_eq
      simp only [List.length_cons] at *; omega
    · intro a ha
      have hne : a ≠ b := by intro hab; exact h.1 (hab ▸ ha)
      exact (List.mem_erase_of_ne hne).mpr (hc a (by simp [ha]))

theorem face_perm (G : DartGraph) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r) :
    (G.darts.map (G.faceStep r)).Perm G.darts := by
  apply perm_of_cover_length _ _ G.darts_nodup (by simp)
  intro a _
  have hm : a ∈ (G.star (G.tail a)).map r :=
    (G.star_perm hr _).mem_iff.mpr ((G.mem_star _ _).mpr rfl)
  obtain ⟨b, _, hb⟩ := List.mem_map.mp hm
  exact List.mem_map.mpr ⟨G.rev b, List.mem_finRange _, by simp [faceStep, G.rev_involutive, hb]⟩

private theorem map_table_zip {D : Type} [DecidableEq D] (xs ys : List D) (hn : xs.Nodup)
    (hl : xs.length = ys.length) : xs.map (tableNext (xs.zip ys)) = ys := by
  induction xs generalizing ys with
  | nil => simpa using hl.symm
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      have h := List.nodup_cons.mp hn
      have hrest := ih ys h.2 (by simpa using hl)
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1
      · simp [tableNext]
      · refine (List.map_congr_left ?_).trans hrest
        intro a ha
        have hne : a ≠ x := by intro e; exact h.1 (e ▸ ha)
        simp [tableNext, List.lookup_cons, beq_eq_false_iff_ne.mpr hne]

private theorem orbitWord_of_chain {D : Type} (r : D → D) (a last : D) (xs : List D)
    (h : (a :: xs).map r = xs ++ [last]) :
    orbitWord r a (xs.length+1) = a :: xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨hab, hbs⟩ := List.cons.inj h
    change a :: orbitWord r (r a) (bs.length+1) = _
    have hb : r a = b := hab
    rw [hb, ih b hbs]

/-- A cyclic word listing a vertex star is a witness for the executable orbit test. -/
theorem singleOn_of_follows {D : Type} {r : D → D} {a : D} {as : List D}
    (h : Follows r (a :: as)) : SingleOn r (a :: as) := by
  simp only [SingleOn]
  rw [orbitWord_of_chain r a a as h]
  exact ⟨.refl _, h⟩

private theorem follows_shift {D : Type} (r : D → D) (x : D) (xs : List D)
    (h : Follows r (x :: xs)) : Follows r (xs ++ [x]) := by
  cases xs with
  | nil => exact h
  | cons b bs =>
    obtain ⟨hxb, hbs⟩ := List.cons.inj h
    change ((b :: bs) ++ [x]).map r = (bs ++ [x]) ++ [b]
    rw [List.map_append, hbs]
    have hx : r x = b := hxb
    simp [hx]

theorem follows_rebase {D : Type} (r : D → D) (a : D) (pre post : List D)
    (h : Follows r (pre ++ a :: post)) : Follows r (a :: (post ++ pre)) := by
  induction pre generalizing post with
  | nil => simpa using h
  | cons b pre ih =>
    have h' := follows_shift r b (pre ++ a :: post) h
    have hu : Follows r (pre ++ a :: (post ++ [b])) := by simpa [List.append_assoc] using h'
    simpa [List.append_assoc] using ih (post ++ [b]) hu

/-- A local rotation is equivalently a single cyclic word on every nonempty
vertex star, with no restriction on the starting dart in that word. -/
theorem isLocalRotation_iff (G : DartGraph) (r : G.Dart → G.Dart) :
    G.IsLocalRotation r ↔ ∀ v, G.star v ≠ [] →
      ∃ w, w.Perm (G.star v) ∧ Follows r w := by
  refine ⟨fun hr => G.local_word hr, ?_⟩
  intro hw v
  cases he : G.star v with
  | nil => trivial
  | cons a as =>
    obtain ⟨w, hp, hf⟩ := hw v (by simp [he])
    rw [he] at hp
    have ha : a ∈ w := hp.mem_iff.mpr (by simp)
    obtain ⟨pre, post, hx, _⟩ := List.eq_append_cons_of_mem ha
    subst w
    have hcy := follows_rebase r a pre post hf
    have hl := hp.length_eq
    have hn : (post ++ pre).length = as.length := by simp at hl ⊢; omega
    simp only [SingleOn, ← hn, orbitWord_of_chain r a a (post ++ pre) hcy]
    exact ⟨(List.perm_append_comm (l₁ := a :: post) (l₂ := pre)).trans hp, hcy⟩

/-- Increasing dart labels give one explicit cyclic order at each vertex,
including a singleton at a leaf. This proves nonemptiness without assuming that
the graph has already been supplied with an embedding or rotation system. -/
def defaultRotation (G : DartGraph) (a : G.Dart) :=
  tableNext (turnPairs (G.star (G.tail a))) a

theorem default_isLocalRotation (G : DartGraph) : G.IsLocalRotation G.defaultRotation := by
  intro v
  cases he : G.star v with
  | nil => trivial
  | cons a as =>
    have hn : (a :: as).Nodup := by
      rw [← he]; exact G.darts_nodup.filter _
    have hmap : (a :: as).map G.defaultRotation = as ++ [a] := by
      have hz := map_table_zip (a :: as) (as ++ [a]) hn (by simp)
      refine (List.map_congr_left ?_).trans hz
      intro x hx
      have ht : G.tail x = v := (G.mem_star v x).mp (he ▸ hx)
      simp [defaultRotation, ht, he, turnPairs]
    exact singleOn_of_follows hmap

end DartGraph
end Page
