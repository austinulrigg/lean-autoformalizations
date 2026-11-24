import Page.Orbits

namespace Page

/-- On a closed word, membership is preserved by the successor. -/
theorem Follows.next_mem {D : Type} {f : D → D} {w : List D} {x : D}
    (hw : Follows f w) (hx : x ∈ w) : f x ∈ w := by
  cases w with
  | nil => contradiction
  | cons a w =>
    have hn := List.mem_map_of_mem (f := f) hx
    change List.map f (a :: w) = w ++ [a] at hw
    rw [hw] at hn
    simpa [or_comm] using hn

/-- For a successor path from `a` to `b`, an invariant holding anywhere in
the path holds at `b`; an invariant holding at `a` holds along the path. -/
private theorem pathInvariant {D : Type} {f : D → D} (p : D → Prop)
    (step : ∀ x, p x → p (f x)) (a b : D) (as : List D)
    (path : (a :: as).map f = as ++ [b]) :
    ((∃ x ∈ a :: as, p x) → p b) ∧ (p a → ∀ x ∈ a :: as, p x) := by
  induction as generalizing a with
  | nil =>
    simp at path
    subst b
    simpa using step a
  | cons c cs ih =>
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at path
    obtain ⟨first, more⟩ := path
    obtain ⟨reachEnd, reachAll⟩ := ih c more
    constructor
    · rintro ⟨x, hx, px⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact reachEnd ⟨c, by simp, first ▸ step x px⟩
      · exact reachEnd ⟨x, hx, px⟩
    · intro pa x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact pa
      · exact reachAll (first ▸ step a pa) x hx

/-- Two successor cycles with a common dart contain exactly the same darts. -/
theorem Follows.same_darts {D : Type} {f : D → D} {u v : List D} {x : D}
    (hu : Follows f u) (hv : Follows f v) (xu : x ∈ u) (xv : x ∈ v) : u ⊆ v := by
  cases u with
  | nil => simp
  | cons a as =>
    have p := pathInvariant (· ∈ v) (fun _ h => hv.next_mem h) a a as hu
    exact fun _ hx => p.2 (p.1 ⟨x, xu, xv⟩) _ hx

/-- Any two orbit decompositions of the same permutation on a duplicate-free
dart list have the same number of cycles. Their order and starting darts may differ. -/
theorem cycle_count_unique {D : Type} [DecidableEq D] (f : D → D)
    {fs gs : List (List D)} (nd : fs.flatten.Nodup) (hp : fs.flatten.Perm gs.flatten)
    (hf : ∀ w ∈ fs, Follows f w) (hg : ∀ w ∈ gs, Follows f w) :
    fs.length = gs.length := by
  induction fs generalizing gs with
  | nil =>
    cases gs with
    | nil => rfl
    | cons g gs =>
      have he : g ++ gs.flatten = [] := List.nil_perm.mp hp
      have eg := (List.append_eq_nil_iff.mp he).1
      have := hg g (by simp)
      subst g
      contradiction
  | cons w fs ih =>
    cases w with
    | nil => exact False.elim (hf [] (by simp))
    | cons x xs =>
      let w := x :: xs
      have hwf : w ∈ w :: fs := by simp
      have hxf : x ∈ (w :: fs).flatten := List.mem_flatten.mpr ⟨w, hwf, by simp [w]⟩
      obtain ⟨g, hgg, hxg⟩ := List.mem_flatten.mp (hp.subset hxf)
      let rest := gs.erase g
      have reorder : gs.Perm (g :: rest) := List.perm_cons_erase hgg
      have hfw := hf w hwf
      have hggf := hg g hgg
      have hww : w.Nodup := (List.sublist_flatten_of_mem hwf).nodup nd
      have hng : g.Nodup := (List.sublist_flatten_of_mem hgg).nodup (hp.nodup nd)
      have same : w.Perm g := by
        apply List.perm_iff_count.mpr
        intro y
        have memEquiv : y ∈ w ↔ y ∈ g :=
          ⟨fun hy => hfw.same_darts hggf (by simp [w] : x ∈ w) hxg hy,
           fun hy => hggf.same_darts hfw hxg (by simp [w] : x ∈ w) hy⟩
        simp only [hww.count, hng.count, memEquiv]
      have hrest : fs.flatten.Perm rest.flatten := by
        apply (List.perm_append_left_iff g).mp
        exact ((same.symm.append_right _).trans hp).trans reorder.flatten
      have hrf : fs.flatten.Nodup := (List.nodup_append.mp nd).2.1
      have hrg : ∀ z ∈ rest, Follows f z := fun z hz => hg z (reorder.symm.subset (by simp [hz]))
      have eqrest := ih hrf hrest (fun z hz => hf z (by simp [hz])) hrg
      have eql := reorder.length_eq
      simpa [eqrest] using eql.symm

end Page
