import Std

namespace Page

/-- A nonempty cyclic word whose successive symbols, including the last-to-first
transition, are obtained by applying `f`. -/
def Follows {D : Type} (f : D → D) : List D → Prop
  | [] => False
  | a :: as => (a :: as).map f = as ++ [a]

instance {D : Type} [DecidableEq D] (f : D → D) (w : List D) : Decidable (Follows f w) := by
  cases w <;> unfold Follows <;> infer_instance

private theorem traceCycle {D : Type} [DecidableEq D] (f : D → D) (a x : D)
    (rem : List D) (balance : (x :: rem.map f).Perm (a :: rem)) :
    ∃ middle rest : List D, (middle ++ rest).Perm rem ∧
      x :: middle.map f = middle ++ [a] ∧ (rest.map f).Perm rest := by
  by_cases h : x = a
  · subst x
    exact ⟨[], rem, .refl _, rfl, balance.cons_inv⟩
  · have hx : x ∈ rem := by
      have hm := balance.subset (List.mem_cons_self (a := x) (l := rem.map f))
      simpa [h] using hm
    have reorder := List.perm_cons_erase hx
    have shorter := reorder.length_eq
    simp only [List.length_cons] at shorter
    have nextBalance : (f x :: (rem.erase x).map f).Perm (a :: rem.erase x) := by
      apply List.Perm.cons_inv (a := x)
      exact (((reorder.map f).symm.cons x).trans balance).trans
        ((reorder.cons a).trans (List.Perm.swap x a _))
    obtain ⟨middle, rest, hperm, hword, hrest⟩ :=
      traceCycle f a (f x) (rem.erase x) nextBalance
    exact ⟨x :: middle, rest, (hperm.cons x).trans reorder.symm,
      congrArg (x :: ·) hword, hrest⟩
termination_by rem.length
decreasing_by all_goals try simp only [List.length_cons] at *
              all_goals omega

/-- A finite permutation decomposes into disjoint orbits when its dart list is
duplicate-free. The multiset decomposition itself does not need that restriction. -/
theorem exists_cycle_partition {D : Type} [DecidableEq D] (f : D → D) (ds : List D)
    (h : (ds.map f).Perm ds) :
    ∃ fs : List (List D), fs.flatten.Perm ds ∧ ∀ w ∈ fs, Follows f w := by
  cases eqds : ds with
  | nil => exact ⟨[], .refl _, by simp⟩
  | cons a rem =>
    obtain ⟨middle, rest, hsplit, hword, hrest⟩ := traceCycle f a (f a) rem (by simpa [eqds] using h)
    obtain ⟨fs, hfs, hw⟩ := exists_cycle_partition f rest hrest
    refine ⟨(a :: middle) :: fs, ((hfs.append_left middle).trans hsplit).cons a, ?_⟩
    intro w hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hword
    · exact hw w hm
termination_by ds.length
decreasing_by
  rw [eqds, List.length_cons]
  have lengthSum := hsplit.length_eq
  simp only [List.length_append] at lengthSum
  omega

end Page
