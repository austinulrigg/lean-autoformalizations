import Pisanski.Basic
import Pisanski.CyclicArithmetic
import Pisanski.Modular

/-! The cyclic construction (Proposition 5.1). Labels are positions in the
B rotation; `label` gives the corresponding element of the cyclic group. -/
namespace Pisanski.Cyclic

open Modular

private theorem up_inj {m : Nat} (x a b : Fin m) (he : up x a = up x b) : a = b := by
  apply Fin.ext
  have := x.isLt; have := a.isLt; have := b.isLt
  have he' := congrArg Fin.val he
  simp only [up] at he'
  split at he' <;> split at he' <;> omega

/-- Four successive signed increments cancel when their opposite sums agree. -/
private theorem four_increments {m : Nat} (x a b c e : Fin m)
    (hsum : a.val+c.val = b.val+e.val) : down (up (down (up x a) b) c) e = x := by
  apply Fin.ext
  have := x.isLt; have := a.isLt; have := b.isLt; have := c.isLt; have := e.isLt
  simp only [down, up]
  repeat' first | omega | split

private def offset {m k : Nat} (hm : 4*k ≤ m) (i : Fin (4*k)) : Fin m :=
  ⟨label i, Nat.lt_of_lt_of_le (label_lt i) hm⟩

private def certificate {m k : Nat} (hm : 4*k ≤ m) : Table (Fin m) (4*k) where
  go x i := up x (offset hm i)
  back x i := down x (offset hm i)
  rotB := next
  rotA i := convert (next (convert i))

private theorem twoI_eq {m k : Nat} (hm : 4*k ≤ m) (i : Fin (4*k)) :
    (certificate hm).twoI i = opposite i := two_corners i

private theorem connected {m k : Nat} (hk : 0 < k) (hm : 4*k ≤ m) :
    ∀ x y, Reach (certificate hm).Across x y := by
  let zero : Fin m := ⟨0, by omega⟩
  let a : Fin (4*k) := ⟨1, by omega⟩
  let b : Fin (4*k) := ⟨0, by omega⟩
  have consecutive (n : Nat) (hn : n+1<m) :
      (certificate hm).Across ⟨n, by omega⟩ ⟨n+1, hn⟩ := by
    refine ⟨a,b,Fin.ext ?_⟩
    change (if n+label a < m then n+label a else n+label a-m) =
      (if n+1+label b < m then n+1+label b else n+1+label b-m)
    have ha : label a = 1 := by simp [label,a,show 1 < 2*k by omega]
    have hb : label b = 0 := by simp [label,b,show 0 < 2*k by omega]
    simp [ha,hb,hn]
  have fromZero (x : Fin m) : Reach (certificate hm).Across zero x := by
    obtain ⟨n, hn⟩ := x
    induction n with
    | zero => exact .refl _
    | succ n ih => exact .tail (ih (by omega)) (consecutive n hn)
  intro x y
  have symmAcross : ∀ {x y : Fin m}, (certificate hm).Across x y → (certificate hm).Across y x := by
    rintro _ _ ⟨i,j,h⟩
    exact ⟨j,i,h.symm⟩
  exact (Reach.symm_of symmAcross (fromZero x)).trans (fromZero y)

private theorem certificate_valid {m k : Nat} (hk : 0 < k) (hm : 4*k ≤ m) :
    (certificate hm).Valid := by
  have pointInj (x : Fin m) (i j : Fin (4*k)) :
      (certificate hm).go x i = (certificate hm).go x j → i=j := by
    intro h
    exact label_injective (congrArg Fin.val (up_inj x _ _ h))
  refine ⟨fun x i => down_up _ _, fun y i => up_down _ _, pointInj, ?_, ?_, connected hk hm, ?_, ?_, ?_, ?_⟩
  · refine ⟨convert, ?_, ?_, ?_⟩
    · intro i j h; simpa using congrArg convert h
    · intro j; exact ⟨convert j, convert_twice j⟩
    · intro i
      change convert (next (convert (convert i))) = convert (next i)
      rw [convert_twice]
  · exact next_singleCycle
  · intro x i
    rw [twoI_eq]
    change down (up (down (up x (offset hm i)) (offset hm (next i)))
      (offset hm (opposite i))) (offset hm (next (opposite i))) = x
    rw [next_opposite]
    exact four_increments _ _ _ _ _ ((label_add_opposite i).trans (label_add_opposite (next i)).symm)
  · intro i
    rw [twoI_eq, twoI_eq, opposite_twice]
  · intro x i h
    have h' := congrArg (fun y => (certificate hm).go y (next i)) h
    change up (down (up x (offset hm i)) (offset hm (next i))) (offset hm (next i)) =
           up x (offset hm (next i)) at h'
    rw [up_down] at h'
    exact next_ne (by omega) i (pointInj x _ _ h').symm
  · intro x i h
    let y := (certificate hm).twoV x i
    have h' : (certificate hm).go y (opposite i) = (certificate hm).go x i := by
      rwa [twoI_eq] at h
    have h'' : (certificate hm).go y (next i) = (certificate hm).go x i := up_down _ _
    exact next_ne_opposite i (pointInj y _ _ (h''.trans h'.symm))

end Pisanski.Cyclic

namespace Pisanski

/-- Proposition 5.1, for every class size m and degree divisible by four. -/
theorem cyclicCase {m d : Nat} (hd : 4 ≤ d) (hdm : d ≤ m) (hdiv : 4 ∣ d) : HasTable m d := by
  obtain ⟨k, rfl⟩ := hdiv
  exact ⟨Fin m, Numbering.fin m, Cyclic.certificate hdm, Cyclic.certificate_valid (by omega) hdm⟩

end Pisanski
