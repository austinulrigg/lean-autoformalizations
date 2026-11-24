import Pisanski.Basic
import Pisanski.Modular

namespace Pisanski
namespace Dihedral

open Modular

private theorem reflect_twice {m : Nat} (x a : Fin m) : down a (down a x) = x := by
  apply Fin.ext
  simp only [down]
  (repeat' split) <;> omega

/-- The dihedral right action in coordinates on a regular orbit. The rotation
label 2a acts by subtracting 2a; the reflection label 2a+1 acts by
x ↦ 2a+1−x. These are the left actions of the inverses of r^a and r^a t,
respectively, after sending each group element to its inverse. -/
private def step {n : Nat} (x a : Fin (2*n)) : Fin (2*n) :=
  if a.val % 2 = 0 then down x a else down a x

private def unstep {n : Nat} (x a : Fin (2*n)) : Fin (2*n) :=
  if a.val % 2 = 0 then up x a else down a x

private theorem unstep_step {n : Nat} (x a : Fin (2*n)) : unstep (step x a) a = x := by
  by_cases ha : a.val % 2 = 0
  · simpa [unstep, step, ha] using up_down x a
  · simpa [unstep, step, ha] using reflect_twice x a

private theorem step_unstep {n : Nat} (x a : Fin (2*n)) : step (unstep x a) a = x := by
  by_cases ha : a.val % 2 = 0
  · simpa [unstep, step, ha] using down_up x a
  · simpa [unstep, step, ha] using reflect_twice x a

private theorem step_injective {n : Nat} (x a b : Fin (2*n))
    (h : step x a = step x b) : a = b := by
  have he := congrArg Fin.val h
  apply Fin.ext
  by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val % 2 = 0 <;>
    simp only [step, ha, hb, if_true, if_false, down] at he <;>
    (repeat' split at he) <;> omega

private theorem mixed_diamond {n : Nat} (x a b : Fin (2*n))
    (h : a.val % 2 ≠ b.val % 2) :
    step (unstep (step x a) b) a = step x b := by
  by_cases ha : a.val % 2 = 0
  · have hb : b.val % 2 ≠ 0 := by omega
    apply Fin.ext
    simp only [step, unstep, ha, hb, if_true, if_false, up, down]
    (repeat' split) <;> omega
  · have hb : b.val % 2 = 0 := by omega
    apply Fin.ext
    simp only [step, unstep, ha, hb, if_true, if_false, up, down]
    (repeat' split) <;> omega

private theorem half_diamond {n : Nat} (x a b : Fin (2*n))
    (ha : a.val = 0) (hb : b.val = n) (hn : n % 2 = 0) :
    step (unstep (step x a) b) a = step x b := by
  apply Fin.ext
  simp only [step, unstep, ha, hb, hn, Nat.zero_mod, if_true, up, down]
  (repeat' split) <;> omega

/-- Labels of one dihedral construction, in cyclic order around the B side.
The matching labels 0,1,2 are the identity, reflection t, and rotation r.
All transitions change parity, except optionally the half-turn 0 → n. -/
private structure Data (n d : Nat) where
  label : Fin d → Fin (2*n)
  injective : ∀ i j, label i = label j → i = j
  zero : ∃ i, (label i).val = 0
  one : ∃ i, (label i).val = 1
  two : ∃ i, (label i).val = 2
  neighbors : ∀ i, (label i).val % 2 ≠ (label (next i)).val % 2 ∨
    ((label i).val = 0 ∧ (label (next i)).val = n ∧ n % 2 = 0)

private def table {n d : Nat} (C : Data n d) : Table (Fin (2*n)) d where
  go x i := step x (C.label i)
  back y i := unstep y (C.label i)
  rotA := prev
  rotB := next

private theorem zero_step {n : Nat} (x a : Fin (2*n)) (ha : a.val = 0) :
    step x a = x := by
  apply Fin.ext
  simp [step, ha, down]

/-- From the identity coordinate one reaches 1 using t. One can then
advance by 2 via the inverse rotation edge, in either parity class. -/
private theorem connected {n d : Nat} (C : Data n d) (hn : 2 ≤ n) :
    ∀ x y, Reach (table C).Across x y := by
  obtain ⟨i0, h0⟩ := C.zero
  obtain ⟨i1, h1⟩ := C.one
  obtain ⟨i2, h2⟩ := C.two
  let origin : Fin (2*n) := ⟨0, by omega⟩
  have fromZero : ∀ y, Reach (table C).Across origin y := by
    intro y
    obtain ⟨v,hv⟩ := y
    induction v using Nat.strongRecOn with
    | ind v ih =>
      by_cases hzero : v = 0
      · subst v
        exact Reach.refl _
      by_cases hone : v = 1
      · subst v
        apply Reach.tail (Reach.refl origin)
        refine ⟨i1,i0,?_⟩
        change step origin (C.label i1) = step _ (C.label i0)
        rw [zero_step _ _ h0]
        apply Fin.ext
        simp [step, h1, origin, down]
      · have hsmall : v - 2 < v := by omega
        have hold : v - 2 < 2*n := by omega
        apply Reach.tail (ih (v-2) hsmall hold)
        refine ⟨i0,i2,?_⟩
        change step _ (C.label i0) = step _ (C.label i2)
        rw [zero_step _ _ h0]
        apply Fin.ext
        simp [step, h2, down, show 2 ≤ v by omega]
  intro x y
  have rev {u v : Fin (2*n)} (h : (table C).Across u v) : (table C).Across v u := by
    obtain ⟨i,j,he⟩ := h
    exact ⟨j,i,he.symm⟩
  exact Reach.trans (Reach.symm_of rev (fromZero x)) (fromZero y)

private theorem build {n d : Nat} (C : Data n d) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    HasTable (2*n) d := by
  refine ⟨Fin (2*n), Numbering.fin _, table C, ?_⟩
  apply Table.valid_of_diamond (table C) hd rfl rfl
  · exact fun x i => unstep_step x (C.label i)
  · exact fun x i => step_unstep x (C.label i)
  · exact fun x i j h => C.injective i j (step_injective _ _ _ h)
  · exact connected C hn
  · intro x i
    rcases C.neighbors i with h | ⟨ha,hb,hn'⟩
    · exact mixed_diamond _ _ _ h
    · exact half_diamond _ _ _ ha hb hn'

private def evenData {n k : Nat} (hk : 2 ≤ k) (hkn : k ≤ n) :
    Data n (2*k) where
  label i := ⟨i.val, by omega⟩
  injective i j h := Fin.ext (congrArg (fun a : Fin (2*n) => a.val) h)
  zero := ⟨⟨0, by omega⟩, rfl⟩
  one := ⟨⟨1, by omega⟩, rfl⟩
  two := ⟨⟨2, by omega⟩, rfl⟩
  neighbors i := by
    left
    simp only [next]
    split <;> dsimp <;> omega

/-- In the odd list we insert the half-turn n immediately after 0.
The even rotation labels otherwise increase, skipping n.
The reflection labels are precisely 1,3,5,... . -/
private def oddLabel (n j : Nat) : Nat :=
  if j = 0 then 0 else if j = 1 then n else
    if j % 2 = 0 then j-1 else if j-1 < n then j-1 else j+1

private theorem oddLabel_parity {n j : Nat} (hj : 2 ≤ j) :
    oddLabel n j % 2 = (j+1) % 2 := by
  simp only [oddLabel, if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega)]
  (repeat' split) <;> omega

private def oddData {n k : Nat} (hk : 2 ≤ k) (hkn : k < n) (hn : 2 ∣ n) :
    Data n (2*k+1) where
  label i := ⟨oddLabel n i.val, by
    simp only [oddLabel]
    (repeat' split) <;> omega⟩
  injective i j h := by
    have he : oddLabel n i.val = oddLabel n j.val := congrArg Fin.val h
    apply Fin.ext
    obtain ⟨s,hs⟩ := hn
    simp only [oddLabel] at he
    (repeat' split at he) <;> omega
  zero := ⟨⟨0, by omega⟩, by simp [oddLabel]⟩
  one := ⟨⟨2, by omega⟩, by simp [oddLabel]⟩
  two := ⟨⟨3, by omega⟩, by simp [oddLabel, show 2 < n by omega]⟩
  neighbors i := by
    obtain ⟨s,hs⟩ := hn
    have hn' : n % 2 = 0 := by omega
    change oddLabel n i.val % 2 ≠ oddLabel n (next i).val % 2 ∨
      oddLabel n i.val = 0 ∧ oddLabel n (next i).val = n ∧ n % 2 = 0
    by_cases h0 : i.val = 0
    · right
      have hi : (next i).val = 1 := by simp [next, h0, show 0+1 < 2*k+1 by omega]
      simp [h0, hi, oddLabel, hn']
    left
    by_cases h1 : i.val = 1
    · have hi : (next i).val = 2 := by simp [next, h1, show 1+1 < 2*k+1 by omega]
      simp [hi,h1,oddLabel,hn']
    have hl : 2 ≤ i.val := by omega
    rw [oddLabel_parity hl]
    by_cases hlast : i.val+1 < 2*k+1
    · have hi : (next i).val = i.val+1 := by simp [next,hlast]
      rw [hi,oddLabel_parity (by omega : 2 ≤ i.val+1)]
      omega
    · have hi : (next i).val = 0 := by simp [next,hlast]
      rw [hi]
      simp only [oddLabel, if_true, Nat.zero_mod]
      omega

end Dihedral

/-- Proposition 4.2. The explicitly alternating dihedral list gives both
even parameters. -/
theorem dihedralEven {n k : Nat} (hk : 2 ≤ k) (hkn : k ≤ n) :
    HasTable (2*n) (2*k) :=
  Dihedral.build (Dihedral.evenData hk hkn) (by omega) (by omega)

/-- Proposition 4.3. A single half-turn transition makes an odd degree
possible when the size of a part is divisible by four. -/
theorem dihedralOdd {n k : Nat} (hk : 2 ≤ k) (hkn : k < n) (hn : 2 ∣ n) :
    HasTable (2*n) (2*k+1) :=
  Dihedral.build (Dihedral.oddData hk hkn hn) (by omega) (by omega)

end Pisanski
