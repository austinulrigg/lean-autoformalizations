import Pisanski.Basic

/-! Arithmetic of the cyclic ordering in equation (9). The indices are
positions in the B rotation. For d = 4k, positions 2k apart have
complementary labels. -/
namespace Pisanski.Cyclic

/-- The connection labels in the order used by the B rotation. -/
def label {k : Nat} (i : Fin (4*k)) : Nat :=
  if i.val < 2*k then i.val else 6*k-1-i.val

theorem label_lt {k : Nat} (i : Fin (4*k)) : label i < 4*k := by
  have hi := i.isLt
  unfold label
  split <;> omega

theorem label_injective {k : Nat} {i j : Fin (4*k)} (h : label i = label j) : i = j := by
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  unfold label at h
  split at h <;> split at h <;> omega

/-- Move halfway around the B cycle. -/
def opposite {k : Nat} (i : Fin (4*k)) : Fin (4*k) :=
  ⟨if i.val < 2*k then i.val+2*k else i.val-2*k, by
    have hi := i.isLt
    split <;> omega⟩

@[simp] theorem opposite_twice {k : Nat} (i : Fin (4*k)) : opposite (opposite i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [opposite]
  split <;> (split <;> omega)

theorem label_add_opposite {k : Nat} (i : Fin (4*k)) :
    label i + label (opposite i) = 4*k-1 := by
  have hi := i.isLt
  simp only [label, opposite]
  split <;> (split <;> omega)

private theorem val_next {d : Nat} (i : Fin d) :
    (next i).val = (if i.val + 1 < d then i.val + 1 else 0) := by
  unfold next
  split <;> simp_all

theorem next_ne_opposite {k : Nat} (i : Fin (4*k)) : next i ≠ opposite i := by
  intro h
  have hi := i.isLt
  have he := congrArg Fin.val h
  simp only [val_next, opposite] at he
  split at he <;> split at he <;> omega

theorem next_opposite {k : Nat} (i : Fin (4*k)) : next (opposite i) = opposite (next i) := by
  apply Fin.ext
  have hi := i.isLt
  simp only [val_next, opposite]
  repeat' first | omega | split

/-- The A position of a B position. This is multiplication by `2k-1`
modulo `4k`, written by parity to avoid a coprimality dependency. Since
`(2k-1)^2 ≡ 1 mod 4k`, the same map converts in the other direction. -/
def convert {k : Nat} (i : Fin (4*k)) : Fin (4*k) :=
  ⟨if i.val%2 = 0 then (if i.val=0 then 0 else 4*k-i.val)
   else if i.val < 2*k then 2*k-i.val else 6*k-i.val, by
    have hi := i.isLt
    split <;> split <;> omega⟩

@[simp] theorem convert_twice {k : Nat} (i : Fin (4*k)) : convert (convert i) = i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [convert]
  repeat' first | omega | split

/-- Passing one B corner and one A corner advances half a B cycle. -/
theorem two_corners {k : Nat} (i : Fin (4*k)) :
    convert (next (convert (next i))) = opposite i := by
  apply Fin.ext
  have hi := i.isLt
  simp only [convert, val_next, opposite]
  repeat' first | omega | split

end Pisanski.Cyclic
