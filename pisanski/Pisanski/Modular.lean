import Std

/-! Bounded-coordinate arithmetic shared by the cyclic and dihedral constructions. -/
namespace Pisanski.Modular

/-- Addition of circular coordinates. Inputs are already in the fundamental interval,
so the sum crosses its right endpoint at most once. -/
def up {m : Nat} (x y : Fin m) : Fin m :=
  ⟨if x.val + y.val < m then x.val + y.val else x.val + y.val - m,
   by split <;> omega⟩

/-- Subtraction of circular coordinates. -/
def down {m : Nat} (x y : Fin m) : Fin m :=
  ⟨if y.val ≤ x.val then x.val - y.val else x.val + m - y.val,
   by split <;> omega⟩

theorem up_down {m : Nat} (x a : Fin m) : up (down x a) a = x := by
  apply Fin.ext
  simp only [up, down]
  (repeat' split) <;> omega

theorem down_up {m : Nat} (x a : Fin m) : down (up x a) a = x := by
  apply Fin.ext
  simp only [up, down]
  (repeat' split) <;> omega

end Pisanski.Modular
