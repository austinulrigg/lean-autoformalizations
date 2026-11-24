import Pisanski.Cyclic
import Pisanski.Dihedral
import Pisanski.Graph
import Pisanski.Haar

/-!
# Pisanski's conjecture: the combinatorial construction
For every admissible pair there is a connected simple regular bipartite graph
with rotations whose facial walks are simple quadrilaterals. The classical
rotation principle interprets this certificate on a closed orientable surface.
-/

namespace Pisanski

/-- The three constructions cover every admissible pair (paper, §6). -/
theorem table_of_admissible {m d : Nat} (hd : 4 ≤ d) (hdm : d ≤ m)
    (hadm : 4 ∣ m * d) : HasTable m d := by
  by_cases h4d : 4 ∣ d
  · exact cyclicCase hd hdm h4d
  · have hmod : (m % 4 * (d % 4)) % 4 = 0 := by
      rw [← Nat.mul_mod]
      exact Nat.mod_eq_zero_of_dvd hadm
    have hm : 2 ∣ m := by
      have hd' : d % 4 ≠ 0 := fun h => h4d (Nat.dvd_of_mod_eq_zero h)
      have hmc : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
      have hdc : d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
      rcases hmc with h|h|h|h <;> rcases hdc with k|k|k <;>
        simp [h, k] at hmod <;> omega
    by_cases he : 2 ∣ d
    · obtain ⟨n, rfl⟩ := hm
      obtain ⟨k, rfl⟩ := he
      exact dihedralEven (n := n) (k := k) (by omega) (by omega)
    · have hf : 4 ∣ m := by
        have hmc : m % 4 = 0 ∨ m % 4 = 2 := by omega
        have hdc : d % 4 = 1 ∨ d % 4 = 3 := by omega
        rcases hmc with h|h
        · exact Nat.dvd_of_mod_eq_zero h
        · rcases hdc with k|k <;> simp [h, k] at hmod
      obtain ⟨n, rfl⟩ := hm
      let k := d / 2
      have hdk : d = 2*k+1 := by dsimp [k]; omega
      rw [hdk]
      exact dihedralOdd (n := n) (k := k) (by omega) (by omega) (by omega)

/-- Constructive direction of Theorem 1.1, in the language of rotation systems. -/
theorem pisanski {m d : Nat} (hd : 4 ≤ d) (hdm : d ≤ m) (hadm : 4 ∣ m * d) :
    HasQuadrangulation m d :=
  hasQuadrangulation_of_hasTable (by omega) (table_of_admissible hd hdm hadm)

end Pisanski
