import Std

namespace Pisanski

/-- Move once around the standard cyclic order on the finite ordinal. -/
def next {d : Nat} (i : Fin d) : Fin d :=
  if h : i.val + 1 < d then ⟨i.val + 1, h⟩ else ⟨0, by omega⟩

def prev {d : Nat} (i : Fin d) : Fin d :=
  if h : i.val = 0 then ⟨d - 1, by omega⟩ else ⟨i.val - 1, by omega⟩

/-- A cyclic listing of all labels, with no repetitions. -/
def SingleCycle {d : Nat} (r : Fin d → Fin d) : Prop :=
  ∃ e : Fin d → Fin d, (∀ i j, e i = e j → i = j) ∧
    (∀ j, ∃ i, e i = j) ∧ ∀ i, r (e i) = e (next i)

/-- A numbering gives the exact size of each vertex class. -/
structure Numbering (V : Type) (m : Nat) where
  encode : V → Fin m
  decode : Fin m → V
  left_inv : ∀ x, decode (encode x) = x
  right_inv : ∀ i, encode (decode i) = i

/-- Finite walks in a relation, including the length-zero walk. -/
inductive Reach {V : Type} (R : V → V → Prop) : V → V → Prop where
  | refl (v) : Reach R v v
  | tail {x y z} : Reach R x y → R y z → Reach R x z

/-- Edges of label i are a perfect matching between two copies of V. -/
structure Table (V : Type) (d : Nat) where
  go : V → Fin d → V
  back : V → Fin d → V
  rotA : Fin d → Fin d
  rotB : Fin d → Fin d

namespace Table
variable {V : Type} {d : Nat} (T : Table V d)

/-- The A-vertex and label after two facial steps from an A-dart. -/
def twoV (x : V) (i : Fin d) : V := T.back (T.go x i) (T.rotB i)
def twoI (i : Fin d) : Fin d := T.rotA (T.rotB i)

/-- Two A-vertices joined by a two-edge walk through the other part. -/
def Across (x y : V) : Prop := ∃ i j, T.go x i = T.go y j

/-- Algebraic checks for the rotation certificate, stated at every A-dart. -/
structure Valid : Prop where
  back_go : ∀ x i, T.back (T.go x i) i = x
  go_back : ∀ y i, T.go (T.back y i) i = y
  go_inj : ∀ x i j, T.go x i = T.go x j → i = j
  cycleA : SingleCycle T.rotA
  cycleB : SingleCycle T.rotB
  connected : ∀ x y, Reach T.Across x y
  fourV : ∀ x i, T.twoV (T.twoV x i) (T.twoI i) = x
  fourI : ∀ i, T.twoI (T.twoI i) = i
  distinctA : ∀ x i, T.twoV x i ≠ x
  distinctB : ∀ x i, T.go (T.twoV x i) (T.twoI i) ≠ T.go x i
end Table

/-- A uniform finite construction before passage to graph-theoretic language. -/
def HasTable (m d : Nat) : Prop :=
  ∃ (V : Type) (_ : Numbering V m) (T : Table V d), T.Valid

end Pisanski

namespace Pisanski

def Numbering.fin (n : Nat) : Numbering (Fin n) n :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

namespace Reach
variable {V : Type} {R : V → V → Prop} {x y z : V}

theorem single (h : R x y) : Reach R x y := .tail (.refl x) h

theorem trans (h : Reach R x y) (k : Reach R y z) : Reach R x z := by
  induction k with
  | refl => exact h
  | tail _ step ih => exact .tail ih step

theorem symm_of (sym : ∀ {a b}, R a b → R b a) (h : Reach R x y) : Reach R y x := by
  induction h with
  | refl => exact .refl _
  | tail _ step ih => exact (single (sym step)).trans ih
end Reach

@[simp] theorem next_prev {d : Nat} (i : Fin d) : next (prev i) = i := by
  apply Fin.ext
  obtain ⟨j, hj⟩ := i
  by_cases hz : j = 0
  · subst j
    simp [prev, next, show ¬ d - 1 + 1 < d by omega]
  · simp [prev, next, hz, show j - 1 + 1 < d by omega]
    omega

@[simp] theorem prev_next {d : Nat} (i : Fin d) : prev (next i) = i := by
  apply Fin.ext
  obtain ⟨j, hj⟩ := i
  by_cases hs : j + 1 < d
  · simp [next, prev, hs]
  · simp [next, prev, hs]
    omega

theorem next_ne {d : Nat} (hd : 2 ≤ d) (i : Fin d) : next i ≠ i := by
  intro h
  have := congrArg Fin.val h
  simp only [next] at this
  split at this <;> simp_all <;> omega

theorem next_singleCycle {d : Nat} : SingleCycle (@next d) := by
  exact ⟨id, fun _ _ h => h, fun j => ⟨j, rfl⟩, fun _ => rfl⟩

theorem prev_singleCycle {d : Nat} : SingleCycle (@prev d) := by
  let rev : Fin d → Fin d := fun i => ⟨d - 1 - i.val, by omega⟩
  have invol (i : Fin d) : rev (rev i) = i := by
    apply Fin.ext
    dsimp [rev]
    omega
  refine ⟨rev, ?_, fun j => ⟨rev j, invol j⟩, ?_⟩
  · intro i j h
    simpa only [invol] using congrArg rev h
  · intro i
    apply Fin.ext
    dsimp [rev, next, prev]
    split <;> split <;> simp_all <;> omega

namespace Table

/-- The square calculation common to both dihedral constructions (Lemma 3.2).
The displayed equality closes the quadrilateral through the two consecutive labels. -/
theorem valid_of_diamond {V : Type} {d : Nat} (T : Table V d) (hd : 2 ≤ d)
    (ha : T.rotA = prev) (hb : T.rotB = next)
    (hback : ∀ x i, T.back (T.go x i) i = x)
    (hgo : ∀ y i, T.go (T.back y i) i = y)
    (hinj : ∀ x i j, T.go x i = T.go x j → i = j)
    (hc : ∀ x y, Reach T.Across x y)
    (hsq : ∀ x i, T.go (T.back (T.go x i) (next i)) i = T.go x (next i)) :
    T.Valid := by
  have ti (i : Fin d) : T.twoI i = i := by simp [twoI, ha, hb]
  have square (x : V) (i : Fin d) : T.go (T.twoV x i) i = T.go x (next i) := by
    simpa only [twoV, hb] using hsq x i
  refine ⟨hback, hgo, hinj, ha ▸ prev_singleCycle, hb ▸ next_singleCycle, hc, ?_, ?_, ?_, ?_⟩
  · intro x i
    rw [ti, twoV, hb, square, hback]
  · intro i
    rw [ti, ti]
  · intro x i he
    have h := square x i
    rw [he] at h
    exact (next_ne hd i) (hinj x _ _ h).symm
  · intro x i
    rw [ti, square]
    exact fun h => (next_ne hd i) (hinj x _ _ h)
end Table
end Pisanski
