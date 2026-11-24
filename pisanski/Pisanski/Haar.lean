import Pisanski.Graph

/-! # The Haar-graph face calculation (Lemma 3.2)

The graph uses the two copies of a group `Γ` and the edges `A(g)—B(g*sᵢ)`.
The group laws are given explicitly so the file depends only on Lean's standard
library. Finiteness of `Γ` is unnecessary for the four-step calculation.
-/

namespace Pisanski

/-- Ordinary group laws for the given product, unit and inverse. -/
structure GroupLaws (Γ : Type) [Mul Γ] [OfNat Γ 1] [Inv Γ] : Prop where
  assoc : ∀ a b c : Γ, (a * b) * c = a * (b * c)
  one_mul : ∀ a : Γ, 1 * a = a
  mul_one : ∀ a : Γ, a * 1 = a
  inv_mul : ∀ a : Γ, a⁻¹ * a = 1
  mul_inv : ∀ a : Γ, a * a⁻¹ = 1

variable {Γ : Type} [Mul Γ] [OfNat Γ 1] [Inv Γ] {d : Nat}

/-- The `B`-rotation follows the listed labels; the `A`-rotation goes in reverse. -/
def haarTable (s : Fin d → Γ) : Table Γ d where
  go g i := g * s i
  back g i := g * (s i)⁻¹
  rotA := prev
  rotB := next

/-- Connectedness here refers to walks in the ordinary graph.
Projecting a walk to the A side pairs its edges into two-edge moves. -/
private theorem across_of_graph_connected {X : Type} (T : Table X d) (k : Fin d)
    (hgo : ∀ y i, T.go (T.back y i) i = y)
    (connected : ∀ v w, Reach T.toGraph.Adj v w) (x y : X) : Reach T.Across x y := by
  let project : Sum X X → X := fun v =>
    match v with | .inl a => a | .inr b => T.back b k
  have edge {v w : Sum X X} (h : T.toGraph.Adj v w) : T.Across (project v) (project w) := by
    obtain ⟨i, rfl⟩ := h
    cases v with
    | inl a => exact ⟨i, k, (hgo (T.go a i) k).symm⟩
    | inr b => exact ⟨k, i, (hgo b k).trans (hgo b i).symm⟩
  have map_walk {v w : Sum X X} (p : Reach T.toGraph.Adj v w) :
      Reach T.Across (project v) (project w) := by
    induction p with
    | refl => exact .refl _
    | tail _ e ih => exact .tail ih (edge e)
  exact map_walk (connected (.inl x) (.inl y))

/-- A connected graph on both copies of an inhabited type has an edge label. -/
private theorem positive_degree {X : Type} (x : X) (T : Table X d)
    (connected : ∀ v w, Reach T.toGraph.Adj v w) : 0 < d := by
  by_cases hd : 0 < d
  · exact hd
  · have equal {v w} (p : Reach T.toGraph.Adj v w) : v = w := by
      induction p with
      | refl => rfl
      | tail _ edge _ => obtain ⟨i, _⟩ := edge; have := i.isLt; omega
    cases equal (connected (.inl x) (.inr x))

/-- Lemma 3.2. For a connected Haar graph, an injective cyclic listing whose
successive products `sᵢ * (sᵢ₊₁)⁻¹` are nonidentity involutions yields a
quadrangulation with *these* prescribed rotations and simple facial cycles.
-/
theorem haar_quadrangulation_of_involutions (L : GroupLaws Γ) (s : Fin d → Γ)
    (hinj : ∀ i j, s i = s j → i = j)
    (hinvol : ∀ i, let q := s i * (s (next i))⁻¹; q ≠ 1 ∧ q * q = 1)
    (connected : ∀ v w, Reach (haarTable s).toGraph.Adj v w) :
    (haarTable s).toGraph.IsQuadrangulation := by
  have hd0 := positive_degree (1 : Γ) (haarTable s) connected
  have hd : 2 ≤ d := by
    by_cases h : 2 ≤ d
    · exact h
    · let i : Fin d := ⟨0, hd0⟩
      have hi : next i = i := Fin.ext (by have := (next i).isLt; have := i.isLt; omega)
      exact False.elim ((hinvol i).1 (by rw [hi, L.mul_inv]))
  have back_go (x : Γ) (i : Fin d) : (x * s i) * (s i)⁻¹ = x := by
    rw [L.assoc, L.mul_inv, L.mul_one]
  have go_back (y : Γ) (i : Fin d) : (y * (s i)⁻¹) * s i = y := by
    rw [L.assoc, L.inv_mul, L.mul_one]
  apply Table.toGraph_quadrangulates _ _ hd0
  apply Table.valid_of_diamond (haarTable s) hd rfl rfl back_go go_back
  · intro x i j e
    apply hinj
    change x * s i = x * s j at e
    have e' := congrArg (fun y => x⁻¹ * y) e
    simpa only [← L.assoc, L.inv_mul, L.one_mul] using e'
  · exact across_of_graph_connected (haarTable s) ⟨0, hd0⟩ go_back connected
  · intro x i
    let a := s i
    let b := s (next i)
    let q := a * b⁻¹
    have qsq : q * q = 1 := (hinvol i).2
    have qb : q * b = a := by
      dsimp only [q]
      rw [L.assoc, L.inv_mul, L.mul_one]
    have qa : q * a = b := calc
      q * a = q * (q * b) := congrArg (q * ·) qb.symm
      _ = (q * q) * b := (L.assoc _ _ _).symm
      _ = b := by rw [qsq, L.one_mul]
    change ((x * a) * b⁻¹) * a = x * b
    rw [L.assoc x a b⁻¹]
    change (x * q) * a = x * b
    rw [L.assoc, qa]

end Pisanski
