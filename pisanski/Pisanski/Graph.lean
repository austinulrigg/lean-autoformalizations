import Pisanski.Basic

/-!
# Graphs, cyclic rotations, and simple four-sided faces

`Sum V V` is the disjoint union of the two vertex classes. A label at a
vertex names one incident edge. Reversing a dart crosses that edge with
its label unchanged; the face step then rotates at the new vertex.
-/

namespace Pisanski

/-- A graph represented by labeled neighbors and a successor on incident
edges at each vertex. The requirements on these maps are stated below. -/
structure RotationGraph (V : Type) (d : Nat) where
  neighbor : Sum V V → Fin d → Sum V V
  rotate : Sum V V → Fin d → Fin d

namespace RotationGraph
variable {V : Type} {d : Nat} (G : RotationGraph V d)

abbrev Dart (V : Type) (d : Nat) := Sum V V × Fin d

/-- Ordinary graph adjacency, forgetting the label. -/
def Adj (v w : Sum V V) : Prop := ∃ i, G.neighbor v i = w

def reverse (a : Dart V d) : Dart V d := (G.neighbor a.1 a.2, a.2)

def rotateDart (a : Dart V d) : Dart V d := (a.1, G.rotate a.1 a.2)

/-- `F = R τ`, with the reversal applied first. -/
def face (a : Dart V d) : Dart V d := G.rotateDart (G.reverse a)

/-- The finite labels index the complete neighbor set without repetitions. -/
def RegularAt (v : Sum V V) : Prop :=
  (∀ i j, G.neighbor v i = G.neighbor v j → i = j) ∧
  Nonempty (Numbering {w : Sum V V // G.Adj v w} d)

/-- All six pairs of vertices on the proposed boundary are distinct. -/
def FourDistinct {X : Type} (a b c e : X) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ e ∧ b ≠ c ∧ b ≠ e ∧ c ≠ e

/-- The walk returns to the original dart after four steps and traverses
four distinct vertices. This implies that its least period is four. -/
def IsSquare (a : Dart V d) : Prop :=
  G.face (G.face (G.face (G.face a))) = a ∧
    FourDistinct a.1 (G.face a).1 (G.face (G.face a)).1 (G.face (G.face (G.face a))).1

/-- This graph is connected, simple, bipartite, and `d`-regular, with one
cyclic rotation per vertex and simple four-cycles as its facial walks. -/
structure IsQuadrangulation : Prop where
  symm : ∀ {v w}, G.Adj v w → G.Adj w v
  loopless : ∀ v, ¬ G.Adj v v
  leftIndependent : ∀ x y, ¬ G.Adj (.inl x) (.inl y)
  rightIndependent : ∀ x y, ¬ G.Adj (.inr x) (.inr y)
  regular : ∀ v, G.RegularAt v
  connected : ∀ v w, Reach G.Adj v w
  reverseInvolutive : ∀ a, G.reverse (G.reverse a) = a
  cyclic : ∀ v, SingleCycle (G.rotate v)
  faceSquare : ∀ a, G.IsSquare a

/-- In the ordinary graph, the neighbor subtype has exactly `d` elements.
The inverse sends each neighbor to the unique label of its incident edge. -/
noncomputable def neighborNumbering {v : Sum V V}
    (hinj : ∀ i j, G.neighbor v i = G.neighbor v j → i = j) :
    Numbering {w : Sum V V // G.Adj v w} d where
  encode w := Classical.choose w.property
  decode i := ⟨G.neighbor v i, ⟨i, rfl⟩⟩
  left_inv w := Subtype.ext (Classical.choose_spec w.property)
  right_inv i := hinj _ i (Classical.choose_spec (show G.Adj v (G.neighbor v i) from ⟨i, rfl⟩))

/-- Follow the face successor a specified number of times. -/
def faceSteps : Nat → Dart V d → Dart V d
  | 0, a => a
  | n + 1, a => G.face (faceSteps n a)

/-- A square certificate entails that the *least* positive return time is four. -/
theorem isSquare_exactPeriod {a : Dart V d} (h : G.IsSquare a) :
    G.faceSteps 4 a = a ∧ ∀ k, 0 < k → k < 4 → G.faceSteps k a ≠ a := by
  rcases h with ⟨h4, hab, hac, had, _⟩
  refine ⟨h4, ?_⟩
  intro k hk hk' heq
  have hv := congrArg Prod.fst heq
  have cases' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases cases' with rfl | rfl | rfl
  · exact hab hv.symm
  · exact hac hv.symm
  · exact had hv.symm

private theorem isSquare_next {a : Dart V d} (h : G.IsSquare a) : G.IsSquare (G.face a) := by
  rcases h with ⟨h4, hab, hac, had, hbc, hbd, hcd⟩
  refine ⟨congrArg G.face h4, ?_⟩
  change FourDistinct (G.face a).1 (G.face (G.face a)).1
    (G.face (G.face (G.face a))).1 (G.face (G.face (G.face (G.face a)))).1
  rw [h4]
  exact ⟨hbc, hbd, Ne.symm hab, hcd, Ne.symm hac, Ne.symm had⟩

end RotationGraph

/-- Each class has exactly `m` elements via its numbering. The graph is
given together with a cyclic order at every vertex. -/
def HasQuadrangulation (m d : Nat) : Prop :=
  ∃ (V : Type) (_ : Numbering V m) (G : RotationGraph V d), G.IsQuadrangulation

namespace Table
variable {V : Type} {d : Nat} (T : Table V d)

/-- Read a matching table as an ordinary bipartite graph with rotations. -/
def toGraph : RotationGraph V d where
  neighbor
    | .inl x, i => .inr (T.go x i)
    | .inr y, i => .inl (T.back y i)
  rotate
    | .inl _, i => T.rotA i
    | .inr _, i => T.rotB i

private theorem back_injective (h : T.Valid) (y : V) (i j : Fin d)
    (eq : T.back y i = T.back y j) : i = j := by
  apply h.go_inj (T.back y i)
  rw [h.go_back, eq, h.go_back]

private theorem rev_rev (h : T.Valid) (a : RotationGraph.Dart V d) :
    T.toGraph.reverse (T.toGraph.reverse a) = a := by
  obtain ⟨x, i⟩ := a
  cases x with
  | inl x => simp [toGraph, RotationGraph.reverse, h.back_go]
  | inr y => simp [toGraph, RotationGraph.reverse, h.go_back]

private theorem adj_symm (h : T.Valid) {v w : Sum V V} (edge : T.toGraph.Adj v w) :
    T.toGraph.Adj w v := by
  obtain ⟨i, rfl⟩ := edge
  exact ⟨i, congrArg Prod.fst (T.rev_rev h (v, i))⟩

private theorem left_independent (x y : V) : ¬ T.toGraph.Adj (.inl x) (.inl y) := by
  rintro ⟨i, eq⟩
  cases eq

private theorem right_independent (x y : V) : ¬ T.toGraph.Adj (.inr x) (.inr y) := by
  rintro ⟨i, eq⟩
  cases eq

private theorem regular (h : T.Valid) (v : Sum V V) : T.toGraph.RegularAt v := by
  have hinj : ∀ i j, T.toGraph.neighbor v i = T.toGraph.neighbor v j → i = j := by
    cases v with
    | inl x => exact fun i j eq => h.go_inj x i j (Sum.inr.inj eq)
    | inr y => exact fun i j eq => T.back_injective h y i j (Sum.inl.inj eq)
  exact ⟨hinj, ⟨T.toGraph.neighborNumbering hinj⟩⟩

private theorem reach_left (h : T.Valid) (x y : V) :
    Reach T.toGraph.Adj (.inl x) (.inl y) := by
  have path := h.connected x y
  induction path with
  | refl => exact .refl _
  | @tail b c _ step ih =>
    obtain ⟨i, j, heq⟩ := step
    refine .tail (.tail ih (z := .inr (T.go b i)) ⟨i, rfl⟩) ?_
    exact T.adj_symm h ⟨j, congrArg Sum.inr heq.symm⟩

private theorem graph_connected (h : T.Valid) (hd : 0 < d) (v w : Sum V V) :
    Reach T.toGraph.Adj v w := by
  let k : Fin d := ⟨0, hd⟩
  have fromRight (z : V) : T.toGraph.Adj (.inr z) (.inl (T.back z k)) := ⟨k, rfl⟩
  have fromLeft (x : V) (u : Sum V V) : Reach T.toGraph.Adj (.inl x) u := by
    cases u with
    | inl y => exact T.reach_left h x y
    | inr z => exact .tail (T.reach_left h x (T.back z k)) (T.adj_symm h (fromRight z))
  cases v with
  | inl x => exact fromLeft x w
  | inr z => exact Reach.trans (.tail (.refl _) (fromRight z)) (fromLeft (T.back z k) w)

private theorem square_from_left (h : T.Valid) (x : V) (i : Fin d) :
    T.toGraph.IsSquare (.inl x, i) := by
  constructor
  · change (Sum.inl (T.twoV (T.twoV x i) (T.twoI i)), T.twoI (T.twoI i)) = _
    rw [h.fourV, h.fourI]
  · change RotationGraph.FourDistinct (Sum.inl x) (Sum.inr (T.go x i))
      (Sum.inl (T.twoV x i)) (Sum.inr (T.go (T.twoV x i) (T.twoI i)))
    exact ⟨by simp, fun e => h.distinctA x i (Sum.inl.inj e).symm, by simp, by simp,
      fun e => h.distinctB x i (Sum.inr.inj e).symm, by simp⟩

private theorem onto_of_singleCycle {r : Fin d → Fin d} (h : SingleCycle r) (j : Fin d) :
    ∃ i, r i = j := by
  obtain ⟨e, _, onto, step⟩ := h
  obtain ⟨k, rfl⟩ := onto j
  exact ⟨e (prev k), (step (prev k)).trans (congrArg e (next_prev k))⟩

private theorem all_squares (h : T.Valid) (a : RotationGraph.Dart V d) : T.toGraph.IsSquare a := by
  obtain ⟨v, i⟩ := a
  cases v with
  | inl x => exact T.square_from_left h x i
  | inr y =>
    obtain ⟨j, rfl⟩ := onto_of_singleCycle h.cycleB i
    have e : T.toGraph.face (.inl (T.back y j), j) = (.inr y, T.rotB j) := by
      change (Sum.inr (T.go (T.back y j) j), T.rotB j) = _
      rw [h.go_back]
    rw [← e]
    exact T.toGraph.isSquare_next (T.square_from_left h (T.back y j) j)

/-- Soundness of the finite certificate, including graph connectedness and
the simple boundary property from darts based in either color class. -/
theorem toGraph_quadrangulates (h : T.Valid) (hd : 0 < d) : T.toGraph.IsQuadrangulation where
  symm := T.adj_symm h
  loopless v := by
    cases v with
    | inl x => exact T.left_independent x x
    | inr y => exact T.right_independent y y
  leftIndependent := T.left_independent
  rightIndependent := T.right_independent
  regular := T.regular h
  connected := T.graph_connected h hd
  reverseInvolutive := T.rev_rev h
  cyclic v := by cases v with | inl _ => exact h.cycleA | inr _ => exact h.cycleB
  faceSquare := T.all_squares h

end Table

theorem hasQuadrangulation_of_hasTable {m d : Nat} (hd : 0 < d) (h : HasTable m d) :
    HasQuadrangulation m d := by
  obtain ⟨V, numbering, T, valid⟩ := h
  exact ⟨V, numbering, T.toGraph, T.toGraph_quadrangulates valid hd⟩

end Pisanski
