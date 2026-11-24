import Page.HoGLocal
import Page

namespace Page.PaperWitnesses
open DartGraph

/-- A four-spoked wheel on five vertices. Edge order 01,02,03,04,12,23,34,14. -/
abbrev wheel : DartGraph where
  vertices := 5
  edges := 8
  tail a := #v[0,1,0,2,0,3,0,4,1,2,2,3,3,4,1,4][a]
  rev a := #v[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14][a]
  rev_involutive := by decide
  rev_ne := by decide

/-- Both orientations of a turn may occur in the same trail. These two words
cover all darts and are individually non-backtracking, but they force the
noncyclic hub permutation (1 3)(2 4), in neighbor labels. -/
def wheelWords : List (List wheel.Dart) :=
  [[1,4,12,7,2,10,5,0,8,3,6,15],[9,14,13,11]]
theorem wheel_covers : wheelWords.flatten.Perm wheel.darts := by decide
theorem wheel_trails_are_valid :
    ∀ w ∈ wheelWords, w.Nodup ∧ w ≠ [] ∧ ∀ t ∈ turnPairs w,
      wheel.tail (wheel.rev t.1) = wheel.tail t.2 ∧ wheel.rev t.1 ≠ t.2 := by decide

/-- Proposition 1(2) of arXiv:2411.07347v5 quantifies over distinct trails. -/
theorem wheel_no_opposing_turn_in_distinct_trails :
    ∀ w ∈ wheelWords, ∀ u ∈ wheelWords, w ≠ u → ∀ t ∈ turnPairs w,
      (wheel.rev t.2, wheel.rev t.1) ∉ turnPairs u := by decide

theorem wheel_hub_splits : ¬SingleOn (wheel.reconstruct wheelWords) (wheel.star 0) := by decide
theorem wheel_not_realizable : ¬wheel.Accept wheelWords := by decide


theorem real_degree_switch_rejects_wheel : wheel.hogFit wheelWords = false := by decide

/-- K₃,₃, with parts {0,1,2} and {3,4,5} and lexicographically ordered edges. -/
abbrev utilityGraph : DartGraph where
  vertices := 6
  edges := 9
  tail a := #v[0,3,0,4,0,5,1,3,1,4,1,5,2,3,2,4,2,5][a]
  rev a := #v[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14,17,16][a]
  rev_involutive := by decide
  rev_ne := by decide

def threeFaces : List (List utilityGraph.Dart) :=
  [[0,7,8,15,12,1,2,9,10,5], [4,17,14,3], [6,13,16,11]]

theorem utility_faces_realizable : utilityGraph.Accept threeFaces := by decide
theorem utility_faces_genus : utilityGraph.eulerGenus threeFaces = 1 := by decide
theorem both_directions_in_first_face :
    ∃ w ∈ threeFaces, (0 : utilityGraph.Dart) ∈ w ∧ utilityGraph.rev 0 ∈ w :=
  ⟨[0,7,8,15,12,1,2,9,10,5], by decide, by decide, by decide⟩

end Page.PaperWitnesses
