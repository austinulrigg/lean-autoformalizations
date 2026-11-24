import Std

namespace Page

/-- Read the remaining darts and then close back at the first dart. -/
def AllowedPath {D : Type} (allow : D → D → Bool) (first : D) :
    D → List D → Prop
  | current, [] => allow current first = true
  | current, d :: ds => allow current d = true ∧ AllowedPath allow first d ds

theorem allowedPath_of_map {D : Type} (allow : D → D → Bool) (r : D → D)
    (legal : ∀ a, allow a (r a) = true) (first current : D) (path : List D)
    (h : (current :: path).map r = path ++ [first]) :
    AllowedPath allow first current path := by
  induction path generalizing current with
  | nil =>
    have hl : r current = first := by simpa using h
    exact hl ▸ legal current
  | cons d ds ih =>
    have edges := List.cons.inj h
    exact ⟨edges.1 ▸ legal current, ih _ edges.2⟩

end Page
