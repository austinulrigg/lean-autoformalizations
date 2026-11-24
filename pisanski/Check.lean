import Pisanski

-- Displays the exact public statement and its transitive axiom dependencies.
#check Pisanski.pisanski
#print axioms Pisanski.pisanski
#print axioms Pisanski.haar_quadrangulation_of_involutions

-- Specializations illustrating each construction and the smallest parameters.
example : Pisanski.HasQuadrangulation 4 4 := Pisanski.pisanski (by decide) (by decide) (by decide)
example : Pisanski.HasQuadrangulation 6 6 := Pisanski.pisanski (by decide) (by decide) (by decide)
example : Pisanski.HasQuadrangulation 8 5 := Pisanski.pisanski (by decide) (by decide) (by decide)
example : Pisanski.HasQuadrangulation 7 4 := Pisanski.pisanski (by decide) (by decide) (by decide)
