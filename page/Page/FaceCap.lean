import Page.HoGLocal

/-! The 21-vertex, 27-edge simple graph consists of two copies of K₃,₃
with the edge from local vertex 0 to 3 removed. Join the two copies at
their local vertices 3 by one edge and at their local vertices 0 by a
path of length ten. Vertices 0 through 11 are cubic. Vertices 12 through
20, in that order on the path, have degree two.

Darts are numbered by tail, then by head, in increasing order. A 12-bit
mask specifies one of the two cyclic orders at each cubic vertex. The
degree-two orders are forced. The final theorem is for *all* local rotations
of the 54 darts, including every possible face ordering or starting point.
-/

namespace Page.FaceCap
open DartGraph

abbrev D := Fin 54
abbrev V := Fin 21

def tail (a : D) : V :=
  ⟨if a.val < 36 then a.val / 3 else 12 + (a.val - 36) / 2, by split <;> omega⟩

def reverseTable : Vector D 54 :=
  #v[12,15,36,9,13,16,10,14,17,3,6,27,0,4,7,1,5,8,
     30,33,52,28,31,34,29,32,35,11,21,24,18,22,25,19,23,26,
     2,38,37,40,39,42,41,44,43,46,45,48,47,50,49,53,20,51]

def graph : DartGraph where
  vertices := 21
  edges := 27
  tail := tail
  rev := reverseTable.get
  rev_involutive := by decide
  rev_ne := by decide

private def degree (v : V) : Nat := if v.val < 12 then 3 else 2
private def first (v : V) : Nat := if v.val < 12 then 3*v.val else 36 + 2*(v.val-12)
private def slot (v : V) (i : Nat) : D := Fin.ofNat 54 (first v + i)

/-- Increasing or decreasing cyclic order at the tail. -/
def successor (back : Bool) (a : D) : D :=
  let v := tail a
  let d := degree v
  slot v ((a.val - first v + (if back then d-1 else 1)) % d)

def rotation (mask : BitVec 12) (a : D) := successor (mask.getLsbD (tail a).val) a

private theorem star_eq : ∀ v : V, graph.star v =
    (if v.val < 12 then [slot v 0, slot v 1, slot v 2] else [slot v 0,slot v 1]) := by decide

private theorem transitions : ∀ v : V, (if v.val < 12 then
    successor false (slot v 0) = slot v 1 ∧ successor false (slot v 1) = slot v 2 ∧
    successor false (slot v 2) = slot v 0 ∧ successor true (slot v 0) = slot v 2 ∧
    successor true (slot v 1) = slot v 0 ∧ successor true (slot v 2) = slot v 1 ∧
    slot v 1 ≠ slot v 2
    else ∀ b : Bool, successor b (slot v 0) = slot v 1 ∧ successor b (slot v 1) = slot v 0) := by decide

private theorem pair_order (r : D → D) (a b : D) (cyc : SingleOn r [a,b]) :
    r a = b ∧ r b = a := by
  have p : [r a].Perm [b] := cyc.1.cons_inv
  have eq : r a = b := by simpa using p
  have walk : Follows r [a,r a] := cyc.2
  simp only [Follows,List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.cons.injEq,
    and_true,true_and] at walk
  exact ⟨eq,by simpa [eq] using walk⟩

private theorem triple_order (r : D → D) (a b c : D) (cyc : SingleOn r [a,b,c]) :
    (r a = b ∧ r b = c ∧ r c = a) ∨ (r a = c ∧ r c = b ∧ r b = a) := by
  have p : [r a,r (r a)].Perm [b,c] := cyc.1.cons_inv
  have ha := p.subset (by simp : r a ∈ [r a, r (r a)])
  have walk : Follows r [a,r a,r (r a)] := cyc.2
  have close : r (r (r a)) = a := by simpa [Follows] using walk
  obtain e|e := (show r a = b ∨ r a = c by simpa using ha)
  · rw [e] at p
    have e' : r b = c := by simpa using p.cons_inv
    exact Or.inl ⟨e,e',by simpa [e,e'] using close⟩
  · rw [e] at p
    have p' : [c,r c].Perm [c,b] := p.trans (List.Perm.swap c b [])
    have e' : r c = b := by simpa using p'.cons_inv
    exact Or.inr ⟨e,e',by simpa [e,e'] using close⟩

private def orientation (r : D → D) (v : V) := decide (r (slot v 0) = slot v 2)

private def encode (r : D → D) : BitVec 12 :=
  let bits := List.ofFn (fun i : Fin 12 => orientation r ⟨i.val,by omega⟩)
  (BitVec.ofBoolListLE bits).cast (by simp [bits])

private theorem encode_bit (r : D → D) (v : V) (h : v.val < 12) :
    (encode r).getLsbD v.val = orientation r v := by
  change (BitVec.ofBoolListLE (List.ofFn (fun i : Fin 12 => orientation r ⟨i.val,by omega⟩))).getLsbD v.val = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
  simp only [Option.getD_some, List.getElem_ofFn]

/-- The mask enumeration covers arbitrary functions satisfying the existing
single-cycle rotation-system definition on this graph. -/
theorem all_rotations (r : D → D) (hr : graph.IsLocalRotation r) : r = rotation (encode r) := by
  funext a
  let v := tail a
  have mem : a ∈ graph.star v := (graph.mem_star v a).mpr rfl
  have cyc := hr v
  rw [star_eq] at cyc mem
  have tbl := transitions v
  change r a = successor ((encode r).getLsbD v.val) a
  by_cases h : v.val < 12
  · simp only [h,if_true,List.mem_cons,List.not_mem_nil,or_false] at cyc mem tbl
    rw [encode_bit r v h]
    obtain ⟨f0,f1,f2,b0,b1,b2,ne⟩ := tbl
    obtain ⟨r0,r1,r2⟩ | ⟨r0,r2,r1⟩ := triple_order r _ _ _ cyc
    · have orient : orientation r v = false := by simp [orientation,r0,ne]
      rw [orient]
      obtain e|e|e := mem
      · rw [e,r0,f0]
      · rw [e,r1,f1]
      · rw [e,r2,f2]
    · have orient : orientation r v = true := by simp [orientation,r0]
      rw [orient]
      obtain e|e|e := mem
      · rw [e,r0,b0]
      · rw [e,r1,b1]
      · rw [e,r2,b2]
  · simp only [h,if_false,List.mem_cons,List.not_mem_nil,or_false] at cyc mem tbl
    obtain ⟨r0,r1⟩ := pair_order r _ _ cyc
    obtain e|e := mem
    · rw [e,r0,(tbl _).1]
    · rw [e,r1,(tbl _).2]


/-- Follow a face until its starting dart occurs again. The fuel cap is
the graph's total number of darts. Validity of every generated cycle and
exact dart coverage are checked independently in the exhaustive certificate. -/
private def trail (f : D → D) (start : D) : Nat → D → List D
  | 0, _ => []
  | n+1, current =>
    if current = start then [] else current :: trail f start n (f current)

def faces (mask : BitVec 12) : List (List D) :=
  let f := graph.faceStep (rotation mask)
  graph.darts.foldl (fun ws a =>
    if ws.any (fun w => w.contains a) then ws
    else (a :: trail f a 53 (f a)) :: ws) []

/-- The independent checks include the permutation of all 54 darts, adherence
of every face to its successor, and the numerical bounds on these face lists.
This closed computation uses Lean's native decision procedure. -/
private theorem audit : ∀ i : Fin 4096, let m : BitVec 12 := BitVec.ofFin i
    let fs := faces m
    fs.flatten.Perm graph.darts ∧
    (∀ w ∈ fs, Follows (graph.faceStep (rotation m)) w) ∧
    fs.length ≤ 6 ∧ (4 < fs.length → ∃ w ∈ fs, w.length = 28) := by native_decide

private theorem equal_length_of_shared {f : D → D} {u v : List D} {a : D}
    (hu : Follows f u) (hv : Follows f v) (xu : a ∈ u) (xv : a ∈ v)
    (nu : u.Nodup) (nv : v.Nodup) : u.length = v.length := by
  apply List.Perm.length_eq
  apply List.perm_iff_count.mpr
  intro x
  have same : x ∈ u ↔ x ∈ v :=
    ⟨fun h => hu.same_darts hv xu xv h, fun h => hv.same_darts hu xv xu h⟩
  simp only [nu.count,nv.count,same]

/-- For every fitting of the graph there are at most six faces. Every fitting
with more than four faces contains a face of length exactly 28. -/
theorem all_fittings {fs : List (List D)} (h : graph.Accept fs) :
    fs.length ≤ 6 ∧ (4 < fs.length → ∃ w ∈ fs, w.length = 28) := by
  obtain ⟨cover,r,hr,hf⟩ := (graph.accept_iff fs).mp h
  let m := encode r
  have eq : r = rotation m := all_rotations r hr
  rw [eq] at hf
  obtain ⟨cover',hf',bound,wide⟩ := audit m.toFin
  have count : fs.length = (faces m).length := cycle_count_unique _
    (cover.symm.nodup graph.darts_nodup) (cover.trans cover'.symm) hf hf'
  refine ⟨Nat.le_trans (Nat.le_of_eq count) bound,?_⟩
  intro large
  obtain ⟨u,hu,len⟩ := wide (Nat.lt_of_lt_of_eq large count)
  have nonempty : u ≠ [] := by intro e; simp [e] at len
  obtain ⟨a,hit⟩ := List.exists_mem_of_ne_nil u nonempty
  have appears := (cover'.trans cover.symm).subset (List.mem_flatten_of_mem hu hit)
  obtain ⟨w,hw,ha⟩ := List.mem_flatten.mp appears
  have nd := cover.symm.nodup graph.darts_nodup
  have nd' := cover'.symm.nodup graph.darts_nodup
  have lengths := equal_length_of_shared (hf _ hw) (hf' _ hu) ha hit
    ((List.sublist_flatten_of_mem hw).nodup nd) ((List.sublist_flatten_of_mem hu).nodup nd')
  exact ⟨w,hw,lengths.trans len⟩

/-- Both face-count upper bounds are attained. These two small concrete
witnesses are checked by Lean's kernel decision procedure. -/
theorem witnesses :
    (graph.Accept (faces 1170) ∧ (faces 1170).length = 6) ∧
    (graph.Accept (faces 0) ∧ (faces 0).length = 4 ∧ ∀ w ∈ faces 0, w.length ≤ 27) := by
  set_option maxRecDepth 100000 in
    decide

/-- Capping all face lengths at m=27 strictly reduces the maximum achievable
face count, hence changes the genus computed from Euler's formula. -/
theorem capped_bound {fs : List (List D)} (h : graph.Accept fs)
    (cap : ∀ w ∈ fs, w.length ≤ graph.edges) : fs.length ≤ 4 := by
  apply Nat.le_of_not_gt
  intro bad
  obtain ⟨w,hw,large⟩ := (all_fittings h).2 bad
  have lim : w.length ≤ 27 := cap w hw
  omega

end Page.FaceCap
