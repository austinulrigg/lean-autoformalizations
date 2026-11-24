import Page.Targets
import Page.Pivot
import Page.Canonical
import Page.SmallDegree
import Page.Pruning

namespace Page.DartGraph

/-- A complete list of the disjoint orbits of the facial permutation R ∘ rev. -/
def IsFaceList (G : DartGraph) (r : G.Dart → G.Dart) (fs : List (List G.Dart)) : Prop :=
  fs.flatten.Perm G.darts ∧ ∀ w ∈ fs, Follows (G.faceStep r) w

theorem faceList_exists (G : DartGraph) (r : G.Dart → G.Dart) (hr : G.IsLocalRotation r) :
    ∃ fs, G.IsFaceList r fs := exists_cycle_partition _ _ (G.face_perm hr)

theorem faceList_length_unique (G : DartGraph) {r : G.Dart → G.Dart}
    {fs gs : List (List G.Dart)} (hf : G.IsFaceList r fs) (hg : G.IsFaceList r gs) :
    fs.length = gs.length :=
  cycle_count_unique _ (hf.1.symm.nodup G.darts_nodup) (hf.1.trans hg.1.symm) hf.2 hg.2

/-- If k faces fit, the other k−1 faces already consume at least this much space. -/
def lengthCap (G : DartGraph) (k : Nat) := G.darts.length - (k - 1) * G.minFaceLength

/-- Index candidate trails by required dart once per face-count search. -/
def candidateTable (G : DartGraph) (k : Nat) :
    Vector (List (List G.Dart)) (2 * G.edges) :=
  let catalog := canonicalCatalog G.darts G.legalTurn (G.lengthCap k)
  Vector.ofFn fun d => catalog.filter (·.contains d)

def candidates (G : DartGraph) (k : Nat) (d : G.Dart) := (G.candidateTable k)[d]

@[simp] theorem candidates_eq (G : DartGraph) (k : Nat) (d : G.Dart) :
    G.candidates k d = canonicalPool G.darts G.legalTurn (G.lengthCap k) d := by
  simp [candidates, candidateTable, canonicalPool]

/-- Look for a realizable family with exactly k faces. The required dart is
chosen again from the current candidate set after every recursive extension. -/
def atCount (G : DartGraph) (k : Nat) : Option (List (List G.Dart)) :=
  let table := G.candidateTable k
  let pool := fun d : G.Dart => table[d]
  pivotFirstFit pool
    (fun fs => budget G.darts.length k fs && G.viable fs)
    (fun fs => decide (G.Accept fs ∧ fs.length = k))
    (requiredDartOrder pool G.rev) G.darts []

theorem atCount_sound {G : DartGraph} {k : Nat} {fs : List (List G.Dart)}
    (h : G.atCount k = some fs) : G.Accept fs ∧ fs.length = k :=
  of_decide_eq_true (pivotFirstFit_sound h)

private theorem nonempty_faces {G : DartGraph} {r} {fs} (hf : G.IsFaceList r fs) :
    ∀ w ∈ fs, w ≠ [] := by
  intro w hw h
  subst w
  exact hf.2 [] hw

private theorem atCount_complete_canonical (G : DartGraph) (r : G.Dart → G.Dart) (hr : G.IsLocalRotation r)
    (fs : List (List G.Dart)) (hf : G.IsFaceList r fs)
    (hc : ∀ w ∈ fs, isCanonical w = true) :
    ∃ out, G.atCount fs.length = some out := by
  have hn := hf.1.symm.nodup G.darts_nodup
  have hne := nonempty_faces hf
  have hpool : ∀ w ∈ fs, ∀ d ∈ w, w ∈ G.candidates fs.length d := by
    intro w hw d hd
    rw [candidates_eq]
    cases w with
    | nil => simp at hd
    | cons a as =>
      have hs := List.sublist_flatten_of_mem hw
      exact canonicalPool_complete _ _ _ _ (G.legal_faceStep r hr) a as (hf.2 _ hw)
        (fun x hx => hf.1.subset (hs.subset hx)) (hs.nodup hn)
        (G.face_length_bound hr hf.1 hf.2 hw) hd (hc _ hw)
  have hv (rem picked : List (List G.Dart)) (hp : (rem ++ picked).Perm fs) :
      (budget G.darts.length fs.length picked && G.viable picked) = true := by
    apply Bool.and_eq_true_iff.mpr
    exact ⟨budget_safe hf.1 hne hp, G.viable_of_rotation r hr picked
      (fun w hw => hf.2 w (hp.subset (List.mem_append_right rem hw)))⟩
  have ha (out : List (List G.Dart)) (hp : out.Perm fs) :
      decide (G.Accept out ∧ out.length = fs.length) = true := by
    apply decide_eq_true
    exact ⟨(G.accept_iff _).mpr ⟨hp.flatten.trans hf.1, r, hr,
      fun w hw => hf.2 w (hp.subset hw)⟩, hp.length_eq⟩
  exact pivotFirstFit_complete (requiredDartOrder_perm _ _) hf.1 hn hne hpool hv ha

/-- Every actual rotation is reachable by the face search at its own face count.
The comparison accepts face words starting anywhere, even though the generator
lists each cycle starting only at its least dart. -/
theorem atCount_complete (G : DartGraph) (r : G.Dart → G.Dart) (hr : G.IsLocalRotation r)
    (fs : List (List G.Dart)) (hf : G.IsFaceList r fs) :
    ∃ out, G.atCount fs.length = some out := by
  have normalized : G.IsFaceList r (fs.map canonicalWord) := by
    refine ⟨(canonical_flatten fs).trans hf.1, ?_⟩
    intro w hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    exact canonicalWord_follows _ _ (hf.2 t ht)
  have starts (w) (hw : w ∈ fs.map canonicalWord) : isCanonical w = true := by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw
    exact canonicalWord_isCanonical t
  simpa using atCount_complete_canonical G r hr _ normalized starts

/-- The executable PAGE search. Return the first fit at the highest attainable count. -/
def page (G : DartGraph) : Option (List (List G.Dart)) :=
  descending G.atCount (G.darts.length / G.minFaceLength)

theorem page_returns (G : DartGraph) : ∃ out, G.page = some out := by
  obtain ⟨fs, hf⟩ := G.faceList_exists _ G.default_isLocalRotation
  have bound := G.target_bound G.default_isLocalRotation hf.1 hf.2
  obtain ⟨_, x, _, _, hx⟩ :=
    descending_dominates G.atCount bound (G.atCount_complete _ G.default_isLocalRotation fs hf)
  exact ⟨x, hx⟩

/-- Soundness and global optimality. The comparison ranges over every local rotation. -/
theorem page_correct (G : DartGraph) {out} (ho : G.page = some out) :
    G.IsLocalRotation (G.reconstruct out) ∧ G.IsFaceList (G.reconstruct out) out ∧
      ∀ r, G.IsLocalRotation r → ∀ fs, G.IsFaceList r fs → fs.length ≤ out.length := by
  obtain ⟨_, _, hx⟩ := descending_chosen G.atCount ho
  obtain ⟨⟨hc, hr, hw⟩, _⟩ := atCount_sound hx
  refine ⟨hr, ⟨hc, hw⟩, ?_⟩
  intro r hrot fs hf
  have bound := G.target_bound hrot hf.1 hf.2
  obtain ⟨j, x, hj, hfit, eq⟩ := descending_dominates G.atCount bound
    (G.atCount_complete r hrot fs hf)
  have same := Option.some.inj (eq.symm.trans ho)
  simpa only [same, ← (atCount_sound hfit).2] using hj

/-- Total interface. The proof of success is erased by Lean on execution. -/
def bestFaces (G : DartGraph) : List (List G.Dart) :=
  G.page.get (by obtain ⟨x, hx⟩ := G.page_returns; simp [hx])

theorem page_eq_some_bestFaces (G : DartGraph) : G.page = some G.bestFaces := by
  unfold bestFaces
  simp

/-- The sole face of the one-vertex, edgeless connected graph has an empty boundary.
At positive edge count the returned orbits already are the full list of walks. -/
def facialWalks (G : DartGraph) (fs : List (List G.Dart)) : List (List G.Dart) :=
  if G.vertices = 1 ∧ G.edges = 0 then [[]] else fs

def faceCount (G : DartGraph) (fs : List (List G.Dart)) := (G.facialWalks fs).length

/-- Exact integer numerator of the orientable Euler genus formula for a connected graph. -/
def twiceGenus (G : DartGraph) (fs : List (List G.Dart)) : Int :=
  2 + (G.edges : Int) - G.vertices - G.faceCount fs

def eulerGenus (G : DartGraph) (fs : List (List G.Dart)) : Int := G.twiceGenus fs / 2

def genus? (G : DartGraph) : Option Int := G.page.map G.eulerGenus

theorem genus_eq_some (G : DartGraph) : G.genus? = some (G.eulerGenus G.bestFaces) := by
  simp [genus?, G.page_eq_some_bestFaces]

/-- The public output for connected graphs: orientable genus and facial dart walks. -/
def result (G : DartGraph) : Int × List (List G.Dart) :=
  let fs := G.bestFaces
  (G.eulerGenus fs, G.facialWalks fs)

/-- The returned witness and exact Euler numerator are optimal BEFORE division by two.
For a connected graph the usual rotation principle and Euler formula identify this
integer numerator with twice the orientable genus. -/
theorem minimum_genus (G : DartGraph) :
    G.IsLocalRotation (G.reconstruct G.bestFaces) ∧
    G.IsFaceList (G.reconstruct G.bestFaces) G.bestFaces ∧
    ∀ r, G.IsLocalRotation r → ∀ fs, G.IsFaceList r fs →
      G.twiceGenus G.bestFaces ≤ G.twiceGenus fs ∧
      G.eulerGenus G.bestFaces ≤ G.eulerGenus fs := by
  obtain ⟨hr, hf, best⟩ := G.page_correct G.page_eq_some_bestFaces
  refine ⟨hr, hf, ?_⟩
  intro r hrot fs hfs
  have le := best r hrot fs hfs
  have count : G.faceCount fs ≤ G.faceCount G.bestFaces := by
    unfold faceCount facialWalks
    split <;> simp_all only [List.length_cons, List.length_nil, Nat.le_refl]
  have twice : G.twiceGenus G.bestFaces ≤ G.twiceGenus fs := by
    unfold twiceGenus
    omega
  exact ⟨twice, Int.ediv_le_ediv (by decide) twice⟩

end Page.DartGraph
