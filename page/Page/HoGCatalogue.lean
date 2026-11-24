import Page
import Page.HoGLocal

namespace Page.DartGraph

/-- A complete face family in the materialized catalogue of absolute cap c.
Words are compared up to cyclic change of their starting dart. -/
def CappedFit (G : DartGraph) (cap k : Nat) (fs : List (List G.Dart)) : Prop :=
  G.Accept fs ∧ fs.length = k ∧ ∀ w ∈ fs, w.length ≤ cap

/-- Mathematical exact-cover core. Candidate storage, rotations of the printed
word, row ordering, automorphism pruning, numerical bounds and early returns
in the actual C execution are outside this abstraction. -/
def hogAtCap (G : DartGraph) (cap k : Nat) : Option (List (List G.Dart)) :=
  let pool := canonicalPool G.darts G.legalTurn cap
  pivotFirstFit pool (G.hogPrefix ·)
    (fun fs => G.hogFit fs && decide (fs.length = k ∧ ∀ w ∈ fs, w.length ≤ cap))
    (requiredDartOrder pool G.rev) G.darts []

theorem hogAtCap_sound (G : DartGraph) (block : ∀ v, 2 ≤ (G.star v).length)
    {cap k fs} (run : G.hogAtCap cap k = some fs) : G.CappedFit cap k fs := by
  have h := Page.pivotFirstFit_sound run
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(G.hogFit_iff_accept block _).mp h.1, h.2⟩

/-- Every rotation whose facial walks fit the stated cap is accessible. -/
theorem hogAtCap_complete (G : DartGraph) (block : ∀ v, 2 ≤ (G.star v).length)
    (cap : Nat) (r : G.Dart → G.Dart) (hr : G.IsLocalRotation r)
    (fs : List (List G.Dart)) (hf : G.IsFaceList r fs) (hc : ∀ w ∈ fs, w.length ≤ cap) :
    ∃ out, G.hogAtCap cap fs.length = some out := by
  let target := fs.map canonicalWord
  have cover : target.flatten.Perm G.darts := (canonical_flatten fs).trans hf.1
  have nd := cover.symm.nodup G.darts_nodup
  have faces (w) (hw : w ∈ target) : Follows (G.faceStep r) w := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
    exact canonicalWord_follows _ _ (hf.2 t ht)
  have bound (w) (hw : w ∈ target) : w.length ≤ cap := by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hw
    rw [(canonicalWord_perm t).length_eq]
    exact hc t ht
  have ne (w) (hw : w ∈ target) : w ≠ [] := by
    intro e
    subst w
    exact faces [] hw
  have pool (w) (hw : w ∈ target) (d) (hd : d ∈ w) :
      w ∈ canonicalPool G.darts G.legalTurn cap d := by
    obtain ⟨t,ht,eq⟩ := List.mem_map.mp hw
    have can : isCanonical w = true := eq ▸ canonicalWord_isCanonical t
    cases w with
    | nil => simp at hd
    | cons a as =>
      have sub := List.sublist_flatten_of_mem hw
      exact canonicalPool_complete _ _ _ _ (G.legal_faceStep r hr) a as (faces _ hw)
        (fun _ hx => cover.subset (sub.subset hx)) (sub.nodup nd) (bound _ hw) hd can
  have viable (rem picked : List (List G.Dart)) (hp : (rem ++ picked).Perm target) :
      G.hogPrefix picked = true :=
    G.hogPrefix_of_rotation block picked hr
      (fun w hw => faces w (hp.subset (List.mem_append_right rem hw)))
  have accept (out : List (List G.Dart)) (hp : out.Perm target) :
      (G.hogFit out && decide (out.length = fs.length ∧ ∀ w ∈ out, w.length ≤ cap)) = true := by
    apply Bool.and_eq_true_iff.mpr
    refine ⟨(G.hogFit_iff_accept block _).mpr ((G.accept_iff _).mpr
      ⟨hp.flatten.trans cover, r, hr, fun w hw => faces w (hp.subset hw)⟩), ?_⟩
    exact decide_eq_true ⟨by simpa [target] using hp.length_eq, fun w hw => bound w (hp.subset hw)⟩
  exact pivotFirstFit_complete (requiredDartOrder_perm _ _) cover nd ne pool viable accept

/-- Exact decision scope of the bounded search. Set cap=G.edges for the
upstream hard cutoff; cap=2*G.edges reproduces the paper's full length range. -/
theorem hogAtCap_iff (G : DartGraph) (block : ∀ v, 2 ≤ (G.star v).length) (cap k : Nat) :
    (∃ out, G.hogAtCap cap k = some out) ↔ ∃ fs, G.CappedFit cap k fs := by
  constructor
  · rintro ⟨out,run⟩
    exact ⟨out, G.hogAtCap_sound block run⟩
  · rintro ⟨fs,hf,rfl,b⟩
    obtain ⟨cov,r,hr,walk⟩ := (G.accept_iff fs).mp hf
    exact G.hogAtCap_complete block cap r hr fs ⟨cov,walk⟩ b

end Page.DartGraph
