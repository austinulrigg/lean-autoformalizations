import Page.SmallDegree

namespace Page.DartGraph

private theorem mappedKeys {D : Type} (fs : List (List D)) :
    (fs.flatMap turnPairs).map Prod.fst = fs.flatten := by
  induction fs with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.flatten_cons, List.map_append, ih]
    cases w with
    | nil => rfl
    | cons a as => rw [turnPairs, List.map_fst_zip (by simp)]

private theorem mappedValues {D : Type} (fs : List (List D)) :
    ((fs.flatMap turnPairs).map Prod.snd).Perm fs.flatten := by
  induction fs with
  | nil => exact .refl _
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.flatten_cons, List.map_append]
    apply List.Perm.append _ ih
    cases w with
    | nil => exact .refl _
    | cons a as =>
      rw [turnPairs, List.map_snd_zip (by simp)]
      exact List.perm_append_comm (l₂ := [a])

private theorem lookup_of_unique {D : Type} [DecidableEq D] (ps : List (D × D))
    (nd : (ps.map Prod.fst).Nodup) {x y : D} (hm : (x,y) ∈ ps) :
    ps.lookup x = some y := by
  induction ps with
  | nil => contradiction
  | cons p ps ih =>
    obtain ⟨u,v⟩ := p
    have hn := List.nodup_cons.mp nd
    obtain h|h := List.mem_cons.mp hm
    · cases h; simp
    · have ne : x ≠ u := by intro eq; subst u; exact hn.1 (List.mem_map.mpr ⟨(x,y), h, rfl⟩)
      simp [List.lookup_cons, beq_eq_false_iff_ne.mpr ne, ih hn.2 h]

private theorem follows_from_zip {D : Type} (f : D → D) (xs ys : List D)
    (len : xs.length = ys.length) (h : ∀ p ∈ xs.zip ys, f p.1 = p.2) :
    xs.map f = ys := by
  induction xs generalizing ys with
  | nil => simpa using len.symm
  | cons a as ih =>
    cases ys with
    | nil => simp at len
    | cons b bs =>
      have head := h (a,b) (by simp)
      have tail := ih bs (by simpa using len) (fun p hp => h p (by simp [hp]))
      simp_all

private theorem reconstructed_turn (G : DartGraph) (fs : List (List G.Dart))
    (nd : fs.flatten.Nodup) {a b} (hm : (a,b) ∈ fs.flatMap turnPairs) :
    G.faceStep (G.reconstruct fs) a = b := by
  have pairs := lookup_of_unique _ (mappedKeys fs ▸ nd) hm
  change ((fs.flatMap turnPairs).lookup (G.rev (G.rev a))).getD (G.rev (G.rev a)) = b
  simp [G.rev_involutive, pairs]

private theorem reconstructed_follows (G : DartGraph) (fs : List (List G.Dart))
    (nd : fs.flatten.Nodup) (hne : ∀ w ∈ fs, w ≠ []) :
    ∀ w ∈ fs, Follows (G.faceStep (G.reconstruct fs)) w := by
  intro w hw
  cases w with
  | nil => exact ((hne [] hw) rfl).elim
  | cons a as =>
    apply follows_from_zip _ _ _ (by simp)
    intro p hp
    exact reconstructed_turn G fs nd (List.mem_flatMap.mpr ⟨_,hw,hp⟩)

private theorem keys_have_turn (G : DartGraph) (fs : List (List G.Dart))
    (cover : fs.flatten.Perm G.darts) (a : G.Dart) :
    (a, G.faceStep (G.reconstruct fs) a) ∈ fs.flatMap turnPairs := by
  have mem : a ∈ (fs.flatMap turnPairs).map Prod.fst :=
    mappedKeys fs ▸ cover.mem_iff.mpr (List.mem_finRange _)
  obtain ⟨⟨x,y⟩,hm,rfl⟩ := List.mem_map.mp mem
  simp only [reconstructed_turn G fs (cover.symm.nodup G.darts_nodup) hm]
  exact hm

private theorem perm_from_cover {D : Type} [DecidableEq D] (xs ys : List D)
    (hn : ys.Nodup) (len : xs.length = ys.length) (sub : ys ⊆ xs) :
    xs.Perm ys := by
  induction ys generalizing xs with
  | nil => simp_all
  | cons a as ih =>
    have nd := List.nodup_cons.mp hn
    have ha := sub (by simp : a ∈ a::as)
    have reorder := List.perm_cons_erase ha
    apply reorder.trans
    apply List.Perm.cons a
    apply ih (xs.erase a) nd.2
    · have := reorder.length_eq; simp only [List.length_cons] at *; omega
    · intro b hb
      have ne : b ≠ a := fun eq => nd.1 (eq ▸ hb)
      exact (List.mem_erase_of_ne ne).mpr (sub (List.mem_cons_of_mem _ hb))

/-- The entire table contains turns internal to a trail and turns from other
selected trails. Taking both quantifiers over that table expresses the joint
effect of the two different reverse-transition checks in the C solver. -/
def HoGTurns (G : DartGraph) (fs : List (List G.Dart)) : Prop :=
  ∀ p ∈ fs.flatMap turnPairs,
    G.tail p.2 = G.tail (G.rev p.1) ∧ p.2 ≠ G.rev p.1 ∧
      (2 < (G.star (G.tail p.2)).length →
        (G.rev p.2, G.rev p.1) ∉ fs.flatMap turnPairs)

instance (G : DartGraph) (fs : List (List G.Dart)) : Decidable (G.HoGTurns fs) := by
  unfold HoGTurns; infer_instance

/-- Generator check for one word, including wrap-around. Each consecutive
pair of darts meets at its center, makes a nonbacktracking turn, and does
not have its opposite elsewhere in this word at a vertex of degree > 2. -/
def hogWord (G : DartGraph) (w : List G.Dart) : Prop :=
  ∀ p ∈ turnPairs w,
    G.tail p.2 = G.tail (G.rev p.1) ∧ p.2 ≠ G.rev p.1 ∧
    (2 < (G.star (G.tail p.2)).length → (G.rev p.2, G.rev p.1) ∉ turnPairs w)

instance (G : DartGraph) (w : List G.Dart) : Decidable (G.hogWord w) := by
  unfold hogWord; infer_instance

/-- Row selection compares the new word's turns with the other selected words. -/
def hogCross (G : DartGraph) (w t : List G.Dart) : Prop :=
  ∀ p ∈ turnPairs w, 2 < (G.star (G.tail p.2)).length →
    (G.rev p.2, G.rev p.1) ∉ turnPairs t

instance (G : DartGraph) (w t : List G.Dart) : Decidable (G.hogCross w t) := by
  unfold hogCross; infer_instance

def hogCheckWords (G : DartGraph) (fs : List (List G.Dart)) : Bool :=
  decide ((∀ w ∈ fs, G.hogWord w) ∧ (∀ w ∈ fs, ∀ t ∈ fs, w ≠ t → G.hogCross w t))

theorem hogCheckWords_iff (G : DartGraph) (fs : List (List G.Dart)) :
    G.hogCheckWords fs = true ↔ G.HoGTurns fs := by
  simp only [hogCheckWords, decide_eq_true_eq]
  constructor
  · rintro ⟨one,two⟩ p hp
    obtain ⟨w, hw, hi⟩ := List.mem_flatMap.mp hp
    obtain ⟨inc,turn,opp⟩ := one w hw p hi
    refine ⟨inc,turn,?_⟩
    intro deg bad
    obtain ⟨t,ht,pair⟩ := List.mem_flatMap.mp bad
    by_cases eq : w = t
    · subst t; exact opp deg pair
    · exact two w hw t ht eq p hi deg pair
  · intro allTurns
    constructor
    · intro w hw p hi
      obtain ⟨inc,turn,opp⟩ := allTurns p (List.mem_flatMap.mpr ⟨w,hw,hi⟩)
      exact ⟨inc,turn,fun deg bad => opp deg (List.mem_flatMap.mpr ⟨w,hw,bad⟩)⟩
    · intro w hw t ht _ p hp deg bad
      exact (allTurns p (List.mem_flatMap.mpr ⟨w,hw,hp⟩)).2.2 deg (List.mem_flatMap.mpr ⟨t,ht,bad⟩)

private theorem induced_star_perm (G : DartGraph) (fs : List (List G.Dart))
    (cover : fs.flatten.Perm G.darts) (ht : G.HoGTurns fs) (v : Fin G.vertices) :
    ((G.star v).map (G.reconstruct fs)).Perm (G.star v) := by
  apply perm_from_cover _ _ (show (G.star v).Nodup from G.darts_nodup.filter _) (List.length_map ..)
  intro a ha
  have hval : a ∈ (fs.flatMap turnPairs).map Prod.snd :=
    ((mappedValues fs).trans cover).mem_iff.mpr (List.mem_finRange _)
  obtain ⟨⟨x,y⟩,hm,rfl⟩ := List.mem_map.mp hval
  exact List.mem_map.mpr ⟨G.rev x, (G.mem_star _ _).mpr
    ((ht _ hm).1.symm.trans ((G.mem_star _ _).mp ha)),
    reconstructed_turn G fs (cover.symm.nodup G.darts_nodup) hm⟩

private theorem nodup_subset_length {D : Type} [DecidableEq D] (xs ys : List D)
    (nd : xs.Nodup) (sub : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    have hn := List.nodup_cons.mp nd
    have ha := sub (by simp : a ∈ a::as)
    have len := (List.perm_cons_erase ha).length_eq
    have t := ih (ys.erase a) hn.2 (by
      intro b hb
      exact (List.mem_erase_of_ne (show b ≠ a from fun eq => hn.1 (eq ▸ hb))).mpr (sub (List.mem_cons_of_mem _ hb)))
    simp only [List.length_cons] at *
    omega

private theorem no_return_two (G : DartGraph) {r : G.Dart → G.Dart}
    (hr : G.IsLocalRotation r) (a : G.Dart) (size : 2 < (G.star (G.tail a)).length) :
    r (r a) ≠ a := by
  intro back
  have ha := (G.mem_star _ a).mpr rfl
  obtain ⟨w,hp,hw⟩ := G.local_word hr (G.tail a) (by intro he; rw [he] at ha; contradiction)
  have pair : Follows r [a, r a] := by simp [Follows, back]
  have sub : w ⊆ [a, r a] := hw.same_darts pair (hp.mem_iff.mpr ha) (by simp)
  have nd := hp.symm.nodup (G.darts_nodup.filter _)
  have len := nodup_subset_length _ _ nd sub
  rw [hp.length_eq] at len
  simp only [List.length_cons, List.length_nil] at len
  omega

/-- For the materialized engine only. Nontrivial biconnected blocks have
minimum degree at least two, as needed for its unconditional nonbacktracking rule. -/
theorem hogTurns_of_rotation (G : DartGraph)
    (block : ∀ v, 2 ≤ (G.star v).length) (fs : List (List G.Dart)) {r : G.Dart → G.Dart}
    (hr : G.IsLocalRotation r) (hb : ∀ w ∈ fs, Follows (G.faceStep r) w) :
    G.HoGTurns fs := by
  have edges {a b : G.Dart} (hm : (a,b) ∈ fs.flatMap turnPairs) : G.faceStep r a = b := by
    obtain ⟨w, hw, hp⟩ := List.mem_flatMap.mp hm
    rw [turnPairs_of_follows _ _ (hb _ hw)] at hp
    obtain ⟨x,_,e⟩ := List.mem_map.mp hp
    have := Prod.mk.inj e
    simpa [← this.1] using this.2
  intro p hm
  have he := edges (a := p.1) (b := p.2) hm
  have pres := G.preserves_tail hr (G.rev p.1)
  change G.tail (G.faceStep r p.1) = _ at pres
  rw [he] at pres
  refine ⟨pres, ?_, ?_⟩
  · intro back
    have fixed : r (G.rev p.1) = G.rev p.1 := he.trans back
    have deg := G.degree_one_of_rotation_fixed hr _ fixed
    have := block (G.tail (G.rev p.1))
    omega
  · intro size opp
    have hr' := edges opp
    change r (G.rev (G.rev p.2)) = G.rev p.1 at hr'
    rw [G.rev_involutive] at hr'
    exact no_return_two G hr p.2 size (by rw [hr']; exact he)

private theorem smallFit_local (G : DartGraph) (fs : List (List G.Dart))
    (cover : fs.flatten.Perm G.darts) (ht : G.HoGTurns fs)
    (lo : ∀ v, (G.star v).length ≤ 5) : G.IsLocalRotation (G.reconstruct fs) := by
  let r := G.reconstruct fs
  have turn (a : G.Dart) : (G.rev a, r a) ∈ fs.flatMap turnPairs := by
    simpa [faceStep,r,G.rev_involutive] using keys_have_turn G fs cover (G.rev a)
  apply (G.isLocalRotation_iff _).mpr
  intro v nonempty
  have per := induced_star_perm G fs cover ht v
  have nf (a : G.Dart) : r a ≠ a := by simpa [G.rev_involutive] using (ht _ (turn a)).2.1
  by_cases hsmall : (G.star v).length ≤ 2
  · cases he : G.star v with
    | nil => exact False.elim (nonempty he)
    | cons a as =>
      rw [he] at per hsmall
      cases as with
      | nil =>
        have h : r a = a := by simpa [r] using per
        exact False.elim (nf a h)
      | cons b bs =>
        cases bs with
        | nil =>
          have mapA : r a ∈ [a,b] := by apply per.subset; simp [r]
          have mapB : r b ∈ [a,b] := by apply per.subset; simp [r]
          have ra : r a = b := by simpa [nf] using mapA
          have rb : r b = a := by simpa [nf] using mapB
          exact ⟨[a,b], .refl _, by change Follows r [a,b]; simp [Follows, ra, rb]⟩
        | cons c cs => simp at hsmall
  · apply small_star_cycle r _ nonempty (lo v) per
    intro a ha eq
    have checked :=  ht _ (turn a)
    have vertex : G.tail (r a) = v := by simpa [G.rev_involutive,(G.mem_star _ _).mp ha] using checked.1
    have bad := checked.2.2 (by simp [vertex]; omega)
    apply bad
    simpa [eq,G.rev_involutive] using turn (r a)


/-- A missing transition marks the open end of a partial rotation chain. -/
def hogNext (G : DartGraph) (fs : List (List G.Dart)) (a : G.Dart) : Option G.Dart :=
  (fs.flatMap turnPairs).lookup (G.rev a)

/-- Does the chain from current return to start in one to fuel transitions? -/
def closesWithin {D : Type} [DecidableEq D] (next : D → Option D) (start : D) :
    Nat → D → Bool
  | 0, _ => false
  | fuel + 1, current =>
    match next current with
    | none => false
    | some b => b == start || closesWithin next start fuel b

/-- A closed chain shorter than the degree cannot be completed at its vertex. -/
def hogNoPremature (G : DartGraph) (fs : List (List G.Dart)) : Bool :=
  G.darts.all fun a =>
    !(closesWithin (G.hogNext fs) a ((G.star (G.tail a)).length - 1) a)

/-- Graph-wide switch in HoG/genus.c viable configurations. Above five we
recompute the closed-chain condition from the current table. The C program
maintains the partial rotations incrementally. -/
def hogPrefix (G : DartGraph) (fs : List (List G.Dart)) : Bool :=
  G.hogCheckWords fs &&
    if ∀ v, (G.star v).length ≤ 5 then true else G.hogNoPremature fs

/-- Check the terminal dart budget, nonempty face words, and local tests. -/
def hogFit (G : DartGraph) (fs : List (List G.Dart)) : Bool :=
  decide (fs.flatten.Perm G.darts ∧ ∀ w ∈ fs, w ≠ []) && G.hogPrefix fs

private theorem path_of_closes {D : Type} [DecidableEq D] (next : D → Option D)
    (r : D → D) (ok : ∀ a b, next a = some b → r a = b) (start : D) (n : Nat)
    (a : D) (cl : closesWithin next start n a = true) :
    ∃ xs, xs.length < n ∧ (a :: xs).map r = xs ++ [start] := by
  induction n generalizing a with
  | zero => contradiction
  | succ n ih =>
    cases hn : next a with
    | none => simp [closesWithin, hn] at cl
    | some b =>
      have step := ok _ _ hn
      simp only [closesWithin, hn, Bool.or_eq_true, beq_iff_eq] at cl
      obtain eq|more := cl
      · exact ⟨[], by simp, by simp [step, eq]⟩
      · obtain ⟨xs,len,walk⟩ := ih _ more
        exact ⟨b::xs, by simp; omega, by simpa [step] using congrArg (List.cons b) walk⟩

private theorem closes_of_path {D : Type} [DecidableEq D] (next : D → Option D)
    (r : D → D) (total : ∀ a, next a = some (r a)) (start : D) (n : Nat)
    (a : D) (xs : List D) (len : xs.length < n)
    (walk : (a::xs).map r = xs ++ [start]) : closesWithin next start n a = true := by
  induction n generalizing a xs with
  | zero => omega
  | succ n ih =>
    cases xs with
    | nil =>
      have eq : r a = start := by simpa using walk
      simp [closesWithin, total, eq]
    | cons b bs =>
      have succs : r a = b ∧ (b::bs).map r = bs ++ [start] := by simpa using walk
      simp [closesWithin, total, succs.1, ih b bs (by simpa using len) succs.2]

private theorem noPremature_of_rotation (G : DartGraph) (fs : List (List G.Dart))
    {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r) (hb : ∀ w ∈ fs, Follows (G.faceStep r) w) :
    G.hogNoPremature fs = true := by
  have nextCorrect (a b : G.Dart) (hn : G.hogNext fs a = some b) : r a = b := by
    obtain ⟨l₁,l₂,e,_⟩ := List.lookup_eq_some_iff.mp hn
    have item : (G.rev a,b) ∈ fs.flatMap turnPairs := by simp [e]
    obtain ⟨w,hw,hp⟩ := List.mem_flatMap.mp item
    rw [turnPairs_of_follows _ _ (hb w hw)] at hp
    obtain ⟨x, _, eq⟩ := List.mem_map.mp hp
    obtain ⟨eq₁,eq₂⟩ := Prod.mk.inj eq
    simpa [faceStep,eq₁,G.rev_involutive] using eq₂
  apply List.all_eq_true.mpr
  intro a _
  simp only [Bool.not_eq_true', Bool.eq_false_iff]
  intro cycle
  obtain ⟨xs,len,path⟩ := path_of_closes _ _ nextCorrect _ _ _ cycle
  have ha := (G.mem_star (G.tail a) a).mpr rfl
  obtain ⟨w,hp,hw⟩ := G.local_word hr (G.tail a) (by intro he; rw [he] at ha; contradiction)
  have hsub : w ⊆ a :: xs := hw.same_darts (show Follows r (a::xs) from path)
    (hp.mem_iff.mpr ha) (by simp)
  have bound := nodup_subset_length _ _ (hp.symm.nodup (G.darts_nodup.filter _)) hsub
  rw [hp.length_eq, List.length_cons] at bound
  omega

/-- Any partial selection of faces from a genuine rotation passes the graph-wide
shortcut or the premature-chain test, whichever branch is selected. -/
theorem hogPrefix_of_rotation (G : DartGraph) (block : ∀ v, 2 ≤ (G.star v).length)
    (fs : List (List G.Dart)) {r : G.Dart → G.Dart} (hr : G.IsLocalRotation r)
    (hb : ∀ w ∈ fs, Follows (G.faceStep r) w) : G.hogPrefix fs = true := by
  simp [hogPrefix, hogCheckWords_iff, G.hogTurns_of_rotation block fs hr hb, noPremature_of_rotation G fs hr hb]

private theorem highFit_local (G : DartGraph) (fs : List (List G.Dart))
    (cover : fs.flatten.Perm G.darts) (ht : G.HoGTurns fs) (ok : G.hogNoPremature fs = true) :
    G.IsLocalRotation (G.reconstruct fs) := by
  let r := G.reconstruct fs
  have total (a : G.Dart) : G.hogNext fs a = some (r a) := by
    apply lookup_of_unique _ (mappedKeys fs ▸ cover.symm.nodup G.darts_nodup)
    simpa [faceStep, r, G.rev_involutive] using keys_have_turn G fs cover (G.rev a)
  apply (G.isLocalRotation_iff _).mpr
  intro v hne
  obtain ⟨ws,hp,hf⟩ := exists_cycle_partition r (G.star v) (induced_star_perm G fs cover ht v)
  have long (w : List G.Dart) (hm : w ∈ ws) : (G.star v).length ≤ w.length := by
    have follows := hf w hm
    cases w with
    | nil => exact follows.elim
    | cons a as =>
      apply Nat.le_of_not_gt
      intro shorter
      have present := hp.subset (List.mem_flatten_of_mem hm (List.mem_cons_self (a := a) (l := as)))
      have vertex := (G.mem_star _ _).mp present
      have nocircle := List.all_eq_true.mp ok a (List.mem_finRange _)
      have found := closes_of_path _ _ total a ((G.star v).length - 1) a as
        (by simp only [List.length_cons] at shorter; omega) follows
      simp [vertex,found] at nocircle
  have count := min_length_sum ws (G.star v).length long
  rw [hp.length_eq] at count
  have pos := List.length_pos_iff.mpr hne
  cases ws with
  | nil =>
    have empty := hp.length_eq
    simp_all
  | cons w ws =>
    cases ws with
    | nil => exact ⟨w, by simpa using hp, hf w (by simp)⟩
    | cons x xs => simp only [List.length_cons, Nat.succ_mul] at count; omega

/-- On a materialized block, accepting a complete fit under the actual
maximum-degree switch is equivalent to the existence of its rotation system.
The forward direction constructs the permutation from the supplied walks. -/
theorem hogFit_iff_accept (G : DartGraph) (block : ∀ v, 2 ≤ (G.star v).length)
    (fs : List (List G.Dart)) : G.hogFit fs = true ↔ G.Accept fs := by
  constructor
  · intro fit
    obtain ⟨⟨cover,hne⟩,pre⟩ := (show
      (fs.flatten.Perm G.darts ∧ ∀ w ∈ fs, w ≠ []) ∧ G.hogPrefix fs = true
      by simpa only [hogFit, Bool.and_eq_true, decide_eq_true_eq] using fit)
    obtain ⟨ht,branch⟩ := (show G.HoGTurns fs ∧ _ by
      simpa only [hogPrefix, Bool.and_eq_true, hogCheckWords_iff] using pre)
    refine ⟨cover,?_,reconstructed_follows G fs (cover.symm.nodup G.darts_nodup) hne⟩
    by_cases lo : ∀ v, (G.star v).length ≤ 5
    · exact smallFit_local G fs cover ht lo
    · exact highFit_local G fs cover ht (by simpa [lo] using branch)
  · rintro ⟨cover,hr,hb⟩
    have hne (w : List G.Dart) (hw : w ∈ fs) : w ≠ [] := by
      intro eq; subst w; exact hb [] hw
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨cover,hne⟩, G.hogPrefix_of_rotation block fs hr hb⟩

end Page.DartGraph
