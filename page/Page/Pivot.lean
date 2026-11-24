import Std

/-!
At each recursive state an arbitrary permutation can put a preferred required
dart first. The ranking below prefers an uncovered reverse of a covered dart
and breaks ties by counting the still-disjoint candidate trails.
-/
namespace Page

variable {D : Type} [DecidableEq D]

private def pivotGo (pool : D → List (List D)) (viable accept : List (List D) → Bool)
    (order : List (List D) → List D → List D) : Nat → List D → List (List D) → Option (List (List D))
  | 0, _, picked => if accept picked then some picked else none
  | n+1, ds, picked =>
    match order picked ds with
    | [] => if accept picked then some picked else none
    | d :: rest =>
      if d ∈ picked.flatten then pivotGo pool viable accept order n rest picked
      else (pool d).findSome? fun f =>
        if d ∈ f ∧ f.Nodup ∧ (∀ a ∈ f, a ∉ picked.flatten) ∧ viable (f :: picked) = true
        then pivotGo pool viable accept order n rest (f :: picked)
        else none

/-- First-success backtracking. A valid ordering chooses a pivot without
adding, removing or repeating any remaining darts. -/
def pivotFirstFit (pool : D → List (List D)) (viable accept : List (List D) → Bool)
    (order : List (List D) → List D → List D) (ds : List D) (picked : List (List D)) :=
  pivotGo pool viable accept order ds.length ds picked

private theorem pivotGo_sound {pool : D → List (List D)} {viable accept : List (List D) → Bool}
    {order : List (List D) → List D → List D} {k ds picked out}
    (h : pivotGo pool viable accept order k ds picked = some out) : accept out = true := by
  induction k generalizing ds picked with
  | zero =>
    simp only [pivotGo] at h
    split at h <;> simp_all
  | succ k ih =>
    simp only [pivotGo] at h
    split at h
    · split at h <;> simp_all
    · split at h
      · exact ih h
      · obtain ⟨_, _, hf⟩ := List.exists_of_findSome?_eq_some h
        split at hf
        · exact ih hf
        · contradiction

theorem pivotFirstFit_sound {pool : D → List (List D)} {viable accept : List (List D) → Bool}
    {order : List (List D) → List D → List D} {ds picked out}
    (h : pivotFirstFit pool viable accept order ds picked = some out) : accept out = true :=
  pivotGo_sound h

omit [DecidableEq D] in
private theorem disjoint_parts {rem picked target : List (List D)}
    (hp : (rem ++ picked).Perm target) (hn : target.flatten.Nodup) :
    ∀ a ∈ rem.flatten, a ∉ picked.flatten := by
  have h : (rem.flatten ++ picked.flatten).Nodup := by
    simpa only [List.flatten_append] using hp.flatten.symm.nodup hn
  exact fun a ha hb => (List.nodup_append.mp h).2.2 a ha a hb rfl

private theorem pivotGo_complete {pool : D → List (List D)} {viable accept : List (List D) → Bool}
    {order : List (List D) → List D → List D} {target : List (List D)}
    (horder : ∀ picked ds, (order picked ds).Perm ds)
    (hn : target.flatten.Nodup) (hne : ∀ f ∈ target, f ≠ [])
    (hpool : ∀ f ∈ target, ∀ d ∈ f, f ∈ pool d)
    (hviable : ∀ rem picked, (rem ++ picked).Perm target → viable picked = true)
    (haccept : ∀ out, out.Perm target → accept out = true)
    (k : Nat) (ds : List D) (rem picked : List (List D)) (hk : ds.length = k)
    (hp : (rem ++ picked).Perm target)
    (hleft : ∀ d ∈ rem.flatten, d ∈ ds)
    (huniv : ∀ d ∈ ds, d ∈ target.flatten) :
    (pivotGo pool viable accept order k ds picked).isSome := by
  induction k generalizing ds rem picked with
  | zero =>
    have hds : ds = [] := List.length_eq_zero_iff.mp hk
    subst ds
    have hempty : rem = [] := by
      cases rem with
      | nil => rfl
      | cons f fs =>
        have hft : f ∈ target := hp.mem_iff.mp (by simp)
        cases f with
        | nil => exact False.elim (hne [] hft rfl)
        | cons d face => simpa using hleft d (by simp)
    subst rem
    simp only [List.nil_append] at hp
    simp [pivotGo, haccept picked hp]
  | succ k ih =>
    have hor := horder picked ds
    have hlen := hor.length_eq.trans hk
    cases eq : order picked ds with
    | nil => simp [eq] at hlen
    | cons d rest =>
      rw [eq] at hor hlen
      have hrest : rest.length = k := by simpa using hlen
      have hA : ∀ a ∈ rem.flatten, a ∈ d :: rest := fun a ha => hor.symm.subset (hleft a ha)
      have hB : ∀ a ∈ d :: rest, a ∈ target.flatten := fun a ha => huniv a (hor.subset ha)
      have huniv' : ∀ a ∈ rest, a ∈ target.flatten := fun _ ha => hB _ (List.mem_cons_of_mem _ ha)
      simp only [pivotGo, eq]
      by_cases hcovered : d ∈ picked.flatten
      · rw [if_pos hcovered]
        apply ih rest rem picked hrest hp _ huniv'
        intro a ha
        rcases List.mem_cons.mp (hA a ha) with e | h
        · subst a
          exact False.elim (disjoint_parts hp hn d ha hcovered)
        · exact h
      · rw [if_neg hcovered, List.findSome?_isSome_iff]
        have hd : d ∈ rem.flatten := by
          have hmem := hp.flatten.mem_iff.mpr (hB d (by simp))
          simpa only [List.flatten_append, List.mem_append, hcovered, or_false] using hmem
        obtain ⟨f, hf, hdf⟩ := List.mem_flatten.mp hd
        have hft : f ∈ target := hp.subset (List.mem_append_left _ hf)
        have hmove : (rem.erase f ++ f :: picked).Perm target :=
          (List.perm_middle.trans ((List.perm_cons_erase hf).symm.append_right picked)).trans hp
        have hwhole := hmove.flatten.symm.nodup hn
        simp only [List.flatten_append, List.flatten_cons, List.nodup_append] at hwhole
        have hfdis : ∀ a ∈ f, a ∉ picked.flatten :=
          fun a ha hb => hwhole.2.1.2.2 a ha a hb rfl
        refine ⟨f, hpool _ hft _ hdf, ?_⟩
        rw [if_pos ⟨hdf, hwhole.2.1.1, hfdis, hviable _ _ hmove⟩]
        apply ih rest (rem.erase f) (f :: picked) hrest hmove _ huniv'
        intro a ha
        have hassigned : a ∈ rem.flatten :=
          (List.perm_cons_erase hf).flatten.mem_iff.mpr (List.mem_append_right f ha)
        rcases List.mem_cons.mp (hA a hassigned) with e | h
        · subst a
          exact False.elim (disjoint_parts hmove hn d ha (List.mem_flatten_of_mem (by simp) hdf))
        · exact h

/-- Every eligible exact cover ensures a successful search for any dynamic
choice of required dart. A different accepted cover may be encountered first. -/
theorem pivotFirstFit_complete {pool : D → List (List D)} {viable accept : List (List D) → Bool}
    {order : List (List D) → List D → List D} {target : List (List D)} {darts : List D}
    (horder : ∀ picked ds, (order picked ds).Perm ds)
    (cover : target.flatten.Perm darts) (hn : target.flatten.Nodup)
    (hne : ∀ f ∈ target, f ≠ []) (hpool : ∀ f ∈ target, ∀ d ∈ f, f ∈ pool d)
    (hviable : ∀ rem picked, (rem ++ picked).Perm target → viable picked = true)
    (haccept : ∀ out, out.Perm target → accept out = true) :
    ∃ out, pivotFirstFit pool viable accept order darts [] = some out := by
  apply Option.isSome_iff_exists.mp
  exact pivotGo_complete horder hn hne hpool hviable haccept darts.length darts target []
    rfl (by simp) (fun _ h => cover.subset h) (fun _ h => cover.symm.subset h)

/-- First prefer an uncovered dart whose reverse is already covered, then other
uncovered darts. Within either class, fewer still-disjoint candidate faces win.
Already covered darts can be skipped, and need no candidate count. -/
def pivotScore (pool : D → List (List D)) (rev : D → D) (used : List D) (a : D) : Nat × Nat :=
  if a ∈ used then (2, 0)
  else (if rev a ∈ used then 0 else 1,
    (pool a).countP fun f => f.all fun d => !(used.contains d))

/-- Lexicographic priority, with the fewest available trails breaking ties. -/
def pivotScoreLE (s t : Nat × Nat) : Bool :=
  decide (s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 ≤ t.2))

/-- Structural insertion keeps small evaluations reducible in Lean's kernel. -/
private def insertRank {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: bs => if le a b then a :: b :: bs else b :: insertRank le a bs

private theorem insertRank_perm {α : Type} (le : α → α → Bool) (a : α) (xs : List α) :
    (insertRank le a xs).Perm (a :: xs) := by
  induction xs with
  | nil => exact .refl _
  | cons b bs ih =>
    simp only [insertRank]; split
    · exact .refl _
    · exact (ih.cons b).trans (.swap a b bs)

private def rankBy {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: as => insertRank le a (rankBy le as)

private theorem rankBy_perm {α : Type} (le : α → α → Bool) (xs : List α) :
    (rankBy le xs).Perm xs := by
  induction xs with
  | nil => exact .refl _
  | cons a as ih => exact (insertRank_perm le a _).trans (ih.cons a)

private theorem rankBy_sorted {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (xs : List α) :
    (rankBy le xs).Pairwise fun a b => le a b = true := by
  have ins (a : α) (ys : List α) (ok : ys.Pairwise fun x y => le x y = true) :
      (insertRank le a ys).Pairwise fun x y => le x y = true := by
    induction ys with
    | nil => simp [insertRank]
    | cons b bs ih =>
      have pair := List.pairwise_cons.mp ok
      simp only [insertRank]; split
      next h =>
        apply List.pairwise_cons.mpr
        exact ⟨fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ h)
          (fun m => trans a b x h (pair.1 x m)), ok⟩
      next h =>
        refine List.pairwise_cons.mpr ⟨?_, ih pair.2⟩
        intro x hx
        rcases List.mem_cons.mp ((insertRank_perm le a bs).subset hx) with e | m
        · subst x
          simpa [h] using total a b
        · exact pair.1 x m
  induction xs with
  | nil => simp [rankBy]
  | cons a as ih => exact ins a _ ih

/-- Rank once per remaining dart and stably sort. If no uncovered reverse
exists, search continues at another uncovered dart. -/
def requiredDartOrder (pool : D → List (List D)) (rev : D → D)
    (picked : List (List D)) (ds : List D) : List D :=
  let score := pivotScore pool rev picked.flatten
  let scored := ds.map fun d => (score d, d)
  (rankBy (fun s t => pivotScoreLE s.1 t.1) scored).map Prod.snd

/-- The heuristic changes only the order. This discharges the entire pivot
obligation in the backtracking completeness theorem. -/
theorem requiredDartOrder_perm (pool : D → List (List D)) (rev : D → D)
    (picked : List (List D)) (ds : List D) :
    (requiredDartOrder pool rev picked ds).Perm ds := by
  unfold requiredDartOrder
  apply List.Perm.trans ((rankBy_perm _ _).map Prod.snd)
  simp [Function.comp_def]

/-- In particular, the first dart has minimum priority and count among all
remaining darts. This also verifies how the two priorities are combined. -/
theorem requiredDartOrder_ranked (pool : D → List (List D)) (rev : D → D)
    (picked : List (List D)) (ds : List D) :
    (requiredDartOrder pool rev picked ds).Pairwise fun a b =>
      pivotScoreLE (pivotScore pool rev picked.flatten a) (pivotScore pool rev picked.flatten b) := by
  let score := pivotScore pool rev picked.flatten
  let scored := ds.map fun d => (score d, d)
  let le := fun a b : (Nat × Nat) × D => pivotScoreLE a.1 b.1
  have sorted : (rankBy le scored).Pairwise fun a b => le a b := by
    apply rankBy_sorted
    · intro a b c hab hbc
      simp only [le, pivotScoreLE, decide_eq_true_eq] at *
      omega
    · intro a b
      simp only [le, pivotScoreLE, Bool.or_eq_true, decide_eq_true_eq]
      omega
  have agrees (s : (Nat × Nat) × D) (h : s ∈ rankBy le scored) : score s.2 = s.1 := by
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp ((rankBy_perm _ _).subset h)
    rfl
  apply List.pairwise_map.mpr
  apply sorted.imp_of_mem
  intro a b ha hb h
  change pivotScoreLE (score a.2) (score b.2) = true
  rwa [agrees _ ha, agrees _ hb]

end Page
