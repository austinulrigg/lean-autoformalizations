import Std

/-!
# House of Graphs PAGE dispatch and low-link walks

Source: `SanderGi/Genus`, commit `4b68d247240ed0e47c8c6e9f40e83f84330242c1`,
`HoG/genus.c` lines 4841–4986, 5017–5083 and 6566–6699. The input
is a connected, simple, accepted graph with its original adjacency order.
The functions below use mathematical integers and immutable state. Resource
failures and worker outcomes are represented explicitly at the dispatch layer.
-/

namespace Page.HoG

abbrev AdjGraph := List (List Nat)
abbrev Edge := Nat × Nat
abbrev Block := List Edge

def row (G : AdjGraph) (v : Nat) := G[v]?.getD []
def edgeCount (G : AdjGraph) := (G.map List.length).sum / 2
def undirected (e : Edge) : Edge := (min e.1 e.2, max e.1 e.2)
def allEdges (G : AdjGraph) : List Edge :=
  (List.range G.length).flatMap fun v => ((row G v).filter (v < ·)).map (v, ·)

private structure Frame where
  vertex : Nat
  parent : Option Nat
  todo : List Nat
  deriving Repr, Inhabited

private structure DFS where
  disc : Array (Option Nat)
  low : Array Nat
  clock : Nat
  edgeStack : List Edge := []
  blocksRev : List Block := []
  bridge : Bool := false
  deriving Inhabited

private inductive WalkMode where
  | findBridge
  | extract
  deriving BEq, DecidableEq, Repr

/-- Pop through the specified edge. The returned block is in chronological
push order, matching the order in which the C implementation relabels it. -/
private def popBlock (boundary : Edge) : List Edge → Block → Option (Block × List Edge)
  | [], _ => none
  | e :: es, acc =>
    if undirected e = undirected boundary then some (e :: acc, es)
    else popBlock boundary es (e :: acc)

private def finish (mode : WalkMode) (u : Nat) (parent : Option Nat) (s : DFS) :
    Option DFS := do
  let some p := parent | return s
  let childLow := s.low[u]?.getD 0
  let parentDisc ← (s.disc[p]?.join)
  let bridge := s.bridge || decide (parentDisc < childLow)
  let next := { s with low := s.low.setIfInBounds p (min (s.low[p]?.getD 0) childLow), bridge }
  if mode == .extract && parentDisc ≤ childLow then
    let (block, rest) ← popBlock (p, u) s.edgeStack []
    let blocks := if block.length == 1 then s.blocksRev else block :: s.blocksRev
    return { next with edgeStack := rest, blocksRev := blocks }
  return next

/-- Each ordinary iteration consumes one adjacency-list entry or pops one
vertex. Discovery occurs at most once per vertex. This gives a direct bound
of the sum of the degrees plus the number of vertices plus one. -/
private def walk (mode : WalkMode) (G : AdjGraph) :
    Nat → List Frame → DFS → Option DFS
  | 0, [], s => some s
  | 0, _ :: _, _ => none
  | _ + 1, [], s => some s
  | fuel + 1, frame :: stack, s => do
    if mode == .findBridge && s.bridge then return s
    let u := frame.vertex
    match frame.todo with
    | [] =>
      let next ← finish mode u frame.parent s
      walk mode G fuel stack next
    | v :: vs =>
      guard (v < G.length)
      let advanced := { frame with todo := vs } :: stack
      match s.disc[v]?.join with
      | none =>
        let edges := if mode == .extract then (u, v) :: s.edgeStack else s.edgeStack
        let next := { s with
          disc := s.disc.setIfInBounds v (some s.clock)
          low := s.low.setIfInBounds v s.clock
          clock := s.clock + 1
          edgeStack := edges }
        walk mode G fuel (⟨v, some u, row G v⟩ :: advanced) next
      | some t =>
        if frame.parent != some v && t < (s.disc[u]?.join).getD 0 then
          let edges := if mode == .extract then (u, v) :: s.edgeStack else s.edgeStack
          let next := { s with
            low := s.low.setIfInBounds u (min t (s.low[u]?.getD 0))
            edgeStack := edges }
          walk mode G fuel advanced next
        else walk mode G fuel advanced s

/-- The C caller has already rejected disconnected inputs, so the root is 0.
The extraction walk also verifies that all vertices were visited and that the
edge stack is empty before accepting its output. -/
private def lowLink (mode : WalkMode) (G : AdjGraph) : Option DFS := do
  guard (!G.isEmpty)
  let n := G.length
  let start : DFS := { disc := (Array.replicate n none).setIfInBounds 0 (some 0)
                       low := Array.replicate n 0, clock := 1 }
  let fuel := (G.map List.length).sum + n + 1
  let final ← walk mode G fuel [⟨0, none, row G 0⟩] start
  guard (mode != .extract || (final.clock == n && final.edgeStack.isEmpty))
  return final

def bridgeDFS (G : AdjGraph) : Option Bool :=
  (lowLink .findBridge G).map (·.bridge)

def nontrivialBlocks (G : AdjGraph) : Option (List Block) :=
  (lowLink .extract G).map (·.blocksRev.reverse)

private def endpoints (es : Block) := (es.flatMap fun e => [e.1, e.2]).eraseDups

/-- Number the vertices in order of first appearance among a block's edge
endpoints, then insert both half-edges in original insertion order. -/
def compactBlock (es : Block) : AdjGraph :=
  let verts := endpoints es
  verts.map fun v =>
    es.filterMap fun e =>
      if e.1 = v then some (verts.idxOf e.2)
      else if e.2 = v then some (verts.idxOf e.1)
      else none

inductive RunResult where
  | answer (genus : Nat)
  | failed
  | cycleMemoryLimit
  deriving DecidableEq, Repr, Inhabited

/-- For the pinned build, the parent checks its signed int accumulator
before adding each nonnegative worker genus. -/
def intMax : Nat := 2147483647

def sumBlocks (solve : AdjGraph → RunResult) : List Block → Nat → RunResult
  | [], acc => .answer acc
  | b :: bs, acc =>
    match solve (compactBlock b) with
    | .failed => .failed
    | .cycleMemoryLimit => .cycleMemoryLimit
    | .answer n =>
      if n ≤ intMax - acc then sumBlocks solve bs (acc + n) else .failed

/-- House of Graphs materialized PAGE on an input that has passed eligibility
and connectivity validation. A bridgeless graph is sent directly to a worker
even when it has a cut vertex. -/
def materialized (solve : AdjGraph → RunResult) (G : AdjGraph) (bridge : Bool) : RunResult :=
  if !bridge then solve G
  else match nontrivialBlocks G with
    | none => .failed
    | some bs => sumBlocks solve bs 0

/-- PAGE-only branch of hog_run_graph/hog_run_page_direct for valid flags.
The tree shortcut is taken up front. The low-memory worker sees the original
graph and bridge flag. Automatic fallback is specific to a cycle-memory limit. -/
def pageOnly (lowMemory autoLowMemory : Bool)
    (blockSolve : AdjGraph → RunResult) (lazySolve : AdjGraph → Bool → RunResult)
    (G : AdjGraph) : RunResult :=
  match bridgeDFS G with
  | none => .failed
  | some bridge =>
    if edgeCount G == G.length - 1 then .answer 0
    else if lowMemory then lazySolve G bridge
    else match materialized blockSolve G bridge with
      | .cycleMemoryLimit =>
        if autoLowMemory then lazySolve G bridge else .cycleMemoryLimit
      | result => result

/-- Abstract the parent's waitpid order by a list of completed worker
outcomes, including a replacement worker when one was launched. -/
def firstWorker : List RunResult → RunResult
  | [] => .failed
  | .answer n :: _ => .answer n
  | _ :: rest => firstWorker rest

theorem firstWorker_answer_from_event (xs : List RunResult) (n : Nat)
    (h : firstWorker xs = .answer n) : RunResult.answer n ∈ xs := by
  induction xs with
  | nil => simp [firstWorker] at h
  | cons x rest ih =>
    cases x with
    | answer m => simp_all [firstWorker]
    | failed => exact List.mem_cons_of_mem _ (ih h)
    | cycleMemoryLimit => exact List.mem_cons_of_mem _ (ih h)

theorem sumBlocks_sound (solve : AdjGraph → RunResult) (value : AdjGraph → Nat)
    (correct : ∀ G n, solve G = .answer n → n = value G) (bs : List Block) :
    ∀ acc n, sumBlocks solve bs acc = .answer n →
      n = acc + (bs.map fun b => value (compactBlock b)).sum := by
  induction bs with
  | nil => simp [sumBlocks]
  | cons b bs ih =>
    intro acc n h
    cases he : solve (compactBlock b) with
    | failed => simp [sumBlocks, he] at h
    | cycleMemoryLimit => simp [sumBlocks, he] at h
    | answer k =>
      simp only [sumBlocks, he] at h
      split at h
      · have hv := correct _ _ he
        have ht := ih _ _ h
        simp only [List.map_cons, List.sum_cons]
        omega
      · contradiction


/-! ## Independent, exponential audit of the decomposition on a concrete input

A nontrivial block in a simple graph is the induced graph on a maximal set of
at least three vertices which stays connected after deleting any one of them.
The audit below uses that definition, rather than discovery times or low links.
It is separate from the HoG worker's executable path.
-/
private def sublistsAll : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs =>
    let rest := sublistsAll xs
    rest ++ rest.map (x :: ·)

/-- All vertex sets, in the fixed increasing label order. -/
def vertexSets (G : AdjGraph) := sublistsAll (List.range G.length)

private def expansion (G : AdjGraph) (allowed reached : List Nat) : List Nat :=
  allowed.filter fun v =>
    reached.contains v || reached.any (fun u => (row G u).contains v)

private def reachedAfter (G : AdjGraph) (allowed : List Nat) (u : Nat) : Nat → List Nat
  | 0 => if u ∈ allowed then [u] else []
  | k + 1 => expansion G allowed (reachedAfter G allowed u k)

/-- A walk of at most k edges entirely in the induced subgraph on S. -/
def WalkWithin (G : AdjGraph) (S : List Nat) : Nat → Nat → Nat → Prop
  | 0, u, v => u = v ∧ v ∈ S
  | k + 1, u, v =>
    v ∈ S ∧ (WalkWithin G S k u v ∨ ∃ w, WalkWithin G S k u w ∧ v ∈ row G w)

theorem reachedAfter_iff {G : AdjGraph} {S : List Nat} {u v : Nat} (k : Nat) :
    v ∈ reachedAfter G S u k ↔ WalkWithin G S k u v := by
  induction k generalizing v with
  | zero =>
    simp only [reachedAfter, WalkWithin]
    split <;> rename_i h
    · simp [eq_comm]
      intro e
      exact e ▸ h
    · simp; intro e; subst e; exact h
  | succ k ih =>
    simp only [reachedAfter, expansion, List.mem_filter, Bool.or_eq_true,
      List.contains_iff_mem, List.any_eq_true, WalkWithin, ih]

def connectedOn (G : AdjGraph) (S : List Nat) : Bool :=
  match S with
  | [] => true
  | start :: _ => S.all (reachedAfter G S start S.length).contains

def biconnectedOn (G : AdjGraph) (S : List Nat) : Bool :=
  decide (3 ≤ S.length) && connectedOn G S &&
  S.all (fun v => connectedOn G (S.erase v))

def referenceBlocks (G : AdjGraph) : List Block :=
  let all := (vertexSets G).filter (biconnectedOn G)
  let maximal := all.filter fun s =>
    !(all.any fun t => s.length < t.length && s.all t.contains)
  maximal.map fun vs => (allEdges G).filter fun e =>
    vs.contains e.1 && vs.contains e.2

private def insertEdge (a : Edge) : Block → Block
  | [] => [a]
  | b :: bs =>
    if a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2) then a :: b :: bs
    else b :: insertEdge a bs

private def blockKey (b : Block) := (b.map undirected).foldr insertEdge []

def HasExactlyBlocks (G : AdjGraph) (bs : List Block) : Prop :=
  (bs.map blockKey).Perm ((referenceBlocks G).map blockKey)

/-- Independently recompute bridges by deleting each edge and testing
connectivity of every vertex in the input. Used only for auditing. -/
def referenceBridge (G : AdjGraph) : Bool :=
  (allEdges G).any fun e =>
    let deletion := (List.range G.length).map fun u =>
      (row G u).filter fun v => undirected (u, v) != e
    !(connectedOn deletion (List.range G.length))

/-- Concrete equality of the two low-link outputs with independent
connectivity tests and maximal induced blocks. A failing audit returns false. -/
def auditDecomposition (G : AdjGraph) : Bool :=
  match bridgeDFS G, nontrivialBlocks G with
  | some flag, some bs =>
    flag == referenceBridge G &&
      decide ((bs.map blockKey).Perm ((referenceBlocks G).map blockKey))
  | _, _ => false

theorem auditDecomposition_sound (G : AdjGraph) (h : auditDecomposition G = true) :
    ∃ flag bs, bridgeDFS G = some flag ∧ nontrivialBlocks G = some bs ∧
      flag = referenceBridge G ∧ HasExactlyBlocks G bs := by
  cases hf : bridgeDFS G with
  | none => simp [auditDecomposition, hf] at h
  | some flag =>
    cases hb : nontrivialBlocks G with
    | none => simp [auditDecomposition, hf, hb] at h
    | some bs =>
      simp only [auditDecomposition, hf, hb, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at h
      exact ⟨flag, bs, rfl, rfl, h.1, h.2⟩

theorem materialized_sound_of_audit (solve : AdjGraph → RunResult) (G : AdjGraph)
    (value : AdjGraph → Nat) (inputAudit : auditDecomposition G = true)
    (correct : ∀ H n, solve H = .answer n → n = value H)
    (additive : ∀ bs, HasExactlyBlocks G bs →
      (bs.map fun b => value (compactBlock b)).sum = value G)
    (flag : Bool) (n : Nat) (h : materialized solve G flag = .answer n) : n = value G := by
  cases flag with
  | false => exact correct _ _ (by simpa [materialized] using h)
  | true =>
    obtain ⟨_, bs, _, hb, _, hc⟩ := auditDecomposition_sound _ inputAudit
    have hh : sumBlocks solve bs 0 = .answer n := by simpa [materialized, hb] using h
    have hn := sumBlocks_sound solve value correct bs 0 n hh
    simpa [additive bs hc] using hn

/-- A successful PAGE-only run, including automatic fallback, reports the
correct genus when the workers are sound, the input decomposition is certified,
and the standard tree and block genus facts apply. This is a composition theorem,
not a proof about an arbitrary implementation of either search engine. -/
theorem pageOnly_sound_of_audit (G : AdjGraph) (low auto : Bool)
    (solve : AdjGraph → RunResult) (lazySolve : AdjGraph → Bool → RunResult)
    (value : AdjGraph → Nat) (ha : auditDecomposition G = true)
    (tree : edgeCount G = G.length - 1 → value G = 0)
    (additive : ∀ bs, HasExactlyBlocks G bs →
      (bs.map fun b => value (compactBlock b)).sum = value G)
    (hm : ∀ H n, solve H = .answer n → n = value H)
    (hl : ∀ flag n, lazySolve G flag = .answer n → n = value G)
    (n : Nat) (h : pageOnly low auto solve lazySolve G = .answer n) :
    n = value G := by
  cases hf : bridgeDFS G with
  | none => simp [pageOnly, hf] at h
  | some flag =>
    by_cases ht : edgeCount G = G.length - 1
    · simp [pageOnly, hf, ht] at h
      omega
    · cases low with
      | true => exact hl _ _ (by simpa [pageOnly, hf, ht] using h)
      | false =>
        cases hw : materialized solve G flag with
        | failed => simp [pageOnly, hf, ht, hw] at h
        | cycleMemoryLimit =>
          cases auto with
          | false => simp [pageOnly, hf, ht, hw] at h
          | true => exact hl _ _ (by simpa [pageOnly, hf, ht, hw] using h)
        | answer k =>
          have hk : k = n := by simpa [pageOnly, hf, ht, hw] using h
          exact hk ▸ materialized_sound_of_audit solve G value ha hm additive flag k hw

/-! Regression inputs deliberately exercise the diverging dispatch paths. The
test worker returns its input order, so a split into two triangles returns
six and handing one graph of order five to the worker returns five. -/
namespace Examples

def bridgedTriangles : AdjGraph :=
  [[1, 2, 3], [0, 2], [0, 1], [0, 4, 5], [3, 5], [3, 4]]

def bowTie : AdjGraph := [[1, 2, 3, 4], [0, 2], [0, 1], [0, 4], [0, 3]]

theorem twoTrianglesBridge : bridgeDFS bridgedTriangles = some true := by decide
theorem bowTieNoBridge : bridgeDFS bowTie = some false := by decide
theorem extractedTriangleSizes :
    (nontrivialBlocks bridgedTriangles).map (List.map List.length) = some [3, 3] := by decide

set_option maxHeartbeats 2000000 in
theorem auditTwoTriangles : auditDecomposition bridgedTriangles = true := by decide

set_option maxHeartbeats 2000000 in
theorem auditBowTie : auditDecomposition bowTie = true := by decide

theorem bowTiePassedWhole :
    pageOnly false false (fun G => .answer G.length) (fun _ _ => .failed) bowTie =
      .answer 5 := by decide

theorem lazyGetsBridgedInput :
    pageOnly true false (fun _ => .failed)
      (fun G b => if b then .answer G.length else .failed) bridgedTriangles =
      .answer 6 := by decide

theorem memoryFallbackGetsOriginal :
    pageOnly false true (fun _ => .cycleMemoryLimit)
      (fun G b => if b then .answer G.length else .failed) bridgedTriangles =
      .answer 6 := by decide

theorem ordinaryFailureStands :
    pageOnly false true (fun _ => .failed) (fun _ _ => .answer 42) bowTie =
      .failed := by decide

end Examples

end Page.HoG
