import Page.HoGCatalogue
import Page.HoGBlocks
import Page.FaceCap
import Page.PaperWitnesses

namespace Page.FaceCap

private theorem degree_two_or_more : ∀ v, 2 ≤ (graph.star v).length := by decide

private theorem all_under_full_cap (fs : List (List D)) (h : graph.Accept fs) :
    ∀ w ∈ fs, w.length ≤ 2 * graph.edges := by
  intro w hw
  have lim := (List.sublist_flatten_of_mem hw).length_le
  have count := h.1.length_eq
  simpa [count, DartGraph.darts] using lim

/-- Contrast the sets of attainable face counts at the two cutoffs. -/
theorem exact_cap_obstruction :
    (∃ fs, graph.hogAtCap 54 6 = some fs) ∧
    (¬ ∃ fs, graph.hogAtCap 27 6 = some fs) ∧
    (∃ fs, graph.hogAtCap 27 4 = some fs) := by
  refine ⟨(graph.hogAtCap_iff degree_two_or_more 54 6).mpr
    ⟨faces 1170, witnesses.1.1, witnesses.1.2, all_under_full_cap _ witnesses.1.1⟩, ?_, ?_⟩
  · intro run
    obtain ⟨fs, h, n, b⟩ := (graph.hogAtCap_iff degree_two_or_more 27 6).mp run
    have bound := capped_bound h b
    omega
  · exact (graph.hogAtCap_iff degree_two_or_more 27 4).mpr ⟨faces 0, witnesses.2⟩

theorem genus_of_witnesses : graph.eulerGenus (faces 1170) = 1 ∧
    graph.eulerGenus (faces 0) = 2 := by
  change (2 + (27 : Int) - 21 - ((faces 1170).length : Int)) / 2 = 1 ∧
    (2 + (27 : Int) - 21 - ((faces 0).length : Int)) / 2 = 2
  rw [witnesses.1.2, witnesses.2.2.1]
  decide

/-- Each number above is the minimum of its respective search domain. -/
theorem optimal_genera {fs : List (List D)} (h : graph.Accept fs) :
    1 ≤ graph.eulerGenus fs ∧
    ((∀ w ∈ fs, w.length ≤ graph.edges) → 2 ≤ graph.eulerGenus fs) := by
  have bound := (all_fittings h).1
  change 1 ≤ (8 - (fs.length : Int)) / 2 ∧
    ((∀ w ∈ fs, w.length ≤ graph.edges) → 2 ≤ (8 - (fs.length : Int)) / 2)
  constructor
  · omega
  · intro cap
    have b := capped_bound h cap
    omega

end Page.FaceCap
