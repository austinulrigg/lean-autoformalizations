import Page.HoGBlocks

open Page.HoG

/- Enumerate every connected, labelled, simple graph on 1..5 vertices,
with edges inserted in both lexicographic and reverse lexicographic order. -/
def casesFor (n : Nat) : IO Unit := do
  let vertices := List.range n
  let edges := vertices.flatMap fun u => (vertices.filter (u < ·)).map (u, ·)
  for mask in List.range (2 ^ edges.length) do
    let chosen := edges.zipIdx.filterMap fun (e, i) =>
      if mask.testBit i then some e else none
    for order in [0, 1] do
      let es := if order == 0 then chosen else chosen.reverse
      let g := vertices.map fun u =>
        es.filterMap fun (a, b) =>
          if a == u then some b else if b == u then some a else none
      if connectedOn g vertices then
        unless auditDecomposition g do
          throw (IO.userError s!"Definition-based check failed at {n}, {mask}, {order}")
        let some b := bridgeDFS g | throw (IO.userError "Bridge DFS failed")
        let some bs := nontrivialBlocks g | throw (IO.userError "Block DFS failed")
        IO.println s!"[{n},{mask},{order},{if b then 1 else 0},{bs.map compactBlock}]"

def main : IO Unit := do
  for n in [1, 2, 3, 4, 5] do casesFor n
