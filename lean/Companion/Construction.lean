import Companion.Data

namespace Companion

private def row (vs : List Nat) (rhs := false) : Equation := ⟨vs, rhs⟩

/-- The four steps of Appendix B, with zero-based variable numbers and with
the single non-involutive generator removed as `p = f v`.
Variable roles are encoded by their disjoint numeric offsets. -/
def construct (p : Presentation) : Game := Id.run do
  let n := p.n0 + p.c1.length + 4
  let f := p.n0
  let v := p.n0 + 1
  let ts := p.n0 + p.c1.length + 2
  let u := ts + 1
  let conj := p.c0 ++ (p.c1.zipIdx).flatMap (fun ((b,c),j) =>
    [(v,b,p.n0+2+j), (f,p.n0+2+j,c)]) ++ [(ts,p.distinguished,u)]
  let prime := fun a => n + a
  let dprime := fun a => 2*n + a
  let gs := 3*n
  let bar := fun a => 3*n+1+a
  let nice := (List.range n).map (fun a => (gs,prime a,dprime a)) ++
    conj.flatMap (fun (a,b,c) => [(bar a,prime b,dprime c), (bar a,dprime b,prime c)])
  let linear := p.linear.map (fun vs => row vs) ++ [row [p.distinguished,u] true] ++
    (List.range n).flatMap (fun a => [row [a,prime a,dprime a], row [a,gs,bar a]]) ++
    conj.zipIdx.flatMap (fun ((_,b,c),j) =>
      [row [prime b,dprime c,4*n+1+2*j], row [prime c,dprime b,4*n+2+2*j]])
  let base := 4*n+1+2*conj.length
  let gadgets := nice.zipIdx.flatMap (fun ((a,b,c),j) =>
    let y := fun k => base+7*j+k
    [row [a,y 0,y 1], row [b,y 1,y 2], row [y 2,y 3,y 4],
     row [a,y 4,y 5], row [c,y 5,y 6], row [y 0,y 3,y 6]])
  return ⟨base+7*nice.length,linear++gadgets⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- C3: exact equality of all variable indices and right-hand sides. -/
theorem construction_matches : construct inputPresentation = suppliedGame := by decide

def wellFormed (g : Game) : Bool := g.equations.all fun e =>
  decide (e.vars.length ≤ 3) && decide e.vars.Nodup && e.vars.all (· < g.n)

theorem game_dimensions : suppliedGame.n = 1993 ∧ suppliedGame.equations.length = 1687 := by decide
theorem game_wellFormed : wellFormed suppliedGame = true := by decide
theorem game_one_rhs : (suppliedGame.equations.filter (·.rhs)).length = 1 := by decide
theorem game_sorted : suppliedGame.equations.all (fun e => decide (e.vars.Pairwise (· < ·))) = true := by decide

/-- Source-presentation relators after the explicitly specified substitution
`g ↦ x_g`, `p ↦ x_f x_v`; the distinguished commutator is separate. -/
def substitutedRelators (p : Presentation) : List Word :=
  (List.range p.n0).map (fun g => [pos g,pos g]) ++
  p.linear.map (fun vs => vs.map pos) ++
  p.c0.map (fun (a,b,c) => [pos a,pos b,pos a,neg c]) ++
  p.c1.map (fun (b,c) => [pos p.n0,pos (p.n0+1),pos b,neg (p.n0+1),neg p.n0,neg c])

def distinguishedCommutator (p : Presentation) : Word :=
  let ts := p.n0+p.c1.length+2
  [pos p.distinguished,pos ts,neg p.distinguished,neg ts,pos (construct p).n]

end Companion
