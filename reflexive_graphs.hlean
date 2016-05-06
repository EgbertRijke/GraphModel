import graphmodel

namespace rgraph

structure ctx extends graph.ctx := 
  ( rfx : Π (i : pts), edg i i)

structure fam (Γ : ctx) extends graph.fam Γ :=
  ( rfx : Π (i : ctx.pts Γ) (x : pts i), edg (ctx.rfx Γ i) x x)

structure tm {Γ : ctx} (A : fam Γ) extends graph.tm A :=
  ( rfx : Π (i : ctx.pts Γ), fam.edg A (ctx.rfx Γ i) (pts i) (pts i))

end rgraph
