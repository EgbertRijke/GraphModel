import init graphmodel

open is_trunc

namespace diagram

  structure ctx extends graph.ctx

  structure fam (Γ : ctx) : Type :=
    ( pts : ctx.pts Γ → Type.{0} )
    ( edg : Π {i j : ctx.pts Γ}, (ctx.edg Γ i j) → pts i → pts j)

  structure tm {Γ : ctx} (A : fam Γ) : Type :=
    ( pts : Π (i : ctx.pts Γ), fam.pts A i )
    ( edg : Π {i j : ctx.pts Γ} (e : ctx.edg Γ i j), fam.edg A e (pts i) = pts j )

end diagram

  definition diagram_ctx_from_graph_ctx : graph.ctx → diagram.ctx :=
     λ Γ, diagram.ctx.mk _ (graph.ctx.edg Γ)

--AZ:class?
  structure is_diagram {Γ : graph.ctx} (A : graph.fam Γ) : Type :=
    ( witness :  Π {i j : graph.ctx.pts Γ} (e : graph.ctx.edg Γ i j) (x : graph.fam.pts A i), 
                   is_contr (Σ (y : graph.fam.pts A j), graph.fam.edg A e x y))

  definition diagram_fam_from_graph_fam_which_is_diagram {Γ : graph.ctx} : 
    Π (A : graph.fam Γ), is_diagram A → diagram.fam (diagram_ctx_from_graph_ctx Γ) := 
    begin
      intros A H,
      fapply diagram.fam.mk,
      unfold diagram_ctx_from_graph_ctx,
      intro i,
      exact (@graph.fam.pts Γ A i),
      intros i j,
      unfold diagram_ctx_from_graph_ctx,
      intros e x,
      refine sigma.pr1 (@is_trunc.center (sigma (graph.fam.edg A e x)) _),
      exact is_diagram.witness H e x
    end
  
----------------------------------------------------------------------------------------------------
