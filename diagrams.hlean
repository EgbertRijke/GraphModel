import types graphmodel

open is_trunc eq sigma sigma.ops equiv is_equiv function sum graph

namespace diagram

  structure ctx extends graph.ctx

  structure fam (Γ : ctx) : Type :=
    ( pts : ctx.pts Γ → Type.{u} )
    ( edg : Π {i j : ctx.pts Γ}, (ctx.edg Γ i j) → pts i → pts j)

  structure tm {Γ : ctx} (A : fam Γ) : Type :=
    ( pts : Π (i : ctx.pts Γ), fam.pts A i )
    ( edg : Π {i j : ctx.pts Γ} (e : ctx.edg Γ i j), fam.edg A e (pts i) = pts j )

end diagram

  definition diagram_ctx_from_graph_ctx : graph.ctx → diagram.ctx :=
     λ Γ, diagram.ctx.mk _ (graph.ctx.edg Γ)

  structure is_diagram [class] {Γ : graph.ctx} (A : graph.fam Γ) : Type :=
    ( witness :  Π {i j : graph.ctx.pts Γ} (e : graph.ctx.edg Γ i j) (x : graph.fam.pts A i), 
                   is_contr (Σ (y : graph.fam.pts A j), graph.fam.edg A e x y))

  attribute is_diagram.witness [instance]

  definition diagram_fam_from_graph_fam_from_is_diagram {Γ : graph.ctx} : 
    Π (A : graph.fam Γ), is_diagram A → diagram.fam (diagram_ctx_from_graph_ctx Γ) := 
    begin
      intros A H,
      fapply diagram.fam.mk,
      exact (@graph.fam.pts Γ A),
      intros i j e x,
      refine sigma.pr1 (@is_trunc.center (sigma (graph.fam.edg A e x)) _),
      exact is_diagram.witness e x
    end

  namespace diagram_tm_from_graph_tm_from_is_diagram
    variables {Γ : graph.ctx} {A : graph.fam Γ} [is_diagram A] (t : graph.tm A)

    definition pts : Π (i : ctx.pts Γ), fam.pts A i := 
      graph.tm.pts t

    definition eq : Π {i j : ctx.pts Γ} (e : ctx.edg Γ i j),
      (center (Σ (a : fam.pts A j), fam.edg A e (tm.pts t i) a)).1 = tm.pts t j :=
    begin
      intros i j e,
      have p : center _ = dpair (tm.pts t j) (tm.edg t e),
      from !center_eq,
      exact ap pr1 p,
    end 

  end diagram_tm_from_graph_tm_from_is_diagram

  definition diagram_tm_from_graph_tm_from_is_diagram 
    {Γ : graph.ctx} (A : graph.fam Γ) [H : is_diagram A] :
    graph.tm A → diagram.tm (diagram_fam_from_graph_fam_from_is_diagram A H) :=
    begin
      intro t,
      fapply diagram.tm.mk,
      intro i,
      exact diagram_tm_from_graph_tm_from_is_diagram.pts t i,
      intro i j e,
      exact diagram_tm_from_graph_tm_from_is_diagram.eq t e,
    end
  
----------------------------------------------------------------------------------------------------
