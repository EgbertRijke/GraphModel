import init types graphmodel

open is_trunc eq sigma sigma.ops equiv is_equiv function sum

namespace diagram
  
  universe u

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

--AZ:class?
  structure is_diagram {Γ : graph.ctx} (A : graph.fam Γ) : Type :=
    ( witness :  Π {i j : graph.ctx.pts Γ} (e : graph.ctx.edg Γ i j) (x : graph.fam.pts A i), 
                   is_contr (Σ (y : graph.fam.pts A j), graph.fam.edg A e x y))

  definition diagram_fam_from_graph_fam_from_is_diagram {Γ : graph.ctx} : 
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

  definition diagram_tm_from_graph_tm_from_is_diagram {Γ : graph.ctx} (A : graph.fam Γ) (H : is_diagram A) :
    graph.tm A → diagram.tm (diagram_fam_from_graph_fam_from_is_diagram A H) :=
    begin
      intro t,
      unfold diagram_fam_from_graph_fam_from_is_diagram,
      unfold diagram_ctx_from_graph_ctx,
      fapply diagram.tm.mk; esimp,
        exact graph.tm.pts t,
      esimp,
      intros i j e,
      assert K : ⟨graph.tm.pts t j, e⟩.1 = graph.tm.pts t j,
      reflexivity,
      refine _ ⬝ K,
      refine @sigma.eq_pr1 _ _ _ _ _,
      
 --     fapply @sigma.eq_pr1 _ _ (@center (sigma (graph.fam.edg A e (graph.tm.pts t i) _ ))) (dpair (graph.tm.pts t j) (graph.tm.edg t e)) _,
--      refine eq.ap01 (@sigma.pr1 (graph.fam.pts A j) (graph.fam.edg A e (graph.tm.pts t i))) _,
 --     fapply diagram.tm.mk,
 --     intro i,
    end
  
----------------------------------------------------------------------------------------------------
