import init graphmodel

open equiv graph is_trunc prod prod.ops eq

namespace equifibered

  structure ctx extends graph.ctx 

  structure fam (Γ : ctx) : Type :=
    ( pts : ctx.pts Γ → Type.{0})
    ( edg : Π {i j : ctx.pts Γ}, ctx.edg Γ i j → (pts i ≃ pts j))

  structure tm {Γ : ctx} (E : fam Γ) : Type :=
    ( pts : Π (i : ctx.pts Γ), fam.pts E i)
    ( edg : Π {i j : ctx.pts Γ} (e : ctx.edg Γ i j), fam.edg E e (pts i) = pts j)

end equifibered

  -- we should show that the following function is an equivalence.
  definition equifibered_ctx_from_graph_ctx : graph.ctx → equifibered.ctx :=
    λ Γ, equifibered.ctx.mk _ (graph.ctx.edg Γ)

  definition is_equifibered {Γ : graph.ctx} (A : graph.fam Γ) : Type.{0} :=
    Π {i j : graph.ctx.pts Γ} (e : graph.ctx.edg Γ i j), 
      (Π (x : graph.fam.pts A i), is_contr (Σ (y : graph.fam.pts A j), graph.fam.edg A e x y))
        ×
      (Π (y : graph.fam.pts A j), is_contr (Σ (x : graph.fam.pts A i), graph.fam.edg A e x y))

/-
  definition equifibered_fam_from_graph_fam_which_is_equifibered (Γ : graph.ctx) : 
    Π (A : graph.fam Γ), is_equifibered A → equifibered.fam (equifibered_ctx_from_graph_ctx Γ) :=
  take A H, equifibered.fam.mk 
    (graph.fam.pts A) 
    ( begin 
        intros i j,
        unfold equifibered_ctx_from_graph_ctx,
        intro e,
        unfold is_equifibered at H,
        fapply equiv.mk,
        intro x,
        exact sigma.pr1 (@is_trunc.center (sigma (fam.edg A e x)) ((prod.ops.pr₁ (H e)) x)),
        fapply is_equiv.adjointify,
        exact λ y, sigma.pr1 (@is_trunc.center (Σ (x : fam.pts A i), fam.edg A e x y) ((prod.ops.pr₂ (H e)) y)),
        intro y,
        
      end
    )
-/
 
/-
  begin
    intros A H,
    fapply equifibered.fam.mk,
    unfold equifibered_ctx_from_graph_ctx,
    intro i,
    exact graph.fam.pts A i,
  end
-/
