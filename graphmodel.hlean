/-
We formalize basic aspects of the graph model of type theory.

On the naming convention. 
- Everything in the graph model of type theory is in the namespace `graph`.
- Most structures will have a part about points, and a part about edges. 
  In their structures, they will be referred to by `pts` and `edg`. For example, 
  a graph is a context in the graph model, so its structure is called `graph.ctx`. 
  A graph consists of a type 
  
    `graph.ctx.pts` 

  and a type family 
  
    `graph.ctx.edg : graph.ctx.pts -> graph.ctx.pts -> Type`.
-/

import init

namespace graph 
  structure ctx : Type :=
    ( pts : Type.{0} )
    ( edg : pts → pts → Type.{0} )

  structure fam (Γ : ctx) : Type :=
    ( pts : ctx.pts Γ → Type.{0})
    ( edg : Π {i j : ctx.pts Γ}, ctx.edg Γ i j → pts i → pts j → Type.{0})

  structure tm {Γ : ctx} (A : fam Γ) : Type :=
    ( pts : Π (i : ctx.pts Γ), fam.pts A i)
    ( edg : Π {i j : ctx.pts Γ} (e : ctx.edg Γ i j) (x : fam.pts A i) (y : fam.pts A j), fam.edg A e x y)

  structure hom (Δ Γ : ctx) : Type :=
    ( pts : ctx.pts Δ → ctx.pts Γ)
    ( edg : Π (i j : ctx.pts Δ), ctx.edg Δ i j → ctx.edg Γ (pts i) (pts j)) 

  structure slice (Γ : ctx) : Type :=
    ( domain : graph.ctx)
    ( mor : graph.hom domain Γ)

  namespace ext
    variables (Γ : ctx) (A : fam Γ)

    structure pts : Type :=
      ( in_ctx : ctx.pts Γ)
      ( in_fam : @fam.pts Γ A in_ctx)

    structure edg (a b : pts Γ A) : Type :=
      ( in_ctx : ctx.edg Γ (pts.in_ctx a) (pts.in_ctx b))
      ( in_fam : fam.edg A in_ctx (pts.in_fam a) (pts.in_fam b))
   
  end ext

  definition ext (Γ : ctx) (A : fam Γ) : ctx :=
    ctx.mk (ext.pts Γ A) (ext.edg Γ A)

--  Why does the following definition not work?!
/-    
    begin
      fapply ctx.mk, 
      exact (ext.pts Γ A),
      exact (ext.edg Γ A)
    end
-/

  namespace proj₁ 
    definition pts (Γ : ctx) (A : fam Γ) : ctx.pts (ext Γ A) → ctx.pts Γ :=
      ext.pts.in_ctx
    
    definition edg (Γ : ctx) (A : fam Γ) (a b : ctx.pts (ext Γ A)) : ctx.edg (ext Γ A) a b → ctx.edg Γ (pts Γ A a) (pts Γ A b) :=
      ext.edg.in_ctx

  end proj₁

  definition proj₁ (Γ : ctx) (A : fam Γ) : hom (ext Γ A) Γ :=
    hom.mk _ (proj₁.edg Γ A)

  definition slice_from_fam (Γ : ctx) : fam Γ → slice Γ :=
    λ A, slice.mk _ (proj₁ Γ A)

end graph

