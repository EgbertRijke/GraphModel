/-
Title: The graph model of type theory.
Author: Egbert Rijke
Copyright: Apache 2.0
Year: 2016

This document is part of the GraphModel project, see
  
  https://github.com/EgbertRijke/GraphModel.git

for the licence.
-/

import types

open sigma sigma.ops eq pi 

-- We fix a universe, because lean makes a mess when we allow it to assign
-- universes freely, and I don't know how to deal with that otherwise.
universe u

/-
We formalize basic aspects of the graph model of type theory. In particular, we
formalize
- The basic structure of type dependence. So we have graphs, families of graphs
  and their terms. We have weakening and substitution and identity.
- We define Pi-types, Id-types and W-types in the graph model

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



namespace graph 

----------------------------------------------------------------------------------------------------
  --= CONTEXTS =--

  namespace ctx
    -- We define the ingredients of a context in the graph model

    definition ty_pts : Type := Type.{u}

    definition ty_edg : ty_pts → Type := λ V, V → V → Type.{u}
  end ctx

  -- introduction of contexts
  structure ctx : Type :=
    ( pts : ctx.ty_pts )
    ( edg : ctx.ty_edg pts)

  namespace ctx
    -- equality of contexts
    definition eq {Δ Γ : ctx} : 
      Π (p : ctx.pts Δ = ctx.pts Γ), (ctx.edg Δ) =[p] ctx.edg Γ → Δ = Γ :=
    begin
      induction Δ with Δ.pts Δ.edg,
      induction Γ with Γ.pts Γ.edg,
      esimp,
      intro p q,
      induction q,
      reflexivity
    end
  end ctx

----------------------------------------------------------------------------------------------------
  --= FAMILIES =--

  namespace fam
    variable (Γ : ctx)

    include Γ

    definition ty_pts : Type := ctx.pts Γ → Type.{u}

    definition ty_edg : ty_pts Γ → Type :=
      λ V, Π ⦃i j : ctx.pts Γ⦄, ctx.edg Γ i j → V i → V j → Type.{u}
  end fam
  
  -- introduction of families
  structure fam (Γ : ctx) : Type :=
    ( pts : fam.ty_pts Γ)
    ( edg : fam.ty_edg Γ pts)

  namespace fam
    -- equality of families
    definition eq {Γ : ctx} (A B : fam Γ) :
      Π ( p : fam.pts A = fam.pts B), fam.edg A =[p] fam.edg B → A = B :=
    begin
      induction A with A.pts A.edg,
      induction B with B.pts B.edg,
      esimp,
      intro p q,
      induction q,
      reflexivity
    end
  end fam

----------------------------------------------------------------------------------------------------
  --= TERMS =--

  namespace tm
    -- We define the basic ingredients of terms in the graph model
    variables {Γ : ctx} (A : fam Γ)

    include A

    definition ty_pts : Type :=
      Π (i : ctx.pts Γ), fam.pts A i

    definition ty_edg : ty_pts A → Type :=
      λ pt, Π ⦃i j : ctx.pts Γ⦄ (e : ctx.edg Γ i j), fam.edg A e (pt i) (pt j)

  end tm

  -- introduction of terms
  structure tm {Γ : ctx} (A : fam Γ) : Type :=
    ( pts : tm.ty_pts A)
    ( edg : tm.ty_edg A pts)
  
  namespace tm
    -- equality of terms
    definition eq {Γ : ctx} {A : fam Γ} {t1 t2 : tm A} : 
      Π ( p : tm.pts t1 = tm.pts t2 ), (tm.edg t1) =[p] tm.edg t2 → t1 = t2 :=
    begin
      induction t1 with t1.pts t1.edg,
      induction t2 with t2.pts t2.edg,
      esimp,
      intro p q,
      induction q,
      reflexivity 
    end
  end tm

----------------------------------------------------------------------------------------------------
  --= CONTEXT EXTENSION =--

  namespace ext
    -- We define the basic ingredients of context extension
    variables (Γ : ctx) (A : fam Γ)

    structure pts : Type :=
      ( in_ctx : ctx.pts Γ)
      ( in_fam : @fam.pts Γ A in_ctx)

    structure edg (a b : pts Γ A) : Type :=
      ( in_ctx : ctx.edg Γ (pts.in_ctx a) (pts.in_ctx b))
      ( in_fam : fam.edg A in_ctx (pts.in_fam a) (pts.in_fam b))
   
  end ext

  -- introduction of context extension
  definition ext (Γ : ctx) (A : fam Γ) : ctx :=
    ctx.mk (ext.pts Γ A) (ext.edg Γ A)

----------------------------------------------------------------------------------------------------
  --= WEAKENING =--

  namespace wk
    -- This namespace contains the ingredients of weakening.

    variables {Γ : ctx} (A B : fam Γ)

    definition pts : ctx.pts (ext Γ A) → Type :=
      λ p, fam.pts B (ext.pts.in_ctx p)

    definition edg : Π {p q : ctx.pts (ext Γ A)}, ctx.edg (ext Γ A) p q → pts A B p → pts A B q → Type :=
      λ p q e, fam.edg B (ext.edg.in_ctx e)
  end wk

  definition wk {Γ : ctx} (A B : fam Γ) : fam (ext Γ A) :=
    fam.mk _ (@wk.edg _ A B)

----------------------------------------------------------------------------------------------------
  --= SUBSTITUTION =--

  namespace subst
    -- This namespace contains the ingredients for substitution

    variables {Γ : ctx} {A : fam Γ}

    definition pts (t : tm A) (P : fam (ext Γ A)) : ctx.pts Γ → Type.{u} :=
      λ i, fam.pts P (ext.pts.mk _ (tm.pts t i))

    definition edg (t : tm A) (P : fam (ext Γ A)) : Π {i j : ctx.pts Γ}, ctx.edg Γ i j → pts t P i → pts t P j → Type :=
      λ i j e, fam.edg P (ext.edg.mk _ (tm.edg t e))
  end subst

  definition subst {Γ : ctx} {A : fam Γ} (t : tm A) (P : fam (ext Γ A)) : fam Γ :=
    fam.mk _ (@subst.edg _ _ t P)

----------------------------------------------------------------------------------------------------
  --= DEPENDENT FUNCTION TYPES =--

  /-
  In the following we implement dependent function types in the graph model. 
  - We introduce `prd A P` for any family `P` over `ext Γ A`
  - We define lambda-abstract and evaluation
  - We show that lambda-abstraction and evaluation are mutual inverses.
  With these three ingredients we have implemented dependent product types satisfying the eta-rule.
  -/

  namespace prd
    -- This namespace contains the ingredients for dependent function graphs

    variables {Γ : ctx} (A : fam Γ) (P : fam (ext Γ A))

    include A P

    definition pts : ctx.pts Γ → Type :=
      λ i, Π (x : fam.pts A i), fam.pts P (ext.pts.mk i x)

    definition edg : Π {i j : ctx.pts Γ}, ctx.edg Γ i j → pts A P i → pts A P j → Type.{u} :=
      λ i j e f g, Π {x : fam.pts A i} {y : fam.pts A j} (s : fam.edg A e x y), fam.edg P (ext.edg.mk e s) (f x) (g y)
  end prd

  -- introduce dependent function types
  definition prd {Γ : ctx} (A : fam Γ) (P : fam (ext Γ A)) : fam Γ :=
    fam.mk _ (@prd.edg _ A P)

  -- lambda-abstraction for dependent function types
  definition abstr [unfold 4] {Γ : ctx} {A : fam Γ} {P : fam (ext Γ A)} : tm P → tm (prd A P) :=
  begin
    intro f,
    fapply tm.mk,
    intro i x,
    exact tm.pts f (ext.pts.mk i x),
    intro i j e x y s,
    exact tm.edg f (ext.edg.mk e s)
  end

  -- evaluation
  definition evl [unfold 4] {Γ : ctx} {A : fam Γ} {P : fam (ext Γ A)} : tm (prd A P) → tm P :=
  begin
    intro g,
    fapply tm.mk,
    intro p,
    induction p with i x,
    exact tm.pts g i x,
    intro p q s,
    induction p with i x,
    induction q with j y,
    induction s with e s,
    exact tm.edg g e x y s
  end

  namespace is_equiv_abstr
    variables {Γ : ctx} {A : fam Γ} (P : fam (ext Γ A))

    include P

    definition beta.pts [unfold 4] (f : tm P) : tm.pts (evl (abstr f)) = tm.pts f :=
    begin
      induction f with f.pts f.edg, esimp,
      apply eq_of_homotopy,
      intro p, induction p with i x, 
      reflexivity
    end

    print eq_of_homotopy

    definition beta (f : tm P) : evl (abstr f) = f :=
    begin
      fapply tm.eq,
      exact beta.pts P f,
      apply pi_pathover_constant,
      intro p, induction p with i x,
      induction f with f.pts f.edg,
      esimp,
      apply pi_pathover_constant,
      intro q, induction q with j y,
      esimp,
      apply pi_pathover_constant,
      intro s; induction s with e s,
      esimp at e,
      esimp at s,
      esimp,
--      assert K : eq_of_homotopy (ext.pts.rec (λ (i : ctx.pts Γ) (x : fam.pts A i), refl (f.pts (ext.pts.mk i x)))) = idpath (λ (i x), f.pts (ext.pts.mk i x)),
--      from eq_of_homotopy (λ (i : ctx.pts Γ) (x : fam.pts A i), refl (refl (f.pts (ext.pts.mk i x)))),
      exact sorry
    end 
  end is_equiv_abstr

  check is_equiv_abstr.beta
  definition is_equiv_abstr {Γ : ctx} {A : fam Γ} (P : fam (ext Γ A)) : is_equiv (@abstr _ _ P) :=
  begin
    fapply is_equiv.adjointify;
    repeat (exact sorry),
  end 
    
----------------------------------------------------------------------------------------------------
  --= GRAPH HOMOMORPHISMS =--

  /-
    Introduction of graph homomorphisms. A graph homomorphism from Δ to Γ is the same thing as
    a term of the weakened graph ⟨Δ⟩Γ.
  -/ 
  structure hom (Δ Γ : ctx) : Type :=
    ( pts : ctx.pts Δ → ctx.pts Γ)
    ( edg : Π (i j : ctx.pts Δ), ctx.edg Δ i j → ctx.edg Γ (pts i) (pts j)) 

  -- introduction of the slice over Γ
  structure slice (Γ : ctx) : Type :=
    ( domain : graph.ctx)
    ( mor : graph.hom domain Γ)

    namespace proj₁ 
    -- We define the basic ingredients of the projections
    definition pts (Γ : ctx) (A : fam Γ) : ctx.pts (ext Γ A) → ctx.pts Γ :=
      ext.pts.in_ctx
    
    definition edg (Γ : ctx) (A : fam Γ) (a b : ctx.pts (ext Γ A)) : 
      ctx.edg (ext Γ A) a b → ctx.edg Γ (pts Γ A a) (pts Γ A b) :=
      ext.edg.in_ctx

  end proj₁

  definition proj₁ (Γ : ctx) (A : fam Γ) : hom (ext Γ A) Γ :=
    hom.mk _ (proj₁.edg Γ A)

  definition slice_from_fam (Γ : ctx) : fam Γ → slice Γ :=
    λ A, slice.mk _ (proj₁ Γ A)

----------------------------------------------------------------------------------------------------

end graph

