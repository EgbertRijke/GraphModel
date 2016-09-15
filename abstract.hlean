import types

open eq funext

universe variable u

    -- We attempt to formalize a weak notion of model of type theory using only homotopy-invariant tools. We have two examples in mind: 
    -- - it should be possible to obtain such a model from a univalent universe,
    -- - given a univalent universe, there should be a model or (reflexive) graphs.
    --
    -- It turns out that what we formalize here is a theory of structures and dependent structures, containing all the ways in which one could manipulate these. From another point of view, this is a theory of contexts and dependent contexts. It is a direct generalization of Cartmell's contextual categories, which were reformulated as C-systems and B-systems by Voevodsky. The weak notion of model we formalize here is a homotopified notion of E-system, which was developed by the author. B-systems form a subcategory of E-systems, for which the inclusion functor is full and faithful.

namespace model
    
    -- The base structure of a model consists of 
    -- - a type of contexts, 
    -- - a family of dependent stuctures over the type of contexts,
    -- - a family of terms of dependent structures
    -- In other words, it looks like
    --
    --     base.tm ---->> base.fam ---->> base.ctx.

  structure base : Type :=
      -- contexts
    ( ctx : Type.{u})
      -- dependent structures
    ( fam : ctx → Type.{u})
      -- terms
    ( tm  : Π ⦃Γ : ctx⦄, fam Γ → Type.{u})

    -- A homomorphism of bases, is simply a three-fold map sending
    -- - the contexts to the contexts,
    -- - the dependent structures to the dependent structures
    -- - the terms to the terms
    -- In a diagram, a homomorphism of bases can be indicated as
    --
    --    base.tm AA  -----> base.tm BB
    --      |                  |
    --      |                  |
    --      V                  V
    --    base.fam AA -----> base.fam BB
    --      |                  |
    --      |                  |
    --      V                  V
    --    base.ctx AA -----> base.ctx BB

  structure hom_base (AA BB : base) : Type :=
      -- action on contexts
    ( action_ctx : base.ctx AA → base.ctx BB)
      -- action on dependent structures
    ( action_fam : Π ⦃Γ : base.ctx AA⦄, base.fam AA Γ → base.fam BB (action_ctx Γ))
      -- action on terms
    ( action_tm  : Π ⦃Γ : base.ctx AA⦄ ⦃A : base.fam AA Γ⦄, base.tm AA A → base.tm BB (action_fam A))

    -- We now extend the notion of base to the notion of extension base, by adding
    -- - context extension
    -- - family extension
    -- - an empty structure, which is a right unit for context extension and a unit (both left and right) for family extension,
    -- - associativity for context extension and family extension
    -- We do not (yet) require further coherence laws for associativity.
    --
    -- Note that the equations are formulated as equations between dependent functions, as opposed to families of equations. This makes it slightly easier, in my experience, to formulate the requirement that these equations should be preserved, in the formalization of later aspects of models of type theory.

  structure ebase extends base :=
      -- context extension
    ( ctxext : Π (Γ : ctx), fam Γ → ctx)
      -- family extension
    ( famext : Π ⦃Γ : ctx⦄ (A : fam Γ), fam (ctxext Γ A) → fam Γ)
      -- empty structure
    ( empstr : Π (Γ : ctx), fam Γ)
      -- context extension is associative
    ( c_assoc : (λ Γ A P, ctxext (ctxext Γ A) P) = (λ Γ A P, ctxext Γ (famext A P)))
      -- family extension is associative
    ( f_assoc : pathover 
                  ( λ (e : Π {Γ : ctx} (A : fam Γ), fam (ctxext Γ A) → ctx), 
                      Π {Γ : ctx} (A : fam Γ) (P: fam (ctxext Γ A)), fam (e A P) → fam Γ)
                  ( λ Γ A P (Q : fam (ctxext (ctxext Γ A) P)), famext A (famext P Q))
                  ( c_assoc)
                  ( λ Γ A P (Q' : fam (ctxext Γ (famext A P))), famext (famext A P) Q')) 
      -- the empty structure is neutral for context extension
    ( c_unit  : (λ (Γ : ctx), Γ) = (λ Γ, ctxext Γ (empstr Γ)))
      -- the empty structure is neutral for family extension from the left
    ( f_unit_left : pathover
                      ( λ (e : ctx → ctx), Π {Γ : ctx}, fam (e Γ) → fam Γ)
                      ( λ Γ A, A )
                      ( c_unit)
                      ( λ Γ A', famext (empstr Γ) A'))
      -- the empty structure is neutral for family extension from the right
    ( f_unit_right : (λ Γ A, famext A (empstr (ctxext Γ A))) = (λ Γ A, A))

  open ebase
    -- We open the name space ebase, so that we can freely use its ingredients.

    -- A pre-homomorphism of ebases is a homomorphism which preserves the operations of context extension, family extension and the empty structure. However, a pre-homomorphism of ebases is not yet required to preserve the further equations in the structure of an ebase. This requires a more elaborate formalization, in which it is useful to have the auxilary notion of pre-homomorphism of ebases available.

  structure prehom_ebase (AA BB : ebase) extends hom_base AA BB :=
      -- preservation of context extension
    ( pres_ctxext : 
        Π (Γ : ctx AA) (A : fam AA Γ), 
          action_ctx (ctxext AA Γ A) = ctxext BB (action_ctx Γ) (action_fam A))
      -- preservation of family extension
    ( pres_famext : 
        Π ⦃Γ : ctx AA⦄ (A : fam AA Γ) (P : fam AA (ctxext AA Γ A)), 
          action_fam (famext AA A P) = famext BB (action_fam A) ((pres_ctxext Γ A) ▸ (action_fam P)))
      -- preservation of the empty structure
    ( pres_empstr : Π (Γ : ctx AA), action_fam (empstr AA Γ) = empstr BB (action_ctx Γ))

  -- Our current goal is to formalize what it means for a pre-homomorphism of 

  open prehom_ebase

    -- Note that, if Δ and Γ are equal contexts, and P is a dependent structure over Δ, then we can transport P along the equality p : Δ = Γ. This results in a dependent structure p ▸ P over Γ. In the following definition, we formalize that ctxext Δ P and ctxext Γ (p ▸ P) are again equal contexts, in this situation.

  definition pres_ext_c_1c_aux (BB : ebase) :
    Π (Δ Γ : ctx BB) (p : Δ = Γ) (P : fam BB Δ), ctxext BB Δ P = ctxext BB Γ (p ▸ P) :=
  begin
    intros Δ Γ p,
    induction p,
    intro P, reflexivity
  end

    -- In the following definition we formalize what it means for a pre-homomorphism of ebases to preserve 
  definition pres_ext_c_1c {AA BB : ebase} (f : prehom_ebase AA BB) :
    Π (Γ : ctx AA) (A : fam AA Γ) (P : fam AA (ctxext AA Γ A)), 
      action_ctx f (ctxext AA (ctxext AA Γ A) P) 
        = 
      ctxext BB (ctxext BB (action_ctx f Γ) (action_fam f A)) ( (pres_ctxext f Γ A) ▸ (action_fam f P)) :=
  begin
    intros Γ A P,
    refine (pres_ctxext f (ctxext AA Γ A) P) ⬝ _,
    apply pres_ext_c_1c_aux BB 
  end

  definition pres_ext_c_2f {AA BB : ebase} (f : prehom_ebase AA BB) :
    Π (Γ : ctx AA) (A : fam AA Γ) (P : fam AA (ctxext AA Γ A)),
      action_ctx f (ctxext AA Γ (famext AA A P))
        =
      ctxext BB (action_ctx f Γ) (famext BB (action_fam f A) ((pres_ctxext f Γ A) ▸ (action_fam f P))) :=
  begin
    intros Γ A P,
    exact (pres_ctxext f Γ (famext AA A P)) ⬝ (ap (ctxext BB (action_ctx f Γ)) (pres_famext f A P))
  end

    -- In the following structure we extend the notion of pre-homomorphism of extension bases to the notion of homomorphism of extension bases. In other words, we formalize the conditions that a pre-homomorphism of extension bases preserves the equalities that are part of the structure of extension bases. 
    --
    -- We use function extensionality to express preservation of associativity conveniently.

  structure hom_ebase (AA BB : ebase) extends prehom_ebase AA BB :=
      -- preservation of c_assoc
    ( pres_c_assoc : 
        pathover
          ( λ (e : Π (XX : ebase) (Γ : ctx XX) (A : fam XX Γ), fam XX (ctxext XX Γ A) → ctx XX),
              Π (Γ : ctx AA) (A : fam AA Γ) (P : fam AA (ctxext AA Γ A)),
                action_ctx (e AA Γ A P) = e BB (action_ctx Γ) (action_fam A) ((pres_ctxext Γ A) ▸ action_fam P))
          ( pres_ext_c_1c ⦃ prehom_ebase, 
                              action_ctx  := action_ctx, 
                              action_fam  := action_fam, 
                              action_tm   := action_tm, 
                              pres_ctxext := pres_ctxext, 
                              pres_famext := pres_famext, 
                              pres_empstr := pres_empstr 
                          ⦄ )
          ( eq_of_homotopy c_assoc)
          ( pres_ext_c_2f ⦃ prehom_ebase, 
                              action_ctx  := action_ctx, 
                              action_fam  := action_fam, 
                              action_tm   := action_tm, 
                              pres_ctxext := pres_ctxext, 
                              pres_famext := pres_famext, 
                              pres_empstr := pres_empstr 
                          ⦄ ) 
    ) --there should be a better way to do this.

  print hom_ebase

/-    Π (Γ : base.ctx AA) (A : base.fam AA Γ) (P : base.fam AA (ebase.ctxext AA Γ A)), 
        @pathover 
            -- base type 
          ( Π (XX : ebase) (Γ' : ebase.ctx XX) (A' : ebase.fam XX Γ'), 
              ebase.fam XX (ebase.ctxext XX Γ' A') → ebase.ctx XX)
            -- base point domain
          ( λ XX Γ' A' P', ebase.ctxext XX (ebase.ctxext XX Γ' A') P')
            -- family
          ( λ e, action_ctx (e AA Γ A P) = e BB (action_ctx Γ) (action_fam A) ((pres_ctxext Γ A) ▸ (action_fam P)))
            -- fiber point domain
          ( (pres_ctxext (ctxext Γ A) P) ⬝ _ )
            -- base point codomain
          ( λ XX Γ' A' P', ebase.ctxext XX Γ' (ebase.famext XX A' P'))
            -- base path
          ( eq_of_homotopy (λ (XX : ebase), eq_of_homotopy3 (ebase.c_assoc XX)))
            -- fiber point codomain
          ( (pres_ctxext Γ (ebase.famext A P)) ⬝ _ ))
-/

      -- preservation of f_assoc
    ( pres_f_assoc : Π ⦃Γ : base.ctx AA⦄ (A : base.fam AA Γ) (P : base.fam AA (ebase.ctxext AA Γ A)) (Q : base.fam AA (ebase.ctxext AA (ebase.ctxext AA Γ A) P)), ap (action_fam (ebase.f_assoc AA A P Q)) = ebase.f_assoc BB (action_fam A) ((pres_ctxext Γ A) ▸ P) (Q) )

  definition slice_base (AA : ebase) (Γ : base.ctx AA) : ebase :=
  begin
    fapply ebase.mk,
      -- contexts
    exact base.fam AA Γ,
      -- dependent structures
    intro A,
    exact ebase.fam AA (ebase.ctxext AA Γ A),
      -- terms
    intros A P,
    exact base.tm AA P,
    repeat exact sorry
  end

  definition slice_ext (AA : base) (ee : is_pre_ebase AA) (Γ : base.ctx AA) : hom_base (slice_base AA ee Γ) AA :=
  begin
    fapply hom_base.mk,
      -- action  on contexts (is context extension)
    intro A,
    exact is_pre_ebase.ctxext ee Γ A,
      -- action on dependent structures (is identity)
    intro A P,
    exact P,
      -- action on terms (is identity)
    intro A P f,
    exact f,
  end    

  structure is_ebase (AA : base) (ee : is_pre_ebase AA) : Type :=
    ( is_hom_ctxext : Π (Γ : base.ctx AA), is_hom_pre_ebase (slice_ext AA ee Γ))

  structure prewk extends ext :=
    ( wkctx : Π ⦃Γ : ctx⦄ (A : fam Γ), fam Γ → fam (ctxext Γ A))
    ( fam : Π ⦃Γ : trunk.ctx⦄ (A : fam Γ) (B : fam Γ), fam (ext.ctx Γ B) → fam (ext.ctx (ext.ctx Γ A) (ctx A B)))
    ( tm  : Π ⦃Γ : trunc.ctx⦄ (A : fam Γ) (B : fam Γ) (Q : fam (ext.ctx Γ B)), 
end model
