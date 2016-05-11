import types

open eq funext

universe u

namespace model

  structure base : Type :=
      -- contexts
    ( ctx : Type.{u})
      -- dependent structures
    ( fam : ctx → Type.{u})
      -- terms
    ( tm  : Π ⦃Γ : ctx⦄, fam Γ → Type.{u})

  structure hom_base (AA BB : base) : Type :=
      -- action on contexts
    ( action_ctx : base.ctx AA → base.ctx BB)
      -- action on dependent structures
    ( action_fam : Π ⦃Γ : base.ctx AA⦄, base.fam AA Γ → base.fam BB (action_ctx Γ))
      -- action on terms
    ( action_tm  : Π ⦃Γ : base.ctx AA⦄ ⦃A : base.fam AA Γ⦄, base.tm AA A → base.tm BB (action_fam A))

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

  structure prehom_ebase (AA BB : ebase) extends hom_base AA BB :=
      -- preservation of context extension
    ( pres_ctxext : Π (Γ : base.ctx AA) (A : base.fam AA Γ), action_ctx (ebase.ctxext AA Γ A) = ebase.ctxext BB (action_ctx Γ) (action_fam A))
      -- preservation of family extension
    ( pres_famext : Π ⦃Γ : base.ctx AA⦄ (A : base.fam AA Γ) (P : base.fam AA (ebase.ctxext AA Γ A)), action_fam (ebase.famext AA A P) = ebase.famext BB (action_fam A) ((pres_ctxext Γ A) ▸ (action_fam P)))
      -- preservation of the empty structure
    ( pres_empstr : Π (Γ : base.ctx AA), action_fam (ebase.empstr AA Γ) = ebase.empstr BB (action_ctx Γ))

    -- In the following structure we use function extensionality to express 
    -- preservation of associativity conveniently. It should
    -- be noted that there probably is a workaround to this, involving more
    -- complicated expressions.
  structure hom_ebase (AA BB : ebase) extends prehom_ebase AA BB :=
      -- preservation of c_assoc
    ( pres_c_assoc : Π (Γ : base.ctx AA) (A : base.fam AA Γ) (P : base.fam AA (ebase.ctxext AA Γ A)), 
        @pathover 
            -- base type 
          ( Π (XX : ebase) (Γ' : ebase.ctx XX) (A' : ebase.fam XX Γ'), 
              ebase.fam XX (ebase.ctxext XX Γ' A') → ebase.ctx XX)
            -- base point domain
          ( λ XX Γ' A' P', ebase.ctxext XX (ebase.ctxext XX Γ' A') P')
            -- family
          ( λ e, action_ctx (e AA Γ A P) = e BB (action_ctx Γ) (action_fam A) ((pres_ctxext Γ A) ▸ (action_fam P))
            -- fiber point domain
          ( (pres_ctxext (ebase.ctxext Γ A) P) ⬝ _ )
            -- base point codomain
          ( λ XX Γ' A' P', ebase.ctxext XX Γ' (ebase.famext XX A' P'))
            -- base path
          ( eq_of_homotopy (λ (XX : ebase), eq_of_homotopy3 (ebase.c_assoc XX)))
            -- fiber point codomain
          ( (pres_ctxext Γ (ebase.famext A P)) ⬝ _ )
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
