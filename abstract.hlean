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
    ( ctx : base.ctx AA → base.ctx BB)
      -- action on dependent structures
    ( fam : Π ⦃Γ : base.ctx AA⦄, base.fam AA Γ → base.fam BB (ctx Γ))
      -- action on terms
    ( tm  : Π ⦃Γ : base.ctx AA⦄ ⦃A : base.fam AA Γ⦄, base.tm AA A → base.tm BB (fam A))

  structure is_pre_ebase (AA : base) : Type :=
      -- context extension
    ( ctxext : Π (Γ : base.ctx AA), base.fam AA Γ → base.ctx AA)
      -- family extension
    ( famext : Π ⦃Γ : base.ctx AA⦄ (A : base.fam AA Γ), base.fam AA (ctxext Γ A) → base.fam AA Γ)
      -- empty structure
    ( empstr : Π (Γ : base.ctx AA), base.fam AA Γ)

  structure is_hom_pre_ebase {AA BB : base} {ee : is_pre_ebase AA} {dd : is_pre_ebase BB} (f : hom_base AA BB) : Type :=
      -- preservation of context extension
    ( ctxext : Π (Γ : base.ctx AA) (A : base.fam AA Γ), hom_base.ctx f (is_pre_ebase.ctxext ee Γ A) = is_pre_ebase.ctxext dd (hom_base.ctx f Γ) (hom_base.fam f A))
      -- preservation of family extension
    ( famext : Π ⦃Γ : base.ctx AA⦄ (A : base.fam AA Γ) (P : base.fam AA (is_pre_ebase.ctxext ee Γ A)), hom_base.fam f (is_pre_ebase.famext ee A P) = is_pre_ebase.famext dd (hom_base.fam f A) ((ctxext Γ A) ▸ (hom_base.fam f P)))
      -- preservation of the empty structure
    ( empstr : Π (Γ : base.ctx AA), hom_base.fam f (is_pre_ebase.empstr ee Γ) = is_pre_ebase.empstr dd (hom_base.ctx f Γ))

  definition slice_base (AA : base) (ee : is_pre_ebase AA) (Γ : base.ctx AA) : base :=
  begin
    fapply base.mk,
      -- contexts
    exact base.fam AA Γ,
      -- dependent structures
    intro A,
    exact base.fam AA (is_pre_ebase.ctxext ee Γ A),
      -- terms
    intros A P,
    exact base.tm AA P
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
