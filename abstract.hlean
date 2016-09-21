import types

open eq funext

universe variable u

    -- We attempt to formalize a weak notion of model of type theory using only homotopy-invariant 
    -- tools. We have two examples in mind: 
    -- - it should be possible to obtain such a model from a univalent universe,
    -- - given a univalent universe, there should be a model or (reflexive) graphs.
    --
    -- It turns out that what we formalize here is a theory of structures and dependent structures, 
    -- containing all the ways in which one could manipulate these. From another point of view, this
    -- is a theory of contexts and dependent contexts. It is a direct generalization of Cartmell's 
    -- contextual categories, which were reformulated as C-systems and B-systems by Voevodsky. The 
    -- weak notion of model we formalize here is a homotopified notion of E-system, which was 
    -- developed by the author. B-systems form a subcategory of E-systems, for which the inclusion 
    -- functor is full and faithful.

namespace model -- open the name space model
    
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

  namespace base -- Open the namespace model.base

  -- One operation we can always define on bases, is that if AA is an indexed base, then we can take
  -- the total space at the level of contexts to obtain a new base ∫ AA.

  definition total {I : Type.{u}} (AA : I → base) : base :=
    mk
        -- contexts
      ( Σ (i : I), @base.ctx (AA i))
        -- families
      ( sigma.rec (λ i, @base.fam (AA i)))
        -- terms
      ( sigma.rec (λ i, @base.tm (AA i)))

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

    -- We add the notion of homomorphism of bases to the namespace model.base

    structure hom (AA BB : base) : Type :=
        -- action on contexts
      ( action_ctx : base.ctx AA → base.ctx BB)
        -- action on dependent structures
      ( action_fam : Π ⦃Γ : base.ctx AA⦄, base.fam AA Γ → base.fam BB (action_ctx Γ))
        -- action on terms
      ( action_tm  : Π ⦃Γ : base.ctx AA⦄ ⦃A : base.fam AA Γ⦄, base.tm AA A → base.tm BB (action_fam A))

    -- infixr ` →base ` : 50 := base.hom

    namespace hom -- Open the namespace model.base.hom

      -- We add the identity homomorphism and composition to the namespace base.hom of base homomorphisms.

      definition id (AA : base) : hom AA AA :=
        mk
            -- action on contexts
          ( id)
            -- action on families
          ( λ Γ, id)
            -- action on terms
          ( λ Γ A, id)

      definition compose {AA BB CC : base} (f : hom AA BB) (g : hom BB CC) : hom AA CC :=
        mk
            -- action on contexts
          ( λ Γ, action_ctx g (action_ctx f Γ))
            -- action on families
          ( λ Γ A, action_fam g (action_fam f A))
            -- action on terms
          ( λ Γ A x, action_tm g (action_tm f x))

      definition total {I J : Type} (k : I → J) {AA : I → base} {BB : J → base} 
        ( f : Π (i : I), hom (AA i) (BB (k i))) : hom (total AA) (total BB) :=
        mk
            -- action on contexts
          ( sigma.rec (λ i Γ, sigma.mk (k i) (action_ctx (f i) Γ)))
            -- action on families
          ( sigma.rec (λ i Γ, @action_fam _ _ (f i) Γ))
            -- action on terms
          ( sigma.rec (λ i Γ, @action_tm _ _ (f i) Γ))

    end hom

    -- Before we extend the base structure to a base structure with context extension, we define the type of the operation of context extension.
    definition has_ctxext (AA : base) : Type := 
      Π (Γ : ctx AA), (fam AA Γ) → (ctx AA)

  end base

    -- We start adding ingredients to the base structure, by adding context extension into the mix.

  structure e0base extends AA : base :=
      -- context extension
    ( ctxext : base.has_ctxext AA)
      -- when base is a class, the following should work
    -- ( ctxext : base.has_ctxext)

  namespace e0base -- Open the namespace model.e0base

      -- If we are given a base, we can make it a base with context extension by adding context extension.
    definition from_base (AA : base) : base.has_ctxext AA → e0base :=
      e0base.mk
        ( base.ctx AA)
        ( base.fam AA)
        ( base.tm  AA)

    -- A homomorphism of bases with context extension is simply a homomorphism of bases which preserves context extension. We first define the type that witnesses whether context extension is preserved, and then we will define homomorphisms of bases with context extension.

    definition ty_pres_ctxext {AA BB : e0base} (f : base.hom AA BB) : Type :=
      Π (Γ : ctx AA) (A : fam AA Γ),
          base.hom.action_ctx f (ctxext AA Γ A) = ctxext BB (base.hom.action_ctx f Γ) (base.hom.action_fam f A)

    structure hom (AA BB : e0base) extends f : base.hom AA BB :=
      ( pres_ctxext : ty_pres_ctxext f)

    definition hom.from_basehom {AA BB : e0base} (f : base.hom AA BB) : ty_pres_ctxext f → hom AA BB :=
      hom.mk
          -- action on contexts
        ( base.hom.action_ctx f)
          -- action on families
        ( base.hom.action_fam f)
          -- action on terms
        ( base.hom.action_tm  f)

    -- notation AA `→e0base` BB := hom AA BB

    -- Given a context Γ in a base with context extension, we can find the base for a new model.

    definition slice {AA : e0base} (Γ : e0base.ctx AA) : base :=
      base.mk 
          -- contexts
        ( fam AA Γ) 
          -- families
        ( λ A, fam AA (ctxext AA Γ A)) 
          -- terms
        ( λ A P, tm AA P)

    definition slice.total (AA : e0base) : e0base :=
      e0base.from_base (base.total (@slice AA))
          -- context extension
        (sigma.rec (λ Γ A P, @sigma.mk (ctx AA) (fam AA) (ctxext AA Γ A) P))

    namespace hom -- Open the namespace model.e0base.hom

      -- Given a base homomorphism between bases with context extension, we define a slice operation on homomorphisms.
  
      definition slice {AA BB : e0base} (f : hom AA BB) (Γ : ctx AA) :
        base.hom (slice Γ) (slice (action_ctx f Γ)) :=
        base.hom.mk
            -- action on contexts
          (λ A, action_fam f A)
            -- action on families
          (λ A P, transport (fam BB) (pres_ctxext f Γ A) (action_fam f P))
            -- action on terms
          (λ A P x, transportD (tm BB) (pres_ctxext f Γ A) _ (action_tm f x))

     -- Furthermore, we can extend context extension to a base homomorphism.

    definition ctxext (AA : e0base) : base.hom (@base.total (ctx AA) (@e0base.slice AA)) AA :=
      base.hom.mk
          -- action on contexts
        (sigma.rec (ctxext AA))
          -- action on families
        (sigma.rec (λ Γ A, id))
          -- action on terms
        (sigma.rec (λ Γ A P, id))

    end hom 

  end e0base

  definition has_famext (AA : e0base) : Type :=
    Π {Γ : e0base.ctx AA} (A : e0base.fam AA Γ), (e0base.fam AA (e0base.ctxext AA Γ A)) → (e0base.fam AA Γ)

  definition has_empstr (AA : e0base) : Type :=
    Π (Γ : e0base.ctx AA), e0base.fam AA Γ

  structure pre_ebase extends AA : e0base :=
      -- family extension
    ( famext : has_famext AA)
      -- empty structure
    ( empstr : has_empstr AA)

  definition pre_ebase.from_e0base (AA : e0base) : has_famext AA → has_empstr AA → pre_ebase :=
    pre_ebase.mk
        -- contexts
      ( e0base.ctx AA)
        -- families
      ( e0base.fam AA)
        -- terms
      ( e0base.tm  AA)
        -- context extension
      ( e0base.ctxext AA)

  namespace pre_ebase -- opens the namespace model.pre_ebase

    definition e0slice (AA : pre_ebase) (Γ : pre_ebase.ctx AA) : e0base :=
      e0base.from_base (@e0base.slice AA Γ) (@pre_ebase.famext AA Γ) 

    -- We will now formalize what it means to preserve family extension.
    -- The idea behind this definition, is that f : AA → BB preserves
    -- family extension precisely when we can define for each Γ : ctx AA
    -- a base homomorphism
    --
    --   slice (f/Γ) : slice (AA/Γ) → slice (BB/(f Γ)),
    --
    -- such that the square of base homomorphisms
    --
    --                        ∫ (slice (f/Γ))
    --      ∫ (slice (AA/Γ)) ----------------> ∫ (slice (BB/(f Γ)))
    --              |                                  |
    --  hom.famext  |                                  | hom.famext
    --              V                                  V
    --             AA/Γ -------------------------> BB/(f Γ)
    --                               f/Γ
    --
    -- commutes. We also formalize this below.

    definition ty_pres_famext {AA BB : pre_ebase} (f : e0base.hom AA BB) : Type :=
      Π (Γ : ctx AA), 
          -- Since family extension is context extension in the slice model, 
          -- we give a specification in terms of context extension
        @e0base.ty_pres_ctxext 
            -- The domain e0base
          (e0slice AA Γ)
            -- The codomain e0base 
          (e0slice BB (e0base.hom.action_ctx f Γ)) 
            -- The base homomorphism between them
          (e0base.hom.slice f Γ)

    definition ty_pres_empstr {AA BB : pre_ebase} (f : e0base.hom AA BB) : Type :=
      Π (Γ : ctx AA), e0base.hom.action_fam f (empstr AA Γ) = empstr BB (e0base.hom.action_ctx f Γ)

    structure hom (AA BB : pre_ebase) extends f : e0base.hom AA BB :=
        -- preserves family extension
      ( pres_famext : ty_pres_famext f)
        -- preserves the empty structure
      ( pres_empstr : ty_pres_empstr f)

    definition hom.from_e0basehom {AA BB : pre_ebase} (f : e0base.hom AA BB) : 
      ty_pres_famext f → ty_pres_empstr f → hom AA BB :=
      hom.mk
          -- action on contexts
        ( e0base.hom.action_ctx f)
          -- action on families
        ( e0base.hom.action_fam f)
          -- action on terms
        ( e0base.hom.action_tm  f)
          -- preserves context extension
        ( e0base.hom.pres_ctxext f)

    definition slice_of_e0slice (AA : pre_ebase) (Γ : ctx AA) : (e0base.ctx (e0slice AA Γ)) → base :=
      @e0base.slice (e0slice AA Γ)
    
    namespace hom -- open the namespace model.pre_ebase.hom
     
      -- We extend the definition of pre_ebase.e0slice to homomorphisms of e0bases,
      -- so that the slice of a pre-ebase homomorphism gets the structure of an
      -- e0base homomorphism.

    definition e0slice {AA BB : pre_ebase} (f : hom AA BB) (Γ : ctx AA) : 
      e0base.hom (pre_ebase.e0slice AA Γ) (pre_ebase.e0slice BB (action_ctx f Γ)) :=
      e0base.hom.from_basehom 
        ( e0base.hom.slice f Γ)
        ( pres_famext f Γ)

    end hom

  end pre_ebase

/--

    -- We now extend the notion of base to the notion of extension base, by adding
    -- - context extension
    -- - family extension
    -- - an empty structure, which is a right unit for context extension and a unit (both left and 
    --   right) for family extension,
    -- - associativity for context extension and family extension
    -- We do not (yet) require further coherence laws for associativity.
    --
    -- Note that the equations are formulated as equations between dependent functions, as opposed 
    -- to families of equations. This makes it slightly easier, in my experience, to formulate the 
    -- requirement that these equations should be preserved, in the formalization of later aspects 
    -- of models of type theory.

  structure ebase extends e0base :=
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
    -- We open the name space model.ebase, so that we can freely use its ingredients.

    -- A pre-homomorphism of ebases is a homomorphism which preserves the operations of context 
    -- extension, family extension and the empty structure. However, a pre-homomorphism of ebases is
    -- not yet required to preserve the further equations in the structure of an ebase. This 
    -- requires a more elaborate formalization, in which it is useful to have the auxilary notion of
    -- pre-homomorphism of ebases available.

  structure prehom_ebase (AA BB : ebase) extends e0base.hom AA BB :=
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

  definition slice_ebase.{v} (AA : ebase.{v}) (Γ : base.ctx AA) : ebase.{v} :=
  begin
    fapply ebase.mk,
      -- contexts
    exact ebase.fam AA Γ,
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

   -- We introduce the Π-constructor 
  definition ty_pi0 (AA : e0base) : Type := Π {Γ : e0base.ctx AA} (A : e0base.fam AA Γ), base.hom (e0base.slice (e0base.ctxext AA Γ A)) (e0base.slice Γ) 

  structure pi0base extends AA : e0base :=
    (pi : ty_pi0 AA)

  definition pi0base.from_e0base (AA : e0base) : ty_pi0 AA → pi0base :=
    pi0base.mk (e0base.ctx AA) (e0base.fam AA) (e0base.tm AA) (e0base.ctxext AA)
--/

end model
