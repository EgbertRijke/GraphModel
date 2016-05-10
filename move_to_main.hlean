import types

open eq

inductive pathover2 {A B : Type} (C : A → B → Type) :
  Π {a a' : A} (p : a=a') {b b' : B} (q : b=b') (x : C a b) (y : C a' b'), Type :=
  | idpo2 : Π {a : A} {b : B} (x : C a b), pathover2 C (idpath a) (idpath b) x x

definition tr_eq_of_homotopy {A : Type} {B : A → Type} (x y : A) (C : B x → B y → Type) :
  Π (f g : Π (a : A), B a) (H : f ~ g) (c : C (f x) (f y)), (eq_of_homotopy H) ▸ c = (H x) ▸ ( (H y) ▸ c) :=
  begin
    intros f g H,
    induction H,
    rewrite eq_of_homotopy_idp,
    intro c,
    reflexivity  
    end

  local attribute homotopy2.rec_on [recursor]

definition tr_eq_of_homotopy2 {A : Type} {B : A → Type} {C : Π {a : A}, B a → Type} {a a' : A} 
  (x : B a) (y : B a') (D : C x → C y → Type) :
  Π (f g : Π {{a : A}} (b : B a), C b) (H : f ~2 g) (d : D (f x) (f y)),
  (eq_of_homotopy2 H) ▸ d = (H a x) ▸ ((H a' y) ▸ d) :=
  begin
    intros f g H,
    induction H,
    induction q,
    intro d,
    krewrite eq_of_homotopy2_id,
  end 
