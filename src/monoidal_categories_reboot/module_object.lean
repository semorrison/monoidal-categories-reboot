-- Copyright (c) 2019 Scott Morrison. All rights reserved.
import .monoidal_functor_attributes

universes v u

namespace category_theory

open monoidal_category

variables (C : Sort u) [𝒞 : monoidal_category.{v} C]
include 𝒞

structure Monoid :=
(A : C)
(unit        : tensor_unit C ⟶ A)
(product     : A ⊗ A ⟶ A)
(pentagon'   : (associator A A A).hom ≫ ((𝟙 A) ⊗ product) ≫ product
             = (product ⊗ (𝟙 A)) ≫ product . obviously)
(left_unit'  : (left_unitor A).hom = (unit ⊗ (𝟙 A)) ≫ product . obviously)
(right_unit' : (right_unitor A).hom = ((𝟙 A) ⊗ unit) ≫ product . obviously)

variables {C}

structure Module (A : Monoid.{v} C) :=
(M : C)
(action    : A.A ⊗ M ⟶ M)
(pentagon' : (associator A.A A.A M).hom ≫ ((𝟙 A.A) ⊗ action) ≫ action
             = (A.product ⊗ (𝟙 M)) ≫ action . obviously)

restate_axiom Module.pentagon'
attribute [simp,search] Module.pentagon

variables {A : Monoid.{v} C}

structure hom (M N : Module A) :=
(f : M.M ⟶ N.M)
(w' : M.action ≫ f = ((𝟙 A.A) ⊗ f) ≫ N.action . obviously)

restate_axiom hom.w'
attribute [simp,search] hom.w

@[extensionality] lemma hom.ext {M N : Module A} (f g : hom M N) (h : f.f = g.f) : f = g :=
begin
  cases f, cases g, congr, exact h
end

instance : category (Module A) :=
{ hom := λ M N, hom M N,
  id := λ M, { f := 𝟙 M.M },
  comp := λ M N O f g, { f := f.f ≫ g.f } }

end category_theory
