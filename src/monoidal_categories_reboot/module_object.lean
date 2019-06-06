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
(left_unit'  : (unit ⊗ (𝟙 A)) ≫ product = (left_unitor A).hom . obviously)
(right_unit' : ((𝟙 A) ⊗ unit) ≫ product = (right_unitor A).hom . obviously)

restate_axiom Monoid.pentagon'
attribute [simp,search] Monoid.pentagon
restate_axiom Monoid.left_unit'
attribute [simp,search] Monoid.left_unit
restate_axiom Monoid.right_unit'
attribute [simp,search] Monoid.right_unit

variables {C}

structure Module (A : Monoid.{v} C) :=
(M : C)
(action    : A.A ⊗ M ⟶ M)
(pentagon' : (associator A.A A.A M).hom ≫ ((𝟙 A.A) ⊗ action) ≫ action
             = (A.product ⊗ (𝟙 M)) ≫ action . obviously)
(left_unit'  : (A.unit ⊗ (𝟙 M)) ≫ action = (left_unitor M).hom . obviously)

restate_axiom Module.pentagon'
attribute [simp,search] Module.pentagon
restate_axiom Module.left_unit'
attribute [simp,search] Module.left_unit

variables {A : Monoid.{v} C}

structure hom (M N : Module A) :=
(f : M.M ⟶ N.M)
(w' : M.action ≫ f = ((𝟙 A.A) ⊗ f) ≫ N.action . obviously)

restate_axiom hom.w'
attribute [search] hom.w

@[extensionality] lemma hom.ext {M N : Module A} (f g : hom M N) (h : f.f = g.f) : f = g :=
begin
  cases f, cases g, congr, exact h
end

instance : category (Module A) :=
{ hom := λ M N, hom M N,
  id := λ M, { f := 𝟙 M.M },
  comp := λ M N O f g, { f := f.f ≫ g.f } }

end category_theory
