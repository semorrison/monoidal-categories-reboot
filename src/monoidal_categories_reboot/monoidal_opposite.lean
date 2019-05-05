-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import .monoidal_category

open category_theory
namespace category_theory.monoidal

universes u₁ v₁ u₂ v₂

def mop (C : Type u₁) : Type u₁ := C

variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
include 𝒞

instance underlying_category_monoidal_opposite : category.{u₁ v₁} (mop C) := 𝒞.to_category

instance monoidal_opposite : monoidal_category.{u₁ v₁} (mop C) :=
{ tensor_obj   := λ X Y, @monoidal_category.tensor_obj C _ Y X,
  tensor_hom   := λ (X₁ Y₁ X₂ Y₂ : mop C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂), @monoidal_category.tensor_hom C _ _ _ _ _ g f,
  tensor_unit  := @monoidal_category.tensor_unit C _,
  associator   := λ X Y Z, (@monoidal_category.associator C _ _ _ _).symm,
  left_unitor  := λ X, (@monoidal_category.right_unitor C _ _),
  right_unitor := λ X, (@monoidal_category.left_unitor C _ _) }

end category_theory.monoidal
