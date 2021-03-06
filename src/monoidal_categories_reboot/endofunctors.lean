-- Copyright (c) 2018 Scott Morrison. All rights reserved.
import .monoidal_functor_attributes
import .monoidal_opposite
import tactic.squeeze
import category_theory.tactics.obviously
import tidy.backwards_reasoning
open category_theory
open tactic

universes u v

namespace category_theory.monoidal

open category_theory

variables {C : Sort u} [𝒞 : category.{v} C]
include 𝒞

instance monoidal_category_of_endofunctors : monoidal_category (C ⥤ C) :=
{ tensor_obj   := λ F G, F ⋙ G,
  tensor_unit  := functor.id C,
  tensor_hom   := λ _ _ _ _ α β, α ◫ β,
  associator   := λ F G H, functor.associator F G H,
  left_unitor  := λ F, functor.left_unitor F,
  right_unitor := λ F, functor.right_unitor F }.

namespace endofunctors

@[simp] lemma tensor_endofunctors (F G : C ⥤ C) : F ⊗ G = F ⋙ G := rfl
@[simp] lemma unit_endofunctor : 𝟙_ (C ⥤ C) = functor.id C := rfl
@[simp] lemma tensor_endotransformations {F G H K : C ⥤ C} (α : F ⟶ G) (β : H ⟶ K) : α ⊗ β = (α ◫ β) :=
rfl

variables (F G H : C ⥤ C)
@[simp] lemma associator_hom : (α_ F G H).hom = 𝟙 _ := rfl
@[simp] lemma associator_inv : (α_ F G H).inv = 𝟙 _ := rfl
@[simp] lemma left_unitor_hom_app (X : C) : nat_trans.app (λ_ F).hom X = 𝟙 _ := rfl
@[simp] lemma left_unitor_inv_app (X : C) : nat_trans.app (λ_ F).inv X = 𝟙 _ := rfl
@[simp] lemma right_unitor_hom_app (X : C) : nat_trans.app (ρ_ F).hom X = 𝟙 _ := rfl
@[simp] lemma right_unitor_inv_app (X : C) : nat_trans.app (ρ_ F).inv X = 𝟙 _ := rfl

end endofunctors
end category_theory.monoidal

namespace category_theory.monoidal
variables {C : Type u} [𝒞 : monoidal_category.{v+1} C]
include 𝒞

def tensor_on_right : monoidal_functor.{v+1 (max u v)+1} C (C ⥤ C) :=
{ obj := λ Y,
  { obj := λ X, X ⊗ Y,
    map := λ X X' f, f ⊗ 𝟙 Y },
  map := λ Y Y' f, { app := λ X, 𝟙 X ⊗ f },
  ε := (monoidal_category.right_unitor_nat_iso C).inv,
  μ := λ X Y, { app := λ Z, (monoidal_category.associator Z X Y).hom },
  ε_is_iso := by {dsimp, apply_instance}, -- TODO, once apply_instance is above ext in tidy, try omitting these
  μ_is_iso := by {dsimp, apply_instance} }.

@[simp] lemma tensor_on_right.obj_obj (Y X : C) : (tensor_on_right.obj Y).obj X = X ⊗ Y := rfl
@[simp] lemma tensor_on_right.obj_map (Y : C) {X X' : C} (f : X ⟶ X') : (tensor_on_right.obj Y).map f = f ⊗ 𝟙 Y := rfl
@[simp] lemma tensor_on_right.map_app {Y Y' : C} (f : Y ⟶ Y') (X : C) : (tensor_on_right.map f).app X = 𝟙 X ⊗ f := rfl

-- -- FIXME mop needs some work
-- def tensor_on_left : monoidal_functor.{v+1 (max u v)+1} C (mop (C ⥤ C)) :=
-- { obj := λ Y : C,
--   { obj := λ X, Y ⊗ X,
--     map := λ X X' f, (𝟙 Y) ⊗ f },
--   map := λ Y Y' f, { app := λ X, f ⊗ 𝟙 X },
--   ε := (monoidal_category.left_unitor_nat_iso C).inv,
--   μ := λ X Y, { app := λ Z, (monoidal_category.associator X Y Z).inv },
--   ε_is_iso := by {dsimp, apply_instance}, -- TODO, once apply_instance is above ext in tidy, try omitting these
--   μ_is_iso := by {dsimp, apply_instance}  }.

-- @[simp] lemma tensor_on_left.obj_obj (Y X : C) : (tensor_on_left.obj Y).obj X = Y ⊗ X := rfl
-- @[simp] lemma tensor_on_left.obj_map (Y : C) {X X' : C} (f : X ⟶ X') : (tensor_on_left.obj Y).map f = 𝟙 Y ⊗ f := rfl
-- @[simp] lemma tensor_on_left.map_app {Y Y' : C} (f : Y ⟶ Y') (X : C) : (tensor_on_left.map f).app X = f ⊗ 𝟙 X := rfl

end category_theory.monoidal