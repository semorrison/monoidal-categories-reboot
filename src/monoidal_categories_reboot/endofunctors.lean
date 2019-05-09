-- Copyright (c) 2018 Scott Morrison. All rights reserved.
import .monoidal_functor
import .monoidal_opposite
import tactic.squeeze
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
open monoidal_category

@[simp] lemma tensor_endofunctors (F G : C ⥤ C) : F ⊗ G = F ⋙ G := rfl
@[simp] lemma unit_endofunctor : tensor_unit (C ⥤ C) = functor.id C := rfl
@[simp] lemma tensor_endotransformations {F G H K : C ⥤ C} (α : F ⟶ G) (β : H ⟶ K) : α ⊗ β = (α ◫ β) :=
rfl

variables (F G H : C ⥤ C)
@[simp] lemma associator_hom : (associator F G H).hom = 𝟙 _ := rfl
@[simp] lemma associator_inv : (associator F G H).inv = 𝟙 _ := rfl
@[simp] lemma left_unitor_hom_app (X : C) : nat_trans.app (monoidal_category.left_unitor F).hom X = 𝟙 _ := rfl
@[simp] lemma left_unitor_inv_app (X : C) : nat_trans.app (monoidal_category.left_unitor F).inv X = 𝟙 _ := rfl
@[simp] lemma right_unitor_hom_app (X : C) : nat_trans.app (monoidal_category.right_unitor F).hom X = 𝟙 _ := rfl
@[simp] lemma right_unitor_inv_app (X : C) : nat_trans.app (monoidal_category.right_unitor F).inv X = 𝟙 _ := rfl

end endofunctors
end category_theory.monoidal

namespace category_theory.monoidal
variables {C : Type u} [𝒞 : monoidal_category.{v+1} C]
include 𝒞

def tensor_on_right : monoidal_functor C (C ⥤ C) :=
{ obj := λ Y,
  { obj := λ X, X ⊗ Y,
    map := λ (X X') (f : X ⟶ X'), f ⊗ 𝟙 Y },
  map := λ Y Y' f,
  { app := λ X, 𝟙 X ⊗ f },
  ε := (monoidal_category.right_unitor_nat_iso C).symm,
  μ := λ X Y, nat_iso.of_components (λ Z, monoidal_category.associator Z X Y) (by obviously) }.

def tensor_on_left : monoidal_functor C (mop (C ⥤ C)) :=
{ obj := λ Y : C,
  { obj := λ X, Y ⊗ X,
    map := λ (X X') (f : X ⟶ X'), (𝟙 Y) ⊗ f },
  map := λ (Y Y' : C) (f : Y ⟶ Y'),
  { app := λ X, f ⊗ 𝟙 X },
  ε := (monoidal_category.left_unitor_nat_iso C).symm,
  μ := λ (X Y : C), nat_iso.of_components (λ Z, (monoidal_category.associator X Y Z).symm) (by obviously) }.

@[simp] lemma tensor_on_right.obj_obj (Y X : C) : (tensor_on_right.obj Y).obj X = X ⊗ Y := rfl
@[simp] lemma tensor_on_right.obj_map (Y : C) {X X' : C} (f : X ⟶ X') : (tensor_on_right.obj Y).map f = f ⊗ 𝟙 Y := rfl
@[simp] lemma tensor_on_right.map_app {Y Y' : C} (f : Y ⟶ Y') (X : C) : (tensor_on_right.map f).app X = 𝟙 X ⊗ f := rfl

@[simp] lemma tensor_on_left.obj_obj (Y X : C) : (tensor_on_left.obj Y).obj X = Y ⊗ X := rfl
@[simp] lemma tensor_on_left.obj_map (Y : C) {X X' : C} (f : X ⟶ X') : (tensor_on_left.obj Y).map f = 𝟙 Y ⊗ f := rfl
@[simp] lemma tensor_on_left.map_app {Y Y' : C} (f : Y ⟶ Y') (X : C) : (tensor_on_left.map f).app X = f ⊗ 𝟙 X := rfl

end category_theory.monoidal