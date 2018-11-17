-- Copyright (c) 2018 Scott Morrison. All rights reserved.
import ..monoidal_functor
import tactic.squeeze
open category_theory
open tactic

universes u v

-- This is section is in a PR for mathlib.
namespace category_theory.functor

universes u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅

variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A]
variables {B : Type u₂} [ℬ : category.{u₂ v₂} B]
include 𝒜 ℬ

variables (F : A ⥤ B)

def left_unitor : ((functor.id _) ⋙ F) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

def right_unitor : (F ⋙ (functor.id _)) ≅ F :=
{ hom := { app := λ X, 𝟙 (F.obj X) },
  inv := { app := λ X, 𝟙 (F.obj X) } }

@[simp] lemma left_unitor_hom_app (X : A) : (left_unitor F).hom.app X = 𝟙 _ := rfl
@[simp] lemma left_unitor_inv_app (X : A) : (left_unitor F).inv.app X = 𝟙 _ := rfl
@[simp] lemma right_unitor_hom_app (X : A) : (right_unitor F).hom.app X = 𝟙 _ := rfl
@[simp] lemma right_unitor_inv_app (X : A) : (right_unitor F).inv.app X = 𝟙 _ := rfl


variables {C : Type u₃} [𝒞 : category.{u₃ v₃} C]
variables {D : Type u₄} [𝒟 : category.{u₄ v₄} D]
include 𝒞 𝒟

variables (G : B ⥤ C) (H : C ⥤ D)

def associator : ((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H)) :=
{ hom := { app := λ _, 𝟙 _ },
  inv := { app := λ _, 𝟙 _ } }

@[simp] lemma associator_hom_app (X : A) : (associator F G H).hom.app X = 𝟙 _ := rfl
@[simp] lemma associator_inv_app (X : A) : (associator F G H).inv.app X = 𝟙 _ := rfl

omit 𝒟

lemma triangle (F : A ⥤ B) (G : B ⥤ C) :
  (associator F (functor.id B) G).hom ⊟ (whisker_left F (left_unitor G).hom) =
    (whisker_right (right_unitor F).hom G) :=
begin
  ext1,
  dsimp [associator, left_unitor, right_unitor],
  simp
end

variables {E : Type u₅} [ℰ : category.{u₅ v₅} E]
include 𝒟 ℰ

variables (K : D ⥤ E)

lemma pentagon :
  (whisker_right (associator F G H).hom K) ⊟ (associator F (G ⋙ H) K).hom ⊟ (whisker_left F (associator G H K).hom) =
    ((associator (F ⋙ G) H K).hom ⊟ (associator F G (H ⋙ K)).hom) :=
begin
  ext1,
  dsimp [associator],
  simp,
end

end category_theory.functor

open category_theory
namespace category_theory.monoidal

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

local attribute [back] category.id

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
variables {C : Type u} [𝒞 : monoidal_category.{u v} C]
include 𝒞

local attribute [back] category.id

def tensor_on_right : monoidal_functor C (C ⥤ C) :=
{ obj := λ Y,
  { obj := λ X, X ⊗ Y,
    map := λ (X X') (f : X ⟶ X'), f ⊗ 𝟙 Y },
  map := λ Y Y' f,
  { app := λ X, 𝟙 X ⊗ f, naturality' := by obviously, /- works (by obviously) -/ },
  ε := (monoidal_category.right_unitor_nat_iso C).symm,
  μ := λ X Y, nat_iso.of_components (λ Z, monoidal_category.associator Z X Y) sorry, /- works (by obviously) -/
  μ_natural' := sorry, /- works (by obviously) -/
  associativity' := sorry, /- works (by obviously) -/
  left_unitality' := sorry, /- works (by obviously) -/
  right_unitality' := begin tidy, obviously,end /- doesn't work! -/ }

end category_theory.monoidal