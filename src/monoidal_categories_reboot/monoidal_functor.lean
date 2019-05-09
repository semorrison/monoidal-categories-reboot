-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import .tensor_product
import .monoidal_category
import tactic.rewrite_search
import tactic.interactive

open category_theory
open tactic

universe u

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

namespace category_theory.monoidal

section

open monoidal_category

variables (C : Sort u₁) [𝒞 : monoidal_category.{v₁} C]
          (D : Sort u₂) [𝒟 : monoidal_category.{v₂} D]
include 𝒞 𝒟

structure lax_monoidal_functor
extends category_theory.functor.{v₁ v₂ u₁ u₂} C D :=
-- unit morphism
(ε               : tensor_unit D ⟶ obj (tensor_unit C))
-- tensorator
(μ                : Π X Y : C, (obj X) ⊗ (obj Y) ⟶ obj (X ⊗ Y))
(μ_natural'       : ∀ (X Y X' Y' : C)
  (f : X ⟶ Y) (g : X' ⟶ Y'),
  ((map f) ⊗ (map g)) ≫ μ Y Y' = μ X X' ≫ map (f ⊗ g)
  . obviously)
-- associativity
(associativity'   : ∀ (X Y Z : C),
    (μ X Y ⊗ 𝟙 (obj Z)) ≫ μ (X ⊗ Y) Z ≫ map (associator X Y Z).hom
  = (associator (obj X) (obj Y) (obj Z)).hom ≫ (𝟙 (obj X) ⊗ μ Y Z) ≫ μ X (Y ⊗ Z)
  . obviously)
-- unitality
(left_unitality'  : ∀ X : C,
    (left_unitor (obj X)).hom
  = (ε ⊗ 𝟙 (obj X)) ≫ μ (tensor_unit C) X ≫ map (left_unitor X).hom
  . obviously)
(right_unitality' : ∀ X : C,
    (right_unitor (obj X)).hom
  = (𝟙 (obj X) ⊗ ε) ≫ μ X (tensor_unit C) ≫ map (right_unitor X).hom
  . obviously)

restate_axiom lax_monoidal_functor.μ_natural'
attribute [simp,search] lax_monoidal_functor.μ_natural
restate_axiom lax_monoidal_functor.left_unitality'
attribute [simp,search] lax_monoidal_functor.left_unitality
restate_axiom lax_monoidal_functor.right_unitality'
attribute [simp,search] lax_monoidal_functor.right_unitality
restate_axiom lax_monoidal_functor.associativity'
attribute [simp,search] lax_monoidal_functor.associativity

structure monoidal_functor
extends lax_monoidal_functor.{v₁ v₂ u₁ u₂} C D :=
(ε_is_iso            : is_iso ε . obviously)
(μ_is_iso            : Π X Y : C, is_iso (μ X Y) . obviously)

attribute [instance] monoidal_functor.ε_is_iso monoidal_functor.μ_is_iso

variables {C D}
def monoidal_functor.ε_iso (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) :
  tensor_unit D ≅ F.obj (tensor_unit C) :=
as_iso F.ε
def monoidal_functor.μ_iso (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) (X Y : C) :
  (F.obj X) ⊗ (F.obj Y) ≅ F.obj (X ⊗ Y) :=
as_iso (F.μ X Y)

end

namespace monoidal_functor

open monoidal_category

section

variables {C : Type u₁} [𝒞 : monoidal_category.{v₁+1} C]
variables {D : Type u₂} [𝒟 : monoidal_category.{v₂+1} D]
include 𝒞 𝒟

def μ_nat_iso (F : monoidal_functor.{v₁+1 v₂+1 u₁+1 u₂+1} C D) :
  (functor.prod F.to_functor F.to_functor) ⋙ (tensor D) ≅ (tensor C) ⋙ F.to_functor :=
nat_iso.of_components
  (by intros; dsimp; apply F.μ_iso)
  (by intros; dsimp; apply F.to_lax_monoidal_functor.μ_natural)

end

variables {C : Sort u₁} [𝒞 : monoidal_category.{v₁} C]
variables {D : Sort u₂} [𝒟 : monoidal_category.{v₂} D]
include 𝒞 𝒟



-- This is unfortunate; we need all sorts of struts to give
-- monoidal functors the features of functors...
@[reducible] def on_iso (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) {X Y : C} (f : X ≅ Y) : F.obj X ≅ F.obj Y :=
F.to_functor.map_iso f

@[search] lemma map_id (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) (X : C) :
  F.map (𝟙 X) = 𝟙 (F.obj X) := F.map_id' X

@[search] lemma map_comp (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  F.map (f ≫ g) = F.map f ≫ F.map g := F.map_comp' f g
end monoidal_functor

section

variables (C : Sort u₁) [𝒞 : monoidal_category.{v₁} C]
include 𝒞

def monoidal_functor.id : monoidal_functor.{v₁ v₁ u₁ u₁} C C :=
{ ε := 𝟙 _,
  μ := λ X Y, 𝟙 _,
  .. functor.id C }

@[simp] lemma id_obj (X : C) : (monoidal_functor.id C).obj X = X := rfl
@[simp] lemma id_map {X X' : C} (f : X ⟶ X') : (monoidal_functor.id C).map f = f :=
rfl

variables {C}
variables {D : Sort u₂} [𝒟 : monoidal_category.{v₂} D]
variables {E : Sort u₃} [ℰ : monoidal_category.{v₃} E]

include 𝒟 ℰ

open tactic.rewrite_search.tracer
-- set_option profiler true

def monoidal_functor.comp
  (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) (G : monoidal_functor.{v₂ v₃ u₂ u₃} D E) : monoidal_functor.{v₁ v₃ u₁ u₃} C E :=
{ ε                := G.ε ≫ (G.map F.ε),
  μ                := λ X Y, G.μ (F.obj X) (F.obj Y) ≫ G.map (F.μ X Y),
  ε_is_iso         := by apply_instance, -- TODO tidy should get this
  μ_is_iso         := by apply_instance, -- TODO tidy should get this
  μ_natural'       :=
  begin
    tidy,
    /- `rewrite_search` says -/
    conv_lhs { erw [←category.assoc] },
    conv_lhs { congr, erw [lax_monoidal_functor.μ_natural] },
    conv_lhs { erw [category.assoc] },
    conv_lhs { congr, skip, erw [←map_comp] },
    conv_rhs { congr, skip, erw [←map_comp] },
    conv_rhs { congr, skip, erw [←lax_monoidal_functor.μ_natural] }
  end,
  associativity'   := λ X Y Z,
  begin
    -- obviously fails here, but it seems like it should be doable!
    dsimp,
    conv { to_rhs,
      rw interchange_right_identity,
      slice 3 4,
      rw ← G.map_id,
      rw G.to_lax_monoidal_functor.μ_natural,
    },
    -- rewrite_search { view := visualiser, trace_summary := tt, explain := tt, max_iterations := 50 }, -- fails
    conv { to_rhs,
      slice 1 3,
      rw ←G.to_lax_monoidal_functor.associativity,
    },
    -- rewrite_search (saw/visited/used) 137/23/16 expressions during proof of category_theory.monoidal.monoidal_functor.comp
    conv { to_lhs,
      rw interchange_left_identity,
      slice 2 3,
      rw ← G.map_id,
      rw G.to_lax_monoidal_functor.μ_natural, },
    repeat { rw category.assoc },
    repeat { rw ←G.map_comp },
    rw F.to_lax_monoidal_functor.associativity,
  end,
  left_unitality'  := λ X,
  begin
    -- Don't attempt to read this; it is a Frankenstein effort of Scott + rewrite_search
    dsimp,
    rw G.to_lax_monoidal_functor.left_unitality,
    rw interchange_left_identity,
    repeat {rw category.assoc},
    apply congr_arg,
    /- `rewrite_search` says -/
    rw F.to_lax_monoidal_functor.left_unitality,
    conv_lhs { congr, skip, erw [map_comp] },
    conv_lhs { erw [←category.id_app] },
    conv_lhs { erw [←category.assoc] },
    conv_lhs { congr, erw [←lax_monoidal_functor.μ_natural] },
    conv_lhs { congr, congr, congr, skip, erw [map_id] },
    conv_rhs { erw [←category.assoc] },
    erw map_comp,
  end,
  right_unitality' := λ X,
  begin
    dsimp,
    rw G.to_lax_monoidal_functor.right_unitality,
    rw interchange_right_identity,
    repeat {rw category.assoc},
    apply congr_arg,
    /- `rewrite_search` says -/
    rw F.to_lax_monoidal_functor.right_unitality,
    conv_lhs { congr, skip, erw [map_comp] },
    conv_lhs { erw [←category.id_app] },
    conv_lhs { erw [←category.assoc] },
    conv_lhs { congr, erw [←lax_monoidal_functor.μ_natural] },
    conv_lhs { congr, congr, congr, erw [map_id] },
    conv_rhs { erw [←category.assoc] },
    erw map_comp,
  end,
  .. (F.to_functor) ⋙ (G.to_functor) }.

variables (F : monoidal_functor.{v₁ v₂ u₁ u₂} C D) (G : monoidal_functor.{v₂ v₃ u₂ u₃} D E)

@[simp] lemma comp_obj (X : C) : (F.comp G).obj X = G.obj (F.obj X) := rfl
@[simp] lemma comp_map {X X' : C} (f : X ⟶ X') :
  begin let h := (F.comp G).map f, dsimp at h, exact h end = G.map (F.map f) :=
rfl

end

end category_theory.monoidal