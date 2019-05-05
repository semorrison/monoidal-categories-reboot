-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import category_theory.tactics.obviously -- Give ourselves access to `rewrite_search`
import .tensor_product
import tactic.slice

open category_theory
open tactic

universes v u

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

-- @[obviously] meta def obviously' (t : option (tactic unit )) : tactic unit :=
-- tactic.tidy { tactics := extended_tidy_tactics }

namespace category_theory
section -- TODO these should be the original lemmas!?
variables {C : Sort u} [𝒞 : category.{v} C]
include 𝒞
variables {X Y Z : C}

lemma cancel_epi'  (f : X ⟶ Y) [epi f]  {g h : Y ⟶ Z} (p : f ≫ g = f ≫ h) : g = h :=
epi.left_cancellation g h p
lemma cancel_mono' (f : X ⟶ Y) [mono f] {g h : Z ⟶ X} (p : g ≫ f = h ≫ f) : g = h :=
mono.right_cancellation g h p
end

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables {X Y Z : C} (f g : X ⟶ Y) (h : Y ⟶ Z)

instance inv_is_iso [is_iso f] : is_iso (inv f) :=
{ inv := f }
instance comp_is_iso [is_iso f] [is_iso h] : is_iso (f ≫ h) :=
{ inv := inv h ≫ inv f }

@[simp] lemma inv_id : inv (𝟙 X) = 𝟙 X := rfl
@[simp] lemma inv_comp [is_iso f] [is_iso h] : inv (f ≫ h) = inv h ≫ inv f := rfl
@[simp] lemma is_iso.inv_inv [is_iso f] : inv (inv f) = f := rfl
@[simp] lemma iso.inv_inv (f : X ≅ Y) : inv (f.inv) = f.hom := rfl
@[simp] lemma iso.inv_hom (f : X ≅ Y) : inv (f.hom) = f.inv := rfl

lemma eq_of_inv_eq [is_iso f] [is_iso g] (p : inv f = inv g) : f = g :=
begin
  apply cancel_epi' (inv f),
  conv {
    to_rhs,
    rw p,
  },
  simp,
end
end
end category_theory

open category_theory

namespace category_theory.monoidal
class monoidal_category (C : Sort u) extends category.{v} C :=
-- curried tensor product of objects:
(tensor_obj               : C → C → C)
-- curried tensor product of morphisms:
(tensor_hom               : Π {X₁ Y₁ X₂ Y₂ : C}, hom X₁ Y₁ → hom X₂ Y₂ → hom (tensor_obj X₁ X₂) (tensor_obj Y₁ Y₂))
-- tensor product laws:
(tensor_map_id'           : ∀ (X₁ X₂ : C), tensor_hom (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensor_obj X₁ X₂) . obviously)
(tensor_map_comp'         : ∀ {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂),
  tensor_hom (f₁ ≫ g₁) (f₂ ≫ g₂) = (tensor_hom f₁ f₂) ≫ (tensor_hom g₁ g₂) . obviously)
-- tensor unit:
(tensor_unit              : C)
-- associator:
(associator               : Π X Y Z : C, (tensor_obj (tensor_obj X Y) Z) ≅ (tensor_obj X (tensor_obj Y Z)))
(associator_naturality'   : assoc_natural tensor_obj @tensor_hom associator . obviously)
-- left unitor:
(left_unitor              : Π X : C, tensor_obj tensor_unit X ≅ X)
(left_unitor_naturality'  : left_unitor_natural tensor_obj @tensor_hom tensor_unit left_unitor . obviously)
-- right unitor:
(right_unitor             : Π X : C, tensor_obj X tensor_unit ≅ X)
(right_unitor_naturality' : right_unitor_natural tensor_obj @tensor_hom tensor_unit right_unitor . obviously)
-- pentagon identity:
(pentagon'                : pentagon @tensor_hom associator . obviously)
-- triangle identity:
(triangle'                : triangle @tensor_hom left_unitor right_unitor associator . obviously)

restate_axiom monoidal_category.tensor_map_id'
attribute [simp,search] monoidal_category.tensor_map_id
restate_axiom monoidal_category.tensor_map_comp'
attribute [simp,search] monoidal_category.tensor_map_comp
restate_axiom monoidal_category.associator_naturality'
attribute [search] monoidal_category.associator_naturality
restate_axiom monoidal_category.left_unitor_naturality'
attribute [search] monoidal_category.left_unitor_naturality
restate_axiom monoidal_category.right_unitor_naturality'
attribute [search] monoidal_category.right_unitor_naturality
restate_axiom monoidal_category.pentagon'
attribute [search] monoidal_category.pentagon
restate_axiom monoidal_category.triangle'
attribute [simp,search] monoidal_category.triangle

@[obviously] meta def obviously'' := tactic.tidy {tactics := tidy.default_tactics ++ [rewrite_search {}]}

section
open monoidal_category

-- TODO remove this
def one {C : Sort u} [monoidal_category.{v} C] (X : C) : X ≅ X :=
{ hom := 𝟙 X,
  inv := 𝟙 X }

def tensor_iso {C : Sort u} {X Y X' Y' : C} [monoidal_category.{v} C] (f : X ≅ Y) (g : X' ≅ Y') :
    tensor_obj X X' ≅ tensor_obj Y Y' :=
{ hom := tensor_hom f.hom g.hom,
  inv := tensor_hom f.inv g.inv}
end
open monoidal_category

infixr ` ⊗ `:80 := tensor_obj
infixr ` ⊗ `:80 := tensor_hom


section

variables (C : Sort u) [𝒞 : monoidal_category.{v} C]
include 𝒞

instance : category C := 𝒞.to_category

infixr ` ⊗ `:80 := tensor_obj
infixr ` ⊗ `:80 := tensor_hom
infixr ` ⊗ `:80 := tensor_iso

variables {C}

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] : is_iso (f ⊗ g) :=
{ inv := inv f ⊗ inv g }

@[simp] lemma inv_tensor {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g
:= rfl

variables {U V W X Y Z : C}

@[search] definition interchange (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z)
  : (f ≫ g) ⊗ (h ≫ k) = (f ⊗ h) ≫ (g ⊗ k) :=
tensor_map_comp C f h g k

@[simp,search] lemma interchange_left_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (f ≫ g) ⊗ (𝟙 Z) = (f ⊗ (𝟙 Z)) ≫ (g ⊗ (𝟙 Z)) :=
begin
  rw ←interchange,
  simp
end

@[simp,search] lemma interchange_right_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z) ⊗ (f ≫ g) = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
begin
  rw ←interchange,
  simp
end

@[search] lemma interchange_identities (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) :=
begin
  rw ←interchange,
  rw ←interchange,
  simp
end

instance tensor_iso_of_iso
    {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    [is_iso f] [is_iso g] : is_iso (f ⊗ g) :=
{ inv := (is_iso.inv f) ⊗ (is_iso.inv g) }

@[simp,search] lemma tensor_left_equiv
    {X Y : C} (f g : X ⟶ Y) :
    ((𝟙 (tensor_unit C)) ⊗ f = (𝟙 (tensor_unit C)) ⊗ g) ↔ (f = g) :=
sorry

@[simp,search] lemma tensor_right_equiv
    {X Y : C} (f g : X ⟶ Y) :
    (f ⊗ (𝟙 (tensor_unit C)) = g ⊗ (𝟙 (tensor_unit C))) ↔ (f = g) :=
sorry

-- proof following the nLab:
@[search] lemma left_unitor_product_aux_perimeter (X Y : C) :
    ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom ≫
    ((𝟙 (tensor_unit C)) ⊗ (associator (tensor_unit C) X Y).hom) ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor (X ⊗ Y)).hom)
  = (((right_unitor (tensor_unit C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) X Y).hom := by obviously

@[search] lemma left_unitor_product_aux_triangle (X Y : C) :
    ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y)) ≫
    (((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom) ⊗ (𝟙 Y))
  = ((right_unitor (tensor_unit C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y) := by obviously

@[search] lemma left_unitor_product_aux_square (X Y : C) :
    (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom ⊗ (𝟙 Y))
  = (((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom) ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) X Y).hom := by obviously

@[search] lemma left_unitor_product_aux (X Y : C) :
    ((𝟙 (tensor_unit C)) ⊗ (associator (tensor_unit C) X Y).hom) ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor (X ⊗ Y)).hom)
  = (𝟙 (tensor_unit C)) ⊗ ((left_unitor X).hom ⊗ (𝟙 Y)) :=
begin
  rw <-(cancel_epi (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom),
  rw left_unitor_product_aux_square,
  rw <-(cancel_epi ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y))),
  conv {
    to_rhs,
    slice 1 2,
    rw left_unitor_product_aux_triangle,
  },
  obviously
end

@[search] lemma right_unitor_product_aux_perimeter (X Y : C) :
    ((associator X Y (tensor_unit C)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X (Y ⊗ (tensor_unit C)) (tensor_unit C)).hom ≫
    ((𝟙 X) ⊗ (associator Y (tensor_unit C) (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (left_unitor (tensor_unit C)).hom)
  = ((right_unitor (X ⊗ Y)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X Y (tensor_unit C)).hom := by obviously

@[search] lemma right_unitor_product_aux_triangle (X Y : C) :
    ((𝟙 X) ⊗ (associator Y (tensor_unit C) (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (left_unitor (tensor_unit C)).hom)
  = (𝟙 X) ⊗ (right_unitor Y).hom ⊗ (𝟙 (tensor_unit C)) := by obviously

@[search] lemma right_unitor_product_aux_square (X Y : C) :
    (associator X (Y ⊗ (tensor_unit C)) (tensor_unit C)).hom ≫
    ((𝟙 X) ⊗ (right_unitor Y).hom ⊗ (𝟙 (tensor_unit C)))
  = (((𝟙 X) ⊗ (right_unitor Y).hom) ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X Y (tensor_unit C)).hom := by obviously

@[search] lemma right_unitor_product_aux (X Y : C) :
    ((associator X Y (tensor_unit C)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (((𝟙 X) ⊗ (right_unitor Y).hom) ⊗ (𝟙 (tensor_unit C)))
  = ((right_unitor (X ⊗ Y)).hom ⊗ (𝟙 (tensor_unit C))) :=
begin
  rw <-(cancel_mono (associator X Y (tensor_unit C)).hom),
  conv {
    to_lhs,
    slice 2 3,
    rw <-right_unitor_product_aux_square,
  },
  obviously
end

@[search] lemma left_unitor_product (X Y : C) :
  ((associator (tensor_unit C) X Y).hom) ≫
    ((left_unitor (X ⊗ Y)).hom)
  = ((left_unitor X).hom ⊗ (𝟙 Y)) :=
begin
  rw <-tensor_left_equiv,
  rw <-interchange_right_identity,
  apply left_unitor_product_aux
end

@[search] lemma right_unitor_product (X Y : C) :
    ((associator X Y (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (right_unitor Y).hom)
  = ((right_unitor (X ⊗ Y)).hom) :=
begin
  rw <-tensor_right_equiv,
  rw <-interchange_left_identity,
  apply right_unitor_product_aux
end

@[search] lemma left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (left_unitor X').inv = (left_unitor X).inv ≫ (𝟙 _ ⊗ f) :=
begin
  apply cancel_mono' (left_unitor X').hom,
  obviously
end

@[search] lemma right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (right_unitor X').inv = (right_unitor X).inv ≫ (f ⊗ 𝟙 _) :=
begin
  apply cancel_mono' (right_unitor X').hom,
  obviously
end

@[search] lemma associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
  (f ⊗ (g ⊗ h)) ≫ (associator X' Y' Z').inv = (associator X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
begin
  apply cancel_mono' (associator X' Y' Z').hom,
  obviously
end

@[search] lemma pentagon_inv (W X Y Z : C) :
  ((𝟙 W) ⊗ (associator X Y Z).inv) ≫ (associator W (X ⊗ Y) Z).inv ≫ ((associator W X Y).inv ⊗ (𝟙 Z))
    = (associator W X (Y ⊗ Z)).inv ≫ (associator (W ⊗ X) Y Z).inv :=
begin
  apply eq_of_inv_eq,
  dsimp,
  repeat { rw category.assoc },
  exact pentagon C W X Y Z
end



@[simp,search] lemma triangle_1 (X Y : C) :
  (associator X (tensor_unit C) Y).hom ≫ ((𝟙 X) ⊗ (left_unitor Y).hom) = (right_unitor X).hom ⊗ 𝟙 Y :=
monoidal_category.triangle C X Y

@[simp,search] lemma triangle_2 (X Y : C) :
  (associator X (tensor_unit C) Y).inv ≫ (right_unitor X).hom ⊗ 𝟙 Y = ((𝟙 X) ⊗ (left_unitor Y).hom) :=
by obviously

@[simp,search] lemma triangle_3 (X Y : C) :
  ((right_unitor X).inv ⊗ 𝟙 Y) ≫ (associator X (tensor_unit C) Y).hom = ((𝟙 X) ⊗ (left_unitor Y).inv) :=
begin
  apply cancel_mono' (𝟙 X ⊗ (left_unitor Y).hom),
  obviously,
end.

@[simp,search] lemma triangle_4 (X Y : C) :
  ((𝟙 X) ⊗ (left_unitor Y).inv) ≫ (associator X (tensor_unit C) Y).inv = ((right_unitor X).inv ⊗ 𝟙 Y) :=
begin
  apply cancel_mono' ((right_unitor X).hom ⊗ 𝟙 Y),
  obviously,
end.

-- This is not completely trivial.
-- See Proposition 2.2.4 of http://www-math.mit.edu/~etingof/egnobookfinal.pdf
@[simp,search] lemma triangle_right (X Y : C) :
  (associator X Y _).inv ≫ (right_unitor (X ⊗ Y)).hom = 𝟙 X ⊗ (right_unitor Y).hom :=
sorry

@[simp,search] lemma triangle_right_inv (X Y : C) :
  (right_unitor (X ⊗ Y)).inv ≫ (associator X Y _).hom = 𝟙 X ⊗ (right_unitor Y).inv :=
begin
  apply eq_of_inv_eq,
  obviously,
end

@[simp,search] lemma triangle_left (X Y : C) :
  (associator _ X Y ).hom ≫ (left_unitor (X ⊗ Y)).hom = (left_unitor X).hom ⊗ 𝟙 Y :=
sorry

@[simp,search] lemma triangle_left_inv (X Y : C) :
  (left_unitor (X ⊗ Y)).inv ≫ (associator _ X Y ).inv = (left_unitor X).inv ⊗ 𝟙 Y :=
begin
  apply eq_of_inv_eq,
  obviously,
end



end

section

-- In order to be able to describe the tensor product as a functor, we
-- need to be up in at least `Type 1` for both objects and morphisms,
-- so that we can construct products.
variables (C : Type u) [𝒞 : monoidal_category.{v+1} C]
include 𝒞

@[reducible] def monoidal_category.tensor : (C × C) ⥤ C :=
{ obj := λ X, tensor_obj X.1 X.2,
  map := λ {X Y : C × C} (f : X ⟶ Y), tensor_hom f.1 f.2 }

@[reducible] def monoidal_category.left_assoc_functor : (C × C × C) ⥤ C :=
{ obj := λ X, (X.1 ⊗ X.2.1) ⊗ X.2.2,
  map := λ {X Y : C × C × C} (f : X ⟶ Y),
    (f.1 ⊗ f.2.1) ⊗ f.2.2 }
@[reducible] def monoidal_category.right_assoc_functor : (C × C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ (X.2.1 ⊗ X.2.2),
  map := λ {X Y : C × C × C} (f : X ⟶ Y),
    f.1 ⊗ (f.2.1 ⊗ f.2.2) }
@[reducible] def monoidal_category.left_unitor_functor : C ⥤ C :=
{ obj := λ X, tensor_unit C ⊗ X,
  map := λ {X Y : C} (f : X ⟶ Y), (𝟙 (tensor_unit C)) ⊗ f }
@[reducible] def monoidal_category.right_unitor_functor : C ⥤ C :=
{ obj := λ X, X ⊗ tensor_unit C,
  map := λ {X Y : C} (f : X ⟶ Y), f ⊗ (𝟙 (tensor_unit C)) }

open monoidal_category

-- natural isomorphisms for the associator and unitors.

@[reducible] def monoidal_category.associator_nat_iso :
  left_assoc_functor C ≅ right_assoc_functor C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.associator)
  (by intros; dsimp; apply monoidal_category.associator_naturality)

@[reducible] def monoidal_category.left_unitor_nat_iso :
  left_unitor_functor C ≅ functor.id C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.left_unitor)
  (by intros; dsimp; apply monoidal_category.left_unitor_naturality)

@[reducible] def monoidal_category.right_unitor_nat_iso :
  right_unitor_functor C ≅ functor.id C :=
nat_iso.of_components
 -- Previously there was a `simp` here;
 -- it's dangerous using `simp` instead of `dsimp` to produce a morphism,
 -- as you might have some `eq.mpr`s left over.
  (by intros; dsimp; apply monoidal_category.right_unitor)
  (by intros; dsimp; apply monoidal_category.right_unitor_naturality)

end

end category_theory.monoidal
