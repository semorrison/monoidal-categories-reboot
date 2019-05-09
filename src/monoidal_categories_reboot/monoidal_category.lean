-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.

import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import .tensor_product
import category_theory.tactics.obviously
import tactic
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
variables {C : Sort u} [𝒞 : category.{v} C]
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
  conv_rhs { rw p },
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

meta def rws : tactic string := `[rewrite_search { explain := tt }] >> pure ""
@[obviously] meta def obviously'' := tactic.tidy {tactics := tidy.default_tactics ++ [rws]}

section
open monoidal_category

-- TODO remove this
def one {C : Sort u} [monoidal_category.{v} C] (X : C) : X ≅ X :=
{ hom := 𝟙 X,
  inv := 𝟙 X }

def tensor_iso {C : Sort u} {X Y X' Y' : C} [monoidal_category.{v} C] (f : X ≅ Y) (g : X' ≅ Y') :
    tensor_obj X X' ≅ tensor_obj Y Y' :=
{ hom := tensor_hom f.hom g.hom,
  inv := tensor_hom f.inv g.inv,
  hom_inv_id' :=
  begin
    /- `rewrite_search` says -/
    conv_lhs { erw [←tensor_map_comp] },
    conv_lhs { congr, erw [is_iso.hom_inv_id], skip, erw [is_iso.hom_inv_id] },
    conv_rhs { erw [←tensor_map_id] }
  end,
  inv_hom_id' :=
  begin
    /- `rewrite_search` says -/
    conv_lhs { erw [←tensor_map_comp] },
    conv_lhs { congr, erw [is_iso.hom_inv_id], skip, erw [is_iso.hom_inv_id] },
    conv_rhs { erw [←tensor_map_id] }
  end }
end
open monoidal_category

infixr ` ⊗ `:70 := tensor_obj
infixr ` ⊗ `:70 := tensor_hom
infixr ` ⊗ `:70 := tensor_iso


section

variables (C : Sort u) [𝒞 : monoidal_category.{v} C]
include 𝒞

instance : category C := 𝒞.to_category

variables {C}

instance tensor_is_iso {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] : is_iso (f ⊗ g) :=
{ ..(as_iso f ⊗ as_iso g) }

@[simp] lemma inv_tensor {W X Y Z : C} (f : W ⟶ X) [is_iso f] (g : Y ⟶ Z) [is_iso g] :
  inv (f ⊗ g) = inv f ⊗ inv g
:= rfl

variables {U V W X Y Z : C}

@[search] definition interchange (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z)
  : (f ≫ g) ⊗ (h ≫ k) = (f ⊗ h) ≫ (g ⊗ k) :=
tensor_map_comp C f h g k

@[simp,search] lemma interchange_left_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (f ≫ g) ⊗ (𝟙 Z) = (f ⊗ (𝟙 Z)) ≫ (g ⊗ (𝟙 Z)) :=
by { rw ←interchange, simp }

@[simp,search] lemma interchange_right_identity (f : W ⟶ X) (g : X ⟶ Y) :
  (𝟙 Z) ⊗ (f ≫ g) = (𝟙 Z ⊗ f) ≫ (𝟙 Z ⊗ g) :=
by { rw ←interchange, simp }

@[search] lemma interchange_identities (f : W ⟶ X) (g : Y ⟶ Z) :
  ((𝟙 Y) ⊗ f) ≫ (g ⊗ (𝟙 X)) = (g ⊗ (𝟙 W)) ≫ ((𝟙 Z) ⊗ f) :=
by { rw [←interchange, ←interchange], simp }

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
    (associator (tensor_unit C) X Y).hom :=
begin
  /- `rewrite_search` says -/
  conv_lhs { congr, skip, erw [←category.assoc] },
  conv_lhs { erw [←category.assoc] },
  conv_lhs { congr, erw [monoidal_category.pentagon] },
  conv_rhs { erw [associator_naturality] },
  conv_rhs { congr, skip, congr, skip, erw [tensor_map_id] },
  conv_rhs { congr, skip, erw [←monoidal_category.triangle] },
  conv_rhs { erw [←category.assoc] }
end

@[search] lemma left_unitor_product_aux_triangle (X Y : C) :
    ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y)) ≫
    (((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom) ⊗ (𝟙 Y))
  = ((right_unitor (tensor_unit C)).hom ⊗ (𝟙 X)) ⊗ (𝟙 Y) :=
begin
  /- `rewrite_search` says -/
  conv_lhs { erw [←interchange_left_identity] },
  conv_rhs { congr, erw [←monoidal_category.triangle] }
end

@[search] lemma left_unitor_product_aux_square (X Y : C) :
    (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom ⊗ (𝟙 Y))
  = (((𝟙 (tensor_unit C)) ⊗ (left_unitor X).hom) ⊗ (𝟙 Y)) ≫
    (associator (tensor_unit C) X Y).hom :=
begin
  /- `rewrite_search` says -/
  conv_rhs { erw [associator_naturality] }
end

@[search] lemma left_unitor_product_aux (X Y : C) :
    ((𝟙 (tensor_unit C)) ⊗ (associator (tensor_unit C) X Y).hom) ≫
    ((𝟙 (tensor_unit C)) ⊗ (left_unitor (X ⊗ Y)).hom)
  = (𝟙 (tensor_unit C)) ⊗ ((left_unitor X).hom ⊗ (𝟙 Y)) :=
begin
  rw ←(cancel_epi (associator (tensor_unit C) ((tensor_unit C) ⊗ X) Y).hom),
  rw left_unitor_product_aux_square,
  rw ←(cancel_epi ((associator (tensor_unit C) (tensor_unit C) X).hom ⊗ (𝟙 Y))),
  slice_rhs 1 2 { rw left_unitor_product_aux_triangle },
  conv_lhs { erw [left_unitor_product_aux_perimeter] }
end

@[search] lemma right_unitor_product_aux_perimeter (X Y : C) :
    ((associator X Y (tensor_unit C)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X (Y ⊗ (tensor_unit C)) (tensor_unit C)).hom ≫
    ((𝟙 X) ⊗ (associator Y (tensor_unit C) (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (left_unitor (tensor_unit C)).hom)
  = ((right_unitor (X ⊗ Y)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X Y (tensor_unit C)).hom :=
begin
  /- `rewrite_search` says -/
  conv_lhs { congr, skip, erw [←category.assoc] },
  transitivity (((associator X Y _).hom ⊗ 𝟙 _) ≫ (associator X _ _).hom ≫ (𝟙 X ⊗ (associator Y _ _).hom)) ≫
    (𝟙 X ⊗ 𝟙 Y ⊗ (monoidal_category.left_unitor _).hom),
  conv_rhs { erw [category.assoc] },
  conv_lhs { congr, erw [monoidal_category.pentagon] },
  conv_rhs { congr, erw [←monoidal_category.triangle] },
  conv_rhs { erw [category.assoc] },
  conv_rhs { congr, skip, congr, congr, erw [←tensor_map_id] },
  conv_rhs { congr, skip, erw [associator_naturality] },
  conv_rhs { erw [←category.assoc] }
end

@[search] lemma right_unitor_product_aux_triangle (X Y : C) :
    ((𝟙 X) ⊗ (associator Y (tensor_unit C) (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (𝟙 Y) ⊗ (left_unitor (tensor_unit C)).hom)
  = (𝟙 X) ⊗ (right_unitor Y).hom ⊗ (𝟙 (tensor_unit C)) :=
begin
  /- `rewrite_search` says -/
  conv_lhs { erw [←interchange_right_identity] },
  conv_rhs { congr, skip, erw [←monoidal_category.triangle] }
end

@[search] lemma right_unitor_product_aux_square (X Y : C) :
    (associator X (Y ⊗ (tensor_unit C)) (tensor_unit C)).hom ≫
    ((𝟙 X) ⊗ (right_unitor Y).hom ⊗ (𝟙 (tensor_unit C)))
  = (((𝟙 X) ⊗ (right_unitor Y).hom) ⊗ (𝟙 (tensor_unit C))) ≫
    (associator X Y (tensor_unit C)).hom :=
begin
  /- `rewrite_search` says -/
  conv_rhs { erw [associator_naturality] }
end

@[search] lemma right_unitor_product_aux (X Y : C) :
    ((associator X Y (tensor_unit C)).hom ⊗ (𝟙 (tensor_unit C))) ≫
    (((𝟙 X) ⊗ (right_unitor Y).hom) ⊗ (𝟙 (tensor_unit C)))
  = ((right_unitor (X ⊗ Y)).hom ⊗ (𝟙 (tensor_unit C))) :=
begin
  rw ←(cancel_mono (associator X Y (tensor_unit C)).hom),
  slice_lhs 2 3 { rw ←right_unitor_product_aux_square },
  conv_lhs { congr, skip, congr, skip, erw [←right_unitor_product_aux_triangle] },
  conv_rhs { erw [←right_unitor_product_aux_perimeter] }
end

@[search] lemma left_unitor_product (X Y : C) :
  ((associator (tensor_unit C) X Y).hom) ≫
    ((left_unitor (X ⊗ Y)).hom)
  = ((left_unitor X).hom ⊗ (𝟙 Y)) :=
by rw [←tensor_left_equiv, interchange_right_identity, left_unitor_product_aux]

@[search] lemma right_unitor_product (X Y : C) :
    ((associator X Y (tensor_unit C)).hom) ≫
    ((𝟙 X) ⊗ (right_unitor Y).hom)
  = ((right_unitor (X ⊗ Y)).hom) :=
by rw [←tensor_right_equiv, interchange_left_identity, right_unitor_product_aux]

@[search] lemma left_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (left_unitor X').inv = (left_unitor X).inv ≫ (𝟙 _ ⊗ f) :=
begin
  apply cancel_mono' (left_unitor X').hom,
  simp only [assoc, comp_id, iso.inv_hom_id],
  /- `rewrite_search` says -/
  conv_rhs { congr, skip, erw [left_unitor_naturality] },
  conv_rhs { erw [←category.assoc] },
  conv_rhs { congr, erw [is_iso.hom_inv_id] },
  conv_rhs { erw [category.id_comp] }
end

@[search] lemma right_unitor_inv_naturality {X X' : C} (f : X ⟶ X') :
  f ≫ (right_unitor X').inv = (right_unitor X).inv ≫ (f ⊗ 𝟙 _) :=
begin
  apply cancel_mono' (right_unitor X').hom,
  simp only [assoc, comp_id, iso.inv_hom_id],
  /- `rewrite_search` says -/
  conv_rhs { congr, skip, erw [right_unitor_naturality] },
  conv_rhs { erw [←category.assoc] },
  conv_rhs { congr, erw [is_iso.hom_inv_id] },
  conv_rhs { erw [category.id_comp] }
end

@[search] lemma associator_inv_naturality {X Y Z X' Y' Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
  (f ⊗ (g ⊗ h)) ≫ (associator X' Y' Z').inv = (associator X Y Z).inv ≫ ((f ⊗ g) ⊗ h) :=
begin
  apply cancel_mono' (associator X' Y' Z').hom,
  simp only [assoc, comp_id, iso.inv_hom_id],
  /- `rewrite_search` says -/
  conv_rhs { congr, skip, erw [associator_naturality] },
  conv_rhs { erw [←category.assoc] },
  conv_rhs { congr, erw [is_iso.hom_inv_id] },
  conv_rhs { erw [category.id_comp] }
end

@[search] lemma pentagon_inv (W X Y Z : C) :
  ((𝟙 W) ⊗ (associator X Y Z).inv) ≫ (associator W (X ⊗ Y) Z).inv ≫ ((associator W X Y).inv ⊗ (𝟙 Z))
    = (associator W X (Y ⊗ Z)).inv ≫ (associator (W ⊗ X) Y Z).inv :=
begin
  apply eq_of_inv_eq,
  dsimp,
  rw [category.assoc, monoidal_category.pentagon]
end

@[simp,search] lemma triangle_1 (X Y : C) :
  (associator X (tensor_unit C) Y).hom ≫ ((𝟙 X) ⊗ (left_unitor Y).hom) = (right_unitor X).hom ⊗ 𝟙 Y :=
monoidal_category.triangle C X Y

@[simp,search] lemma triangle_2 (X Y : C) :
  (associator X (tensor_unit C) Y).inv ≫ ((right_unitor X).hom ⊗ 𝟙 Y) = ((𝟙 X) ⊗ (left_unitor Y).hom) :=
begin
  /- `rewrite_search` says -/
  conv_lhs { congr, skip, erw [←triangle_1] },
  conv_lhs { erw [←category.assoc] },
  conv_lhs { congr, erw [is_iso.hom_inv_id] },
  conv_lhs { erw [category.id_comp] }
end

@[simp,search] lemma triangle_3 (X Y : C) :
  ((right_unitor X).inv ⊗ 𝟙 Y) ≫ (associator X (tensor_unit C) Y).hom = ((𝟙 X) ⊗ (left_unitor Y).inv) :=
begin
  apply cancel_mono' (𝟙 X ⊗ (left_unitor Y).hom),
  simp only [assoc, triangle_1],
  /- `rewrite_search` says -/
  conv_lhs { erw [is_iso.hom_inv_id] },
  conv_rhs { erw [is_iso.hom_inv_id] }
end

@[simp,search] lemma triangle_4 (X Y : C) :
  ((𝟙 X) ⊗ (left_unitor Y).inv) ≫ (associator X (tensor_unit C) Y).inv = ((right_unitor X).inv ⊗ 𝟙 Y) :=
begin
  apply cancel_mono' ((right_unitor X).hom ⊗ 𝟙 Y),
  simp only [triangle_2, assoc],
  /- `rewrite_search` says -/
  conv_lhs { erw [is_iso.hom_inv_id] },
  conv_rhs { erw [is_iso.hom_inv_id] }
end

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

-- TODO replace all these @[simp] annotations with simp lemmas for the projections

@[simp] def monoidal_category.tensor : (C × C) ⥤ C :=
{ obj := λ X, tensor_obj X.1 X.2,
  map := λ {X Y : C × C} (f : X ⟶ Y), tensor_hom f.1 f.2 }

@[simp] def monoidal_category.triple_tensor_left : (C × C × C) ⥤ C :=
{ obj := λ X, (X.1 ⊗ X.2.1) ⊗ X.2.2,
  map := λ {X Y : C × C × C} (f : X ⟶ Y),
    (f.1 ⊗ f.2.1) ⊗ f.2.2 }
@[simp] def monoidal_category.triple_tensor_right : (C × C × C) ⥤ C :=
{ obj := λ X, X.1 ⊗ (X.2.1 ⊗ X.2.2),
  map := λ {X Y : C × C × C} (f : X ⟶ Y),
    f.1 ⊗ (f.2.1 ⊗ f.2.2) }
@[simp] def monoidal_category.tensor_unit_left : C ⥤ C :=
{ obj := λ X, tensor_unit C ⊗ X,
  map := λ {X Y : C} (f : X ⟶ Y), (𝟙 (tensor_unit C)) ⊗ f }
@[simp] def monoidal_category.tensor_unit_right : C ⥤ C :=
{ obj := λ X, X ⊗ tensor_unit C,
  map := λ {X Y : C} (f : X ⟶ Y), f ⊗ (𝟙 (tensor_unit C)) }

open monoidal_category

-- natural isomorphisms for the associator and unitors.

def monoidal_category.associator_nat_iso :
  triple_tensor_left C ≅ triple_tensor_right C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.associator)
  (by intros; dsimp; apply monoidal_category.associator_naturality)

def monoidal_category.left_unitor_nat_iso :
  tensor_unit_left C ≅ functor.id C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.left_unitor)
  (by intros; dsimp; apply monoidal_category.left_unitor_naturality)

def monoidal_category.right_unitor_nat_iso :
  tensor_unit_right C ≅ functor.id C :=
nat_iso.of_components
  (by intros; dsimp; apply monoidal_category.right_unitor)
  (by intros; dsimp; apply monoidal_category.right_unitor_naturality)

end

end category_theory.monoidal
