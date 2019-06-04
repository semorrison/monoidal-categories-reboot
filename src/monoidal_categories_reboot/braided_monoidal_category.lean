import .monoidal_functor_attributes
open category_theory
open tactic

universes v u v₁ u₁ v₂ u₂

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.nat_iso

namespace category_theory

class braided_monoidal_category (C : Sort u) extends monoidal_category.{v} C :=
-- braiding natural iso:
(braiding             : Π X Y : C, X ⊗ Y ≅ Y ⊗ X)
(braiding_naturality' : ∀ {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
  (f ⊗ g) ≫ (braiding Y Y').hom = (braiding X X').hom ≫ (g ⊗ f) . obviously)
-- hexagon identities:
(hexagon_forward'     : Π X Y Z : C,
    (associator X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (associator Y Z X).hom
  = ((braiding X Y).hom ⊗ (𝟙 Z)) ≫ (associator Y X Z).hom ≫ ((𝟙 Y) ⊗ (braiding X Z).hom)
  . obviously)
(hexagon_reverse'     : Π X Y Z : C,
    (associator X Y Z).inv ≫ (braiding (X ⊗ Y) Z).hom ≫ (associator Z X Y).inv
  = ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (associator X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y))
  . obviously)


restate_axiom braided_monoidal_category.braiding_naturality'
attribute [simp,search] braided_monoidal_category.braiding_naturality
restate_axiom braided_monoidal_category.hexagon_forward'
attribute [simp,search] braided_monoidal_category.hexagon_forward
restate_axiom braided_monoidal_category.hexagon_reverse'
attribute [simp,search] braided_monoidal_category.hexagon_reverse

section

variables (C : Type u) [𝒞 : braided_monoidal_category.{v+1} C]
include 𝒞

open monoidal_category
open braided_monoidal_category
open monoidal_category

-- @[simp,search] def braiding_of_product (X Y Z : C) :
--   (braiding (X ⊗ Y) Z).hom =
--   (associator X Y Z).hom ≫ ((𝟙 X) ⊗ (braiding Y Z).hom) ≫ (associator X Z Y).inv ≫ ((braiding X Z).hom ⊗ (𝟙 Y)) ≫ (associator Z X Y).hom :=
-- begin
--   sorry
-- end

end

class symmetric_monoidal_category (C : Sort u) extends braided_monoidal_category.{v} C :=
-- braiding symmetric:
(symmetry' : ∀ X Y : C, (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 (X ⊗ Y) . obviously)

restate_axiom symmetric_monoidal_category.symmetry'
attribute [simp,search] symmetric_monoidal_category.symmetry

open braided_monoidal_category

variables (C : Type u₁) [𝒞 : braided_monoidal_category.{v₁} C]
variables (D : Type u₂) [𝒟 : braided_monoidal_category.{v₂} D]
include 𝒞 𝒟

-- FIXME add tensorators
-- structure braided_functor extends F : monoidal_functor.{v₁ v₂} C D :=
-- (w' := Π X Y : C, F.to_functor.map_iso (braiding X Y) = braiding (F.obj X) (F.obj Y))

end category_theory
