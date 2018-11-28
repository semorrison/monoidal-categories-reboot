import .braided_monoidal_category
import .pseudo_natural_transformation
import category_theory.functor_category

universes u v u₁ v₁ u₂ v₂

open category_theory

namespace category_theory.is_iso

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C]
variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

variables {F G : C ⥤ D}

instance is_iso_of_is_iso_app (α : Π X : C, F.obj X ⟶ G.obj X) [∀ X : C, is_iso (α X)] (nat) : 
  @is_iso (C ⥤ D) (category_theory.functor.category C D) F G { app := λ X, α X, naturality' := nat } :=
begin
  sorry
end

end category_theory.is_iso

namespace category_theory.monoidal

variables {C : Type u} [𝒞 : monoidal_category.{u v} C]
include 𝒞

def iso.of_is_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : X ≅ Y :=
{ hom := f,
  inv := inv f }


open monoidal_category

-- We give two versions, one abstract nonsense, as `(End (1 C))`, and the other concrete.
-- They are not-so-far from definitionally equal.
instance drinfeld_centre : braided_monoidal_category (pseudo_natural_transformation (monoidal_functor.id C) (monoidal_functor.id C)) :=
{ braiding := λ X Y,
  -- As in the Eckmann-Hilton argument:
  by calc
  X ⊗ Y
      ≅ X.vcomp Y : by refl
  ... ≅ Y.vcomp X : sorry -- Argh, so many unitors. :-)
  ... ≅ Y ⊗ X : by refl,
  braiding_naturality' := sorry,
  hexagon_forward' := sorry,
  hexagon_reverse' := sorry }

variables (C)

structure Z :=
(X : C)
(β : tensor_on_left.obj X ≅ tensor_on_right.obj X)

variables {C}

structure Z_hom (P Q : Z.{u v} C) :=
(hom : P.X ⟶ Q.X)
(w' : ∀ Y : C, P.β.hom.app Y ≫ (𝟙 _ ⊗ hom) = (hom ⊗ 𝟙 _) ≫ Q.β.hom.app Y . obviously)

restate_axiom Z_hom.w'
attribute [search] Z_hom.w

namespace Z_hom

@[extensionality] lemma ext {P Q : Z.{u v} C} {f g : Z_hom P Q} (w : f.hom = g.hom) : f = g :=
begin
  cases f, cases g,
  congr,
  obviously,
end

def id (P : Z.{u v} C) : Z_hom P P :=
{ hom := 𝟙 _ }

@[simp] lemma id_hom (P : Z.{u v} C) : (id P).hom = 𝟙 P.X := rfl

def comp {P Q R : Z.{u v} C} (f : Z_hom P Q) (g : Z_hom Q R) : Z_hom P R :=
{ hom := f.hom ≫ g.hom }

@[simp] lemma comp_hom {P Q R : Z.{u v} C} (f : Z_hom P Q) (g : Z_hom Q R) : 
  (comp f g).hom = f.hom ≫ g.hom := rfl
end Z_hom

instance drinfeld_centre_category : category.{(max u v) v} (Z.{u v} C) :=
{ hom := λ P Q, Z_hom P Q,
  id := λ P, Z_hom.id P,
  comp := λ P Q R f g, Z_hom.comp f g }.

def Z_tensor_unit : Z.{u v} C := 
{ X := tensor_unit C,
  β := iso.of_is_iso
  { app := λ Y, (left_unitor Y).hom ≫ (right_unitor Y).inv, 
    naturality' := by obviously, } }

set_option class.instance_max_depth 200

def Z_tensor_obj (P Q : Z.{u v} C) : Z.{u v} C :=
{ X := P.X ⊗ Q.X,
  β := iso.of_is_iso
  { app := λ Y, (associator _ _ _).hom ≫ (𝟙 _ ⊗ (Q.β.hom.app Y)) ≫ (associator _ _ _).inv ≫ ((P.β.hom.app Y) ⊗ 𝟙 _) ≫ (associator _ _ _).hom,
    naturality' := sorry
  } }

def Z_tensor_hom {P Q R S : Z.{u v} C} (f : Z_hom P Q) (g : Z_hom R S) : 
  Z_hom (Z_tensor_obj P R) (Z_tensor_obj Q S) :=
{ hom := f.hom ⊗ g.hom }

instance : monoidal_category.{(max u v) v} (Z.{u v} C) :=
{ tensor_unit := Z_tensor_unit,
  tensor_obj := Z_tensor_obj,
  tensor_hom := λ P Q R S f g, Z_tensor_hom f g,
  associator := sorry,
  left_unitor := sorry,
  right_unitor := sorry,
}

end category_theory.monoidal
