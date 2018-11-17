import .monoidal_functor
import tidy.rewrite_search
import tactic.interactive

open category_theory
open tactic

universes u₁ u₂ u₃ v₁ v₂ v₃

open category_theory.category
open category_theory.functor
open category_theory.prod
open category_theory.functor.category.nat_trans
open category_theory.nat_iso

namespace category_theory.monoidal

open monoidal_category

variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : monoidal_category.{u₂ v₂} D]
variables (F G : monoidal_functor C D)

structure pseudo_natural_transformation :=
(N : D)
(β : F.to_functor ⋙ (tensor_on_left N) ⟹ G.to_functor ⋙ (tensor_on_right N))
(c : Π X Y : C,
  β.app (X ⊗ Y) =
  (𝟙 N ⊗ (F.μ X Y).inv) ≫ (associator _ _ _).inv ≫
    ((β.app X) ⊗ 𝟙 _) ≫ (associator _ _ _).hom ≫
    (𝟙 _ ⊗ (β.app Y)) ≫ (associator _ _ _).inv ≫ (G.μ X Y).hom ⊗ 𝟙 N)

namespace pseudo_natural_transformation

variable (H : monoidal_functor C D)

def vcomp (α : pseudo_natural_transformation F G) (β : pseudo_natural_transformation G H) :
  pseudo_natural_transformation F H :=
{ N := α.N ⊗ β.N,
  β := begin end

}

end pseudo_natural_transformation


-- TODO define vcomp and hcomp on these
-- TODO define modifications
-- TODO obtain the Drinfeld centre from these, as a braided monoidal category

end category_theory.monoidal
