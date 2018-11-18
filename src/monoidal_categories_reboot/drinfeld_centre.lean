import .braided_monoidal_category
import .pseudo_natural_transformation

universes u₁ v₁

namespace category_theory.monoidal

variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
include 𝒞

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

end category_theory.monoidal
