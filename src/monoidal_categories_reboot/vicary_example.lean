import .monoidal_functor_attributes

universes v u

open category_theory

variables {C : Sort u} [𝒞 : monoidal_category.{v} C]
include 𝒞

lemma vicary : λ_ (𝟙_ C) = ρ_ (𝟙_ C) :=
begin
  obviously,
end