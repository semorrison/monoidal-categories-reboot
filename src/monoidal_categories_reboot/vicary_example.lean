import .monoidal_functor_attributes
import tactic.slice

universes v u

open category_theory
open category_theory.category
open category_theory.monoidal_category

variables {C : Sort u} [𝒞 : monoidal_category.{v} C]
include 𝒞

lemma vicary : ρ_ (𝟙_ C) = λ_ (𝟙_ C) :=
begin
  obviously,
end

lemma vicary1 : (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv = 𝟙 _ :=
begin
  obviously,
end

lemma vicary2 : (λ_ (𝟙_ C ⊗ 𝟙_ C)).inv ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ _).hom) = (ρ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv :=
by obviously

@[search] lemma vicary12 : (ρ_ (𝟙_ C)).hom = (λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by obviously

lemma vicary4 :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).hom)) = (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv :=
by obviously

lemma vicary4' :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv = (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv ≫ ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv)) :=
by rw [←assoc, ←vicary4, assoc, ←id_tensor_comp, iso.hom_inv_id, tensor_id, comp_id]

@[search] lemma vicary34 :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv = (𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv) :=
by rw [vicary4', ←assoc, iso.hom_inv_id, id_comp]

@[search] lemma vicary1234 :
(ρ_ (𝟙_ C)).hom  = ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv))  ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by obviously

lemma vicary6 :
((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).hom = (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv :=
by obviously

lemma vicary6' :
((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) = (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv :=
by {rw [←assoc, ←vicary6, assoc, iso.hom_inv_id, comp_id], }

@[search] lemma vicary56 : ((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) = (ρ_ (𝟙_ C ⊗ 𝟙_ C)).inv :=
by rw [vicary6', ←assoc, iso.hom_inv_id, id_comp]

@[search] lemma vicary7 : ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv)) = ((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom :=
by obviously

@[search] lemma vicary1234567 :
(ρ_ (𝟙_ C)).hom = (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by obviously.

@[search] lemma vicary_8 : (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom = (ρ_ (((𝟙_ C) ⊗ (𝟙_ C)) ⊗ (𝟙_ C))).inv ≫ ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ ((𝟙_ C) ⊗ ((𝟙_ C) ⊗ (𝟙_ C)))).hom :=
by obviously.

@[search] lemma vicary_14 : (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (ρ_ (((𝟙_ C) ⊗ (𝟙_ C)) ⊗ (𝟙_ C))).inv = (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) :=
by rw [right_unitor_naturality'']

lemma vicary_9 : ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) = (α_ ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C) (𝟙_ C)).hom ≫ (α_ (𝟙_ C) (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv) ≫ (α_ (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C)).inv  :=
begin
  have := monoidal_category.pentagon C (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C),
  slice_rhs 1 2 { rw ←this },
  slice_rhs 3 4 { rw [←id_tensor_comp, iso.hom_inv_id], },
  simp,
end

@[search] lemma vicary_10_13 : ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) ≫ (α_ ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C) (𝟙_ C)).hom ≫ (α_ (𝟙_ C) (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv) ≫ (α_ (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C)).inv = ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C)) :=
begin
 slice_lhs 1 2 { simp, },
 slice_lhs 1 2 { rw [←tensor_id, associator_naturality], },
 slice_lhs 2 3 { rw [←id_tensor_comp], simp, },
 slice_lhs 1 2 { rw ←associator_naturality, },
 simp,
end

@[search] lemma vicary_9_13 : ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) ≫ ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) = ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C)) :=
begin
  rw vicary_9,
  rw vicary_10_13,
end

@[search] lemma vicary_15 : (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ ((𝟙_ C) ⊗ ((𝟙_ C) ⊗ (𝟙_ C)))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) = 𝟙 _ :=
begin
  slice_lhs 1 2 { rw [right_unitor_naturality''] },
  slice_lhs 2 3 { rw [iso.inv_hom_id] },
  obviously
end

lemma vicary' : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom :=
begin
  rw vicary1234567,
  rw vicary_8,
  slice_lhs 1 2 { rw vicary_14 },
  slice_lhs 2 3 { rw vicary_9_13 },
  slice_lhs 1 4 { rw vicary_15 },
  rw id_comp,
end
