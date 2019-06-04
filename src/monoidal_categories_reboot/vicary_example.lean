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

@[search] lemma vicary_1_2 : (ρ_ (𝟙_ C)).hom = (λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by obviously

lemma vicary_4 :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).hom)) = (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv :=
by obviously

lemma vicary_4' :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv = (λ_ (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).inv ≫ ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv)) :=
by rw [←assoc, ←vicary_4, assoc, ←id_tensor_comp, iso.hom_inv_id, tensor_id, comp_id]

@[search] lemma vicary_3_4 :
(λ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv = (𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv) :=
by rw [vicary_4', ←assoc, iso.hom_inv_id, id_comp]

@[search] lemma vicary_1_4 :
(ρ_ (𝟙_ C)).hom  = ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv))  ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by obviously

lemma vicary_6 :
((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).hom = (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv :=
by obviously

lemma vicary_6' :
((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) = (ρ_ (𝟙_ C)).hom ≫ (ρ_ (𝟙_ C)).inv ≫ (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv :=
by {rw [←assoc, ←vicary_6, assoc, iso.hom_inv_id, comp_id], }

@[search] lemma vicary_5_6 : ((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) = (ρ_ (𝟙_ C ⊗ 𝟙_ C)).inv :=
by rw [vicary_6', ←assoc, iso.hom_inv_id, id_comp]

@[search] lemma vicary_7 : ((𝟙 (𝟙_ C)) ⊗ ((λ_ (𝟙_ C)).inv)) = ((ρ_ (𝟙_ C)).inv ⊗ (𝟙 (𝟙_ C))) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom :=
by obviously

@[search] lemma vicary_1_7 :
(ρ_ (𝟙_ C)).hom = (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom :=
by obviously.

@[search] lemma vicary_8 : (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom = (ρ_ (((𝟙_ C) ⊗ (𝟙_ C)) ⊗ (𝟙_ C))).inv ≫ ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) ≫ (ρ_ ((𝟙_ C) ⊗ ((𝟙_ C) ⊗ (𝟙_ C)))).hom :=
by obviously.

@[search] lemma vicary_14 : (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (ρ_ (((𝟙_ C) ⊗ (𝟙_ C)) ⊗ (𝟙_ C))).inv = (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ ((ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ⊗ (𝟙 (𝟙_ C))) :=
by rw [right_unitor_inv_naturality]

@[search] lemma vicary_9 : ((α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom ⊗ 𝟙 (𝟙_ C)) = (α_ ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C) (𝟙_ C)).hom ≫ (α_ (𝟙_ C) (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).inv) ≫ (α_ (𝟙_ C) ((𝟙_ C) ⊗ (𝟙_ C)) (𝟙_ C)).inv  :=
begin
  slice_rhs 1 2 { rw ←(monoidal_category.pentagon C (𝟙_ C) (𝟙_ C) (𝟙_ C) (𝟙_ C)) },
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
by obviously

@[search] lemma vicary_15 : (ρ_ ((𝟙_ C) ⊗ (𝟙_ C))).inv ≫ (((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).inv) ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ ((𝟙_ C) ⊗ ((𝟙_ C) ⊗ (𝟙_ C)))).hom ≫ ((𝟙 (𝟙_ C)) ⊗ (ρ_ (𝟙_ C)).hom) = 𝟙 _ :=
begin
  slice_lhs 1 2 { rw [←right_unitor_inv_naturality] },
  slice_lhs 2 3 { rw [iso.inv_hom_id] },
  obviously
end

lemma vicary' : (ρ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom :=
begin
  rw vicary_1_7,
  rw vicary_8,
  slice_lhs 1 2 { rw vicary_14 },
  slice_lhs 2 3 { rw vicary_9_13 },
  slice_lhs 1 4 { rw vicary_15 },
  rw id_comp,
end
