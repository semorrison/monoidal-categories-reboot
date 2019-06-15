import category_theory.monoidal.functor
import category_theory.tactics.obviously

open category_theory
open category_theory.monoidal_category

attribute [search]
tensor_id tensor_comp associator_naturality
left_unitor_naturality right_unitor_naturality
pentagon triangle

comp_tensor_id id_tensor_comp id_tensor_comp_tensor_id tensor_id_comp_id_tensor
left_unitor_tensor left_unitor_tensor_inv right_unitor_tensor right_unitor_tensor_inv
triangle_assoc_comp_left triangle_assoc_comp_right
triangle_assoc_comp_right_inv triangle_assoc_comp_left_inv
pentagon_inv
associator_inv_naturality
left_unitor_inv_naturality
right_unitor_inv_naturality

lax_monoidal_functor.μ_natural lax_monoidal_functor.left_unitality
lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

meta def rws : tactic string := `[rewrite_search {explain := tt}] >> pure ""
@[obviously] meta def obviously'' := tactic.tidy {tactics := tactic.tidy.default_tactics ++ [rws]}


notation `𝟙_` := tensor_unit
notation `α_` := associator
notation `λ_` := left_unitor
notation `ρ_` := right_unitor

universes v u

variables {C : Sort u} [𝒞 : monoidal_category.{v} C]
include 𝒞

@[search] lemma right_unitor_conjugation {X Y : C} (f : X ⟶ Y) : (ρ_ X).inv ≫ (f ⊗ (𝟙 (𝟙_ C))) ≫ (ρ_ Y).hom = f :=
by rw [right_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]

@[search] lemma left_unitor_conjugation {X Y : C} (f : X ⟶ Y) : (λ_ X).inv ≫ ((𝟙 (𝟙_ C)) ⊗ f) ≫ (λ_ Y).hom = f :=
by rw [left_unitor_naturality, ←category.assoc, iso.inv_hom_id, category.id_comp]
