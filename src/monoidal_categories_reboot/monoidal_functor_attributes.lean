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

-- FIXME I need to put `explain := tt` back in here.
meta def rws : tactic string := tactic.rewrite_search {} >> pure ""
@[obviously] meta def obviously'' := tactic.tidy {tactics := tactic.tidy.default_tactics ++ [rws]}


notation `𝟙_` := tensor_unit
notation `α_` := associator
notation `λ_` := left_unitor
notation `ρ_` := right_unitor
