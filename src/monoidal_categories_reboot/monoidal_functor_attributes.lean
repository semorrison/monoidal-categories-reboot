import .monoidal_functor
import category_theory.tactics.obviously

open category_theory.monoidal

attribute [search]
monoidal_category.tensor_map_id monoidal_category.tensor_map_comp monoidal_category.associator_naturality
monoidal_category.left_unitor_naturality monoidal_category.right_unitor_naturality
monoidal_category.pentagon monoidal_category.triangle

interchange interchange_left_identity interchange_right_identity interchange_identities
triangle_1 triangle_2 triangle_3 triangle_4
left_unitor_product left_unitor_product_inv
right_unitor_product right_unitor_product_inv
pentagon_inv
associator_inv_naturality
left_unitor_inv_naturality
right_unitor_inv_naturality

lax_monoidal_functor.μ_natural lax_monoidal_functor.left_unitality
lax_monoidal_functor.right_unitality lax_monoidal_functor.associativity

meta def rws : tactic string := `[rewrite_search { explain := tt }] >> pure ""
@[obviously] meta def obviously'' := tactic.tidy {tactics := tidy.default_tactics ++ [rws]}

