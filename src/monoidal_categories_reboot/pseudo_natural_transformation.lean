import .monoidal_functor
import .endofunctors
import tidy.rewrite_search
import tactic.interactive

open category_theory
open tactic

universes u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

open category_theory.category

namespace tactic
open conv
private meta def conv_target' (c : conv unit) : tactic unit :=
do t ← target,
   (new_t, pr) ← c.convert t,
   replace_target new_t pr,
   try tactic.triv, try (tactic.reflexivity reducible)

namespace interactive
open interactive
open lean.parser

meta def slice_lhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic unit :=
do conv_target' (conv.interactive.to_lhs >> slice a b >> t)
meta def slice_rhs (a b : parse small_nat) (t : conv.interactive.itactic) : tactic unit :=
do conv_target' (conv.interactive.to_rhs >> slice a b >> t)
end interactive
end tactic

namespace category_theory.monoidal

open monoidal_category

variables {C : Type u₁} [𝒞 : monoidal_category.{u₁ v₁} C]
          {D : Type u₂} [𝒟 : monoidal_category.{u₂ v₂} D]
variables (F G : monoidal_functor C D)

structure pseudo_natural_transformation :=
(N : D)
(β : Π X : C, (F.obj X) ⊗ N ⟶ N ⊗ (G.obj X))
(β_natural' : Π {X X' : C} (f : X ⟶ X'), (F.map f ⊗ 𝟙 N) ≫ β X' = β X ≫ (𝟙 N ⊗ G.map f) . obviously)
(c' : Π X Y : C,
  β (X ⊗ Y) =
  ((F.μ X Y).inv ⊗ 𝟙 N) ≫ (associator _ _ _).hom ≫
    (𝟙 _ ⊗ (β Y)) ≫ (associator _ _ _).inv ≫
    ((β X) ⊗ 𝟙 _) ≫ (associator _ _ _).hom ≫ (𝟙 N ⊗ (G.μ X Y).hom) . obviously)

restate_axiom pseudo_natural_transformation.β_natural'
attribute [simp,search] pseudo_natural_transformation.β_natural
restate_axiom pseudo_natural_transformation.c'
attribute [simp,search] pseudo_natural_transformation.c

namespace pseudo_natural_transformation

def id : pseudo_natural_transformation F F :=
{ N := tensor_unit D,
  β := λ X, (right_unitor _).hom ≫ (left_unitor _).inv,
  β_natural' := sorry,
  c' := sorry }

@[simp] lemma id_N : (id F).N = tensor_unit D := rfl

variables {F G}

def β_nat_trans (σ : pseudo_natural_transformation F G) :
  F.to_functor ⋙ (tensor_on_right.obj σ.N) ⟹ G.to_functor ⋙ (tensor_on_left.obj σ.N) :=
{ app := λ X, σ.β X,
  naturality' := λ X Y f, σ.β_natural f }

variable {H : monoidal_functor C D}

attribute [trans] nat_trans.vcomp
section vcomp
variables (σ : pseudo_natural_transformation F G) (τ : pseudo_natural_transformation G H)

def vcomp : pseudo_natural_transformation F H :=
{ N := σ.N ⊗ τ.N,
  β := λ X, (associator _ _ _).inv ≫ (σ.β X ⊗ 𝟙 _) ≫ (associator _ _ _).hom ≫ (𝟙 _ ⊗ τ.β X) ≫ (associator _ _ _).inv,
  β_natural' := λ X X' f,
  begin
    rw ←monoidal_category.tensor_map_id,
    slice_lhs 1 2 { rw monoidal_category.associator_inv_naturality },
    slice_lhs 2 3 { rw [←interchange_left_identity, σ.β_natural, interchange_left_identity], },
    slice_lhs 3 4 { rw associator_naturality },
    slice_lhs 4 5 { rw [←interchange_right_identity, τ.β_natural, interchange_right_identity], },
    repeat { rw category.assoc },
    rw monoidal_category.associator_inv_naturality,
  end,
  c' := sorry
}


@[simp] lemma vcomp_N : (σ.vcomp τ).N = σ.N ⊗ τ.N := rfl

-- Hopefully this is eventually provable just by `rfl`
lemma vcomp_β_nat_trans :
  (σ.vcomp τ).β_nat_trans =
  (by calc
    F.to_functor ⋙ (tensor_on_right).obj (σ.N ⊗ τ.N) ⟹
        F.to_functor ⋙ ((tensor_on_right).obj σ.N) ⋙ ((tensor_on_right).obj τ.N) : whisker_left F.to_functor sorry
    ... ⟹ (F.to_functor ⋙ (tensor_on_right).obj τ.N) ⋙ ((tensor_on_right).obj σ.N) : sorry
    ... ⟹ (H.to_functor ⋙ (tensor_on_left).obj (σ.N ⊗ τ.N)) : sorry) :=
sorry
end vcomp

variables {E : Type u₃} [ℰ : monoidal_category.{u₃ v₃} E]
variables {K L : monoidal_functor D E}

attribute [trans] category.comp

section hcomp

variables (σ : pseudo_natural_transformation F G) (τ : pseudo_natural_transformation K L)

def hcomp  : pseudo_natural_transformation (F.comp K) (G.comp L) :=
{ N := (K.obj σ.N) ⊗ τ.N,
  β := λ X, by calc
  K.obj (F.obj X) ⊗ K.obj σ.N ⊗ τ.N
      ⟶ (K.obj (F.obj X) ⊗ K.obj σ.N) ⊗ τ.N   : (associator _ _ _).inv
  ... ⟶ (K.obj ((F.obj X) ⊗ σ.N)) ⊗ τ.N       : (K.μ _ _).hom ⊗ 𝟙 _
  ... ⟶ (K.obj (σ.N ⊗ (G.obj X))) ⊗ τ.N       : K.map (σ.β X) ⊗ 𝟙 _
  ... ⟶ (K.obj σ.N ⊗ (K.obj (G.obj X))) ⊗ τ.N : (K.μ _ _).inv ⊗ 𝟙 _
  ... ⟶ K.obj σ.N ⊗ (K.obj (G.obj X)) ⊗ τ.N   : (associator _ _ _).hom
  ... ⟶ K.obj σ.N ⊗ (τ.N ⊗ L.obj (G.obj X))   : 𝟙 _ ⊗ τ.β _
  ... ⟶ (K.obj σ.N ⊗ τ.N) ⊗ L.obj (G.obj X)   : (associator _ _ _).inv,
  β_natural' := sorry,
  c' := sorry }

@[simp] lemma hcomp_N : (σ.hcomp τ).N = (K.obj σ.N) ⊗ τ.N := rfl

end hcomp
end pseudo_natural_transformation

variables {F G}
variables (σ τ : pseudo_natural_transformation F G)

structure modification :=
(hom : σ.N ⟶ τ.N)
(w' : Π X : C, σ.β X ≫ (hom ⊗ 𝟙 _) = (𝟙 _ ⊗ hom) ≫ τ.β X . obviously)

restate_axiom modification.w'
attribute [search] modification.w

namespace pseudo_natural_transformation
namespace vcomp
variables {H K : monoidal_functor C D}
variables (ρ : pseudo_natural_transformation G H) (ν : pseudo_natural_transformation H K)

def associator_hom : modification ((σ.vcomp ρ).vcomp ν) (σ.vcomp (ρ.vcomp ν)) :=
{ hom := (associator _ _ _).hom,
  w' := sorry }
def associator_inv : modification (σ.vcomp (ρ.vcomp ν)) ((σ.vcomp ρ).vcomp ν) :=
{ hom := (associator _ _ _).inv,
  w' := sorry }

def left_unitor_hom : modification ((pseudo_natural_transformation.id _).vcomp σ) σ :=
{ hom := (left_unitor σ.N).hom,
  w' := sorry }
def left_unitor_inv : modification σ ((pseudo_natural_transformation.id _).vcomp σ) :=
{ hom := (left_unitor σ.N).inv,
  w' := sorry }
def right_unitor_hom : modification (σ.vcomp (pseudo_natural_transformation.id _)) σ :=
{ hom := (right_unitor σ.N).hom,
  w' := sorry }
def right_unitor_inv : modification σ (σ.vcomp (pseudo_natural_transformation.id _)) :=
{ hom := (right_unitor σ.N).inv,
  w' := sorry }
end vcomp

section
variables {A : Type u₃} [𝒜 : monoidal_category.{u₃ v₃} A]
variables {B : Type u₄} [ℬ : monoidal_category.{u₄ v₄} B]
variables {K L : monoidal_functor A B}
variables {M N : monoidal_functor B C}

variables (ρ : pseudo_natural_transformation K L)
variables (ν : pseudo_natural_transformation M N)
-- def hcomp_assoc_hom : modification ((ρ.hcomp ν).hcomp σ) (ρ.hcomp (ν.hcomp σ))

end

section exchange
variables {H : monoidal_functor C D}
variables (ρ : pseudo_natural_transformation G H)
variables {E : Type u₃} [ℰ : monoidal_category.{u₃ v₃} E]
variables {K L M : monoidal_functor D E}
variables (ν : pseudo_natural_transformation K L)
variables (κ : pseudo_natural_transformation L M)
def exchange : modification ((σ.vcomp ρ).hcomp (ν.vcomp κ)) ((σ.hcomp ν).vcomp (ρ.hcomp κ)) :=
{ hom := by calc
  K.obj (σ.N ⊗ ρ.N) ⊗ (ν.N ⊗ κ.N)
      ⟶ (K.obj σ.N ⊗ K.obj ρ.N) ⊗ (ν.N ⊗ κ.N) : (K.μ _ _).inv ⊗ 𝟙 _
  ... ⟶ K.obj σ.N ⊗ (K.obj ρ.N ⊗ ν.N) ⊗ κ.N : sorry
  ... ⟶ K.obj σ.N ⊗ (ν.N ⊗ L.obj ρ.N) ⊗ κ.N : 𝟙 _ ⊗ (ν.β _) ⊗ 𝟙 _
  ... ⟶ (K.obj (σ.N) ⊗ ν.N) ⊗ (L.obj (ρ.N) ⊗ κ.N) : sorry,
  w' := sorry
}
end exchange
end pseudo_natural_transformation

namespace modification

@[extensionality] lemma ext {f g : modification σ τ} (p : f.hom = g.hom) : f = g :=
begin
  cases f, cases g,
  congr,
  exact p
end

variables (ρ : pseudo_natural_transformation F G)

def id : modification σ σ :=
{ hom := 𝟙 _ }

@[simp] lemma id_hom : (id σ).hom = 𝟙 _ := rfl

variables {σ τ ρ}

def comp (f : modification σ τ) (g : modification τ ρ) : modification σ ρ :=
{ hom := f.hom ≫ g.hom }.

@[simp] lemma comp_hom (f : modification σ τ) (g : modification τ ρ) : (f.comp g).hom = f.hom ≫ g.hom := rfl

end modification

instance category_pseudo_natural_transformations : category (pseudo_natural_transformation F G) :=
{ hom := modification,
  id := modification.id,
  comp := λ _ _ _ f g, modification.comp f g }.

namespace pseudo_natural_transformation
@[simp] lemma id_hom (ρ : pseudo_natural_transformation F G) : ((𝟙 ρ) : modification ρ ρ).hom = 𝟙 _ := rfl
@[simp] lemma comp_hom {ρ σ τ : pseudo_natural_transformation F G} (f : ρ ⟶ σ) (g : σ ⟶ τ) :
  (f ≫ g).hom = f.hom ≫ g.hom := rfl
end pseudo_natural_transformation

namespace pseudo_natural_transformation.vcomp
variables {H K : monoidal_functor C D}
variables (ρ : pseudo_natural_transformation G H) (ν : pseudo_natural_transformation H K)

@[simp] def associator : ((σ.vcomp ρ).vcomp ν) ≅ (σ.vcomp (ρ.vcomp ν)) :=
{ hom := associator_hom _ _ _,
  inv := associator_inv _ _ _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
@[simp] def left_unitor : ((pseudo_natural_transformation.id _).vcomp σ) ≅ σ :=
{ hom := left_unitor_hom _,
  inv := left_unitor_inv _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }
@[simp] def right_unitor : (σ.vcomp (pseudo_natural_transformation.id _)) ≅ σ :=
{ hom := right_unitor_hom _,
  inv := right_unitor_inv _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end pseudo_natural_transformation.vcomp

namespace modification
open pseudo_natural_transformation

variables {σ τ}
variables {H : monoidal_functor C D}
variables {α β : pseudo_natural_transformation G H}

def vcomp (f : modification σ τ) (g : modification α β) : modification (σ.vcomp α) (τ.vcomp β) :=
{ hom := f.hom ⊗ g.hom,
  w' := by sorry }.

@[simp] lemma vcomp_hom (f : modification σ τ) (g : modification α β) : (f.vcomp g).hom = f.hom ⊗ g.hom := rfl

instance monoidal_category_pseudo_natural_endotransformations : monoidal_category (pseudo_natural_transformation F F) :=
{ tensor_obj := λ σ τ, σ.vcomp τ,
  tensor_hom := λ _ _ _ _ f g, f.vcomp g,
  tensor_unit := pseudo_natural_transformation.id F,
  associator := λ σ τ ρ, vcomp.associator σ τ ρ,
  left_unitor := λ σ, vcomp.left_unitor σ,
  right_unitor := λ σ, vcomp.right_unitor σ }.

variables {E : Type u₃} [ℰ : monoidal_category.{u₃ v₃} E]
variables {K L : monoidal_functor D E}
variables {γ δ : pseudo_natural_transformation K L}

def hcomp (f : modification σ τ) (g : modification γ δ) : modification (σ.hcomp γ) (τ.hcomp δ) :=
{ hom := K.map (f.hom) ⊗ g.hom,
  w' := λ X,
  begin
    dsimp [pseudo_natural_transformation.hcomp],
    simp,
    slice_rhs 1 2 { rw monoidal_category.associator_inv_naturality },
    repeat { rw category.assoc },
    apply congr_arg,
    sorry
  end }.

end modification

-- TODO obtain the Drinfeld centre from these, as a braided monoidal category

end category_theory.monoidal
