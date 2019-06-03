-- Copyright (c) 2018 Michael Jendrusch. All rights reserved.
import data.equiv.basic
import category_theory.category
import category_theory.functor
import category_theory.products
import category_theory.natural_isomorphism
import ..monoid_object
open category_theory
open tactic

universes u v

namespace category_theory

section

open monoidal_category

inductive nat_hom (m n : ℕ) : Type
| mk : nat_hom

@[simp] lemma equality {m n : ℕ} (f : nat_hom m n) : f = nat_hom.mk m n :=
by cases f; refl

@[simp] def nat_id (X : ℕ) : nat_hom X X :=
nat_hom.mk X X
@[simp] def nat_comp (X Y Z : ℕ) (f : nat_hom X Y) (g : nat_hom Y Z) : nat_hom X Z :=
nat_hom.mk X Z
@[simp] def nat_tensor_obj (X Y : ℕ) : ℕ := X + Y
@[simp] def nat_tensor_hom (A B C D : ℕ) (f : nat_hom A B) (g : nat_hom C D) :
  nat_hom (A + C) (B + D) := nat_hom.mk (A + C) (B + D)

instance naturals : monoidal_category (nat) :=
{ hom  := λ X Y, nat_hom X Y,
  id   := nat_id,
  comp := nat_comp,
  id_comp' := by tidy; rw equality f,
  comp_id' := by tidy; rw equality f,
  tensor_obj := nat_tensor_obj,
  tensor_hom := nat_tensor_hom,
  tensor_unit := nat.zero,
  left_unitor := λ X,
    { hom := nat_hom.mk (nat_tensor_obj 0 X) X,
      inv := nat_hom.mk X (nat_tensor_obj 0 X) },
  right_unitor := λ X,
    { hom := nat_hom.mk (nat_tensor_obj X 0) X,
      inv := nat_hom.mk X (nat_tensor_obj X 0) },
  associator := λ X Y Z,
    { hom := nat_hom.mk (nat_tensor_obj (nat_tensor_obj X Y) Z)
                        (nat_tensor_obj X (nat_tensor_obj Y Z)),
      inv := nat_hom.mk (nat_tensor_obj X (nat_tensor_obj Y Z))
                        (nat_tensor_obj (nat_tensor_obj X Y) Z)} }

end

instance nat_monoid_object (n : nat) : monoid_object n :=
{ unit    := nat_hom.mk 0 n,
  product := nat_hom.mk (n + n) n }

instance nat_comonoid_object (n : nat) : comonoid_object n :=
{ counit    := nat_hom.mk n 0,
  coproduct := nat_hom.mk n (n + n) }

instance nat_frobenius_object (n : nat) : frobenius_object n := {}

end category_theory
