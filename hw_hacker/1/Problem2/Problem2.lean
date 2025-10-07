import Mathlib.Data.Set.Lattice

open Set

variable {X : Type} [Nonempty X] (R : X → X → Prop) (h_refl : Reflexive R) (h_symm : Symmetric R)

example : ⋃ (x : X), {y | R x y} = (univ : Set X) := by
  ext y
  constructor
  · intro h
    exact mem_univ y
  · intro h
    exact ⟨y, h_refl y⟩
