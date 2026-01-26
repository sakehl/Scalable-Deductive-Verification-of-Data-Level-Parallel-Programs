import Mathlib.Data.Vector.Defs

import QuantifierLean.Definitions
import QuantifierLean.Lemmas

open Mathlib

theorem f_bij_on' {l a: Vector Int (k+1)} (p: Props a n) (C: Vector Int (k+1) → Prop):
  Set.BijOn (f b a) (X a l n C) (Y a l (offset b a l) n C) := by
  rw [Y3_subset_Y2', ← cond_image (f_inv_on p) (f_bij_on p), ← X3_subset_X3']
  apply Set.BijOn.subset_left (f_bij_on p) (X3_subset_X2 a l n C)

theorem f_inv_on' {a l: Vector Int (k+1)} (p: Props a n):
  Set.InvOn (f_inv (offset b a l) a l) (f b a) (X a l n C) (Y a l (offset b a l) n C) := by
  apply Set.InvOn.mono (f_inv_on p)
  rw [X3_subset_X3']
  apply Set.inter_subset_left
  rw [Y3_subset_Y2']
  apply Set.inter_subset_left

-- Proves the main equivalence theorem
theorem equiv_quantifier'
  -- a is the array (length k+1) with the coefficients a_i for each x_i,
  -- l is the array (length k+1) with the lower bounds for each x_i
  (a l: Vector Int (k+1))
  (n: Int) -- n is the upper bound for the last element
  (C: Vector Int (k+1) → Prop)  -- C is an arbitrary condition on the quantifier
  (p: Props a n) -- p encodes the properties on a and n
  {α: Type} -- α is an arbitrary type, which models the values in the array/arbitrary data structure
  (A: Int → α) -- This models an array/arbitrary data structure which is indexed by an integer
  (R: α → Vector Int (k+1) → Prop): -- This models a random (boolean)function, which takes an array value
   -- This is the original quantifier
  (∀ xs: Vector Int (k+1), xs ∈ X a l n C → R (A (f b a xs)) xs) =
  -- This is the rewritten quantifer, where R (A x) can be taken as trigger
  (∀ x: Int, x ∈ (Y a l (offset b a l) n C) → R (A x) (f_inv (offset b a l) a l x))
  := by
  apply equiv_quantifier
  apply (f_inv_on' p)
  apply (f_bij_on' p)
