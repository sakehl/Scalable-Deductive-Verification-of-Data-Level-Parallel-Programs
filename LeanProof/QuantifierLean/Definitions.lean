
import Mathlib.Tactic
import Mathlib.Data.Vector.Zip
import QuantifierLean.Prelude
open Mathlib


-- Definitions
def f (b: Int) (as xs:  Vector Int k) : Int :=
  b + ∑ i ∈ Fin.FinSet k, as.get i * xs.get i

def base (off: Int) (as: Mathlib.Vector Int (k+1)) (x': Int) : (i: Fin (k+1)) → Int
  | 0 => |x'-off|
  | ⟨i+1, lt⟩ =>
    let i' : Fin (k+1) := ⟨i, Nat.lt_trans (Nat.lt_add_one i) lt⟩
    base off as x' i' % as.get i'

def f_inv (off: Int) (as ls: Mathlib.Vector Int (k+1)) (x': Int): Vector Int (k+1) :=
  (Vector.fin_range (k+1)).map fun i => base off as x' i / |as.get i| + ls.get i

def prodSum: Mathlib.Vector Int k → Mathlib.Vector Int k → Int
  | ⟨[], _⟩, ⟨[], _⟩ => 0
  | ⟨a :: as, ha⟩, ⟨x :: xs, hx⟩ => a*x + prodSum ⟨as, congrArg Nat.pred ha⟩ ⟨xs, congrArg Nat.pred hx⟩

def upToProd {k: Nat} (as ls xs : Vector Int k) (i: Fin k) : Int :=
  prodSum (as.drop i) (Vector.zipWith (λ x l ↦ x-l) (xs.drop i) (ls.drop i))

def offset (b: Int) (as ls: Mathlib.Vector Int k): Int := b + prodSum as ls

def X (as ls : Vector Int (k+1)) (n : Int)
(C: Vector Int (k+1) → Prop)
: Set (Vector Int (k+1)) :=
  {xs : Vector Int (k+1) |
    xs.head < ls.head + n ∧
    (∀ i: Fin (k+1), ls.get i ≤ xs.get i) ∧
    (∀ i: Fin (k+1), ↑i<k →
      (0 < as.last → upToProd as ls xs (i+1)  < as.get i) ∧
      (as.last < 0 → as.get i < upToProd as ls xs (i+1)) )
    ∧ C xs
  }

def Y (as ls: Vector Int (k+1)) (off n: Int)
(C: Vector Int (k+1) → Prop)
: Set Int :=
  {x : Int |
    base off as x k % as.last = 0 ∧
    (0<as.last → 0 ≤ x-off ∧ x-off < as.head*n) ∧
    (as.last<0 → as.head*n < x-off ∧ x-off ≤ 0)
    ∧ C (f_inv off as ls x)
  }

def Props (as : Vector Int (k+1)) (n : Int)
: Prop :=
  0 < n ∧
  (∀ i, as.get i ≠ 0) ∧
  (∀ i, i<k → Int.sign (as.get i) = Int.sign (as.get (i+1)))


-- Helper definitions, on which most of the actual proves take place.
def f' (b: Int) (as ls xs:  Mathlib.Vector Int k) : Int := b + prodSum as (Vector.zipWith (λ x l ↦ x-l) xs ls)

def f_inv_el (off: Int) (as ls: Mathlib.Vector Int (k+1)) (x': Int) (i: Fin (k+1)): Int :=
  base off as x' i / |as.get i| + ls.get i

def f_inv'' (off: Int) (as ls: Mathlib.Vector Int (k+1)) (x': Int): (i: Fin (k+1)) → Vector Int (i+1)
  | 0 => f_inv_el off as ls x' ⟨k, Nat.lt_add_one k⟩ ::ᵥ Vector.nil
  | ⟨i+1, lt⟩ => f_inv_el off as ls x' ⟨k-(i+1), by omega⟩ ::ᵥ f_inv'' off as ls x' ⟨i, by omega⟩

def f_inv' (off: Int) (as ls: Mathlib.Vector Int (k+1)) (x': Int): Vector Int (k+1) :=
  f_inv'' off as ls x' ⟨k, by simp⟩

def ls_zero: Mathlib.Vector Int k := ⟨List.replicate k 0, by simp⟩

def implies {a: Prop} {b: Prop} (h2: a → b):  (a ∧ b) = a := by
  have right: a ∧ b → a := by
    intro ab
    exact ab.left
  have left: a → a ∧ b := by
    intro ha
    constructor
    · exact ha
    · exact h2 ha
  exact propext ⟨right, left⟩

def X2 (as ls : Vector Int (k+1)) (n : Int)
: Set (Vector Int (k+1)) :=
  {xs : Vector Int (k+1) |
    xs.head < ls.head + n ∧
    (∀ i: Fin (k+1), ls.get i ≤ xs.get i) ∧
    (∀ i: Fin (k+1), ↑i<k →
      (0 < as.last → upToProd as ls xs (i+1)  < as.get i) ∧
      (as.last < 0 → as.get i < upToProd as ls xs (i+1))
    )
  }

def Y2 (as: Vector Int (k+1)) (off n: Int)
: Set Int :=
  {x : Int |
    base off as x k % as.last = 0 ∧
    (0<as.last → 0 ≤ x-off ∧ x-off < as.head*n) ∧
    (as.last<0 → as.head*n < x-off ∧ x-off ≤ 0)
  }
