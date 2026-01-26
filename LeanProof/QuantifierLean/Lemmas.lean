
import Mathlib.Tactic
import QuantifierLean.Definitions

import Mathlib.Data.Vector.Snoc
import Mathlib.Logic.Basic

open Mathlib

lemma zipWithWith {xs ls: List Int} (h: xs.length = ls.length)
 (f: Int → Int → Int)
 (f': Int → Int → Int)
 (h2: ∀ l x, f l (f' l x) = x)
 : List.zipWith (fun x l ↦ f l x) (List.zipWith (fun x l ↦ f' l x) xs ls) ls = xs := by
  revert ls h
  induction xs
  case nil =>
    simp
  case cons x xs ih =>
    intro ls h
    cases ls
    case nil =>
      simp_all
    case cons l ls =>
      rw [List.zipWith, List.zipWith]
      simp
      rw [h2 l x]
      simp
      apply ih
      simp at h
      exact h

lemma base_off {a: Vector Int (k+1)} : base off a x i = base 0 a (x-off) i := by
  cases' i with i isLt
  induction i
  case zero =>
    rw [base, base]
    simp
  case succ i ih =>
    rw [base, base]
    rw [ih]

lemma stupidCoercions {k j: Nat} (h: j < k): ↑(j + 1) = (↑j: Fin (k+1)).succ := by
  simp
  apply Fin.mk_eq_mk.mpr
  simp
  rw [Nat.mod_eq_of_lt]
  simp
  rw [Nat.mod_eq_of_lt]
  apply lt_trans h
  simp
  simp
  apply lt_trans h
  simp

theorem eq_or_not (a b: Int) : a=b ∨ a≠b := by apply eq_or_ne

@[simp]
lemma ls_zero_get: ls_zero.get i = 0 := by
  rw [ls_zero, Vector.get]
  simp

@[simp]
lemma ls_zero_head {k: Nat}: (@ls_zero (k+1)).head = 0 := by
  rw [← Vector.get_zero]
  exact ls_zero_get

@[simp]
lemma ls_zero_last {k: Nat}: (@ls_zero (k+1)).last = 0 := by
  rw [Vector.last]
  exact ls_zero_get

@[simp]
lemma ls_zero_zipWith {k: Nat} (x: Vector Int k):
 (Vector.zipWith (fun x l ↦ x - l) x (@ls_zero k) = x) := by
  apply Vector.toList_injective
  simp
  induction k
  case a.zero =>
    simp
  case a.succ k ih =>
    rw [ls_zero]
    simp
    have ih' := @ih x.tail
    rw [List.replicate_succ]
    match x with
    | ⟨xh::x, xl⟩ =>
    simp
    rw [ls_zero, Vector.tail] at ih'
    simp at ih'
    exact ih'

lemma drop_ls_zero {k j: Nat}:
  ((@ls_zero k).drop j) = @ls_zero (k-j) := by
    apply Vector.toList_injective
    cases j
    case a.zero =>
      simp
    case a.succ j =>
      simp
      rw [ls_zero, ls_zero]
      simp

lemma ls_zero_cons {k: Nat}:
  (@ls_zero (k+1)) = 0 ::ᵥ @ls_zero (k) := by
  apply Vector.toList_injective
  simp
  rw [ls_zero, ls_zero]
  simp
  rw [List.replicate_succ]

@[simp]
lemma ls_zero_drop_zipWith {k: Nat} {x: Vector Int k}:
 (Vector.zipWith (fun x l ↦ x - l) (x.drop j) ((@ls_zero k).drop j) = x.drop j) := by
  rw [drop_ls_zero]
  simp

lemma Vector.drop_zipWith {k: Nat} {x y: Vector Int k} {f: Int → Int → Int}:
 (Vector.zipWith f x y).drop j = Vector.zipWith f (x.drop j) (y.drop j) := by
  apply Vector.toList_injective
  simp
  rw [List.drop_zipWith]

@[simp]
lemma Vector.congr_arg (f: ∀ k, Mathlib.Vector α k → β) (v : Mathlib.Vector α n) (h : n = m) :
    f m (v.congr h) = f n v := by
  subst h
  rfl

@[simp]
lemma Vector.congr_arg₂ (f: ∀ k₁ k₂, Mathlib.Vector α₁ k₁ → Mathlib.Vector α₂ k₂ → β)
  (v₁ : Mathlib.Vector α₁ n₁) (v₂ : Mathlib.Vector α₂ n₂) (h₁ : n₁ = m₁) (h₂ : n₂ = m₂) :
    f m₁ m₂ (v₁.congr h₁) (v₂.congr h₂) = f n₁ n₂ v₁ v₂ := by
  subst h₁
  subst h₂
  rfl

@[simp]
lemma Vector.congr_same_arg₂ (f: ∀ k₁, Mathlib.Vector α₁ k₁ → Mathlib.Vector α₂ k₁ → β)
  (v₁ : Mathlib.Vector α₁ n₁) (v₂ : Mathlib.Vector α₂ n₁) (h₁ : n₁ = m₁) :
    f m₁ (v₁.congr h₁) (v₂.congr h₁) = f n₁ v₁ v₂ := by
  subst h₁
  rfl

@[simp]
lemma Vector.congr_arg₃
  (f: ∀ k₁ k₂ k₃, Mathlib.Vector α₁ k₁ → Mathlib.Vector α₂ k₂ → Mathlib.Vector α₃ k₃ → β)
  (v₁ : Mathlib.Vector α₁ n₁) (v₂ : Mathlib.Vector α₂ n₂) (v₃ : Mathlib.Vector α₃ n₃)
  (h₁ : n₁ = m₁) (h : n₂ = m₂) :
    f m₁ m₂ m₃ (v₁.congr h₁) (v₂.congr h₂) (v₃.congr h₃) = f n₁ n₂ n₃ v₁ v₂ v₃ := by
  subst h₁
  subst h₂
  subst h₃
  rfl

@[simp]
lemma Vector.drop_zero {a: Vector α (k)}:
  Vector.drop 0 a = a := by
  match a with
  | ⟨[], _⟩ => rfl
  | ⟨_::_, _⟩ => rfl

@[simp]
lemma Vector.drop_one {a: Vector α (k+1)}:
  Vector.drop 1 a = a.tail := by
  match a with | ⟨_::_, _⟩ => rfl

lemma Vector.drop_all {a: Vector α k}:
  Vector.drop k a = Vector.nil.congr (by simp) := by
  apply Vector.toList_injective
  simp

lemma Vector.drop_tail {a: Vector α (k+1)}:
  Vector.drop (i+1) a = (Vector.drop (i) a.tail).congr (Nat.add_comm 1 i ▸ Nat.sub_sub (k+1) 1 i) := by
  match a with | ⟨_::_, _⟩ => rfl

lemma drop_congr: i < k+1 → (k + 1 - (i + 1) + 1 = k + 1 - i) := by
  omega

@[simp]
lemma Vector.tail_cons' {α: Type} {n: Nat} {a_h: α} {a_tail: List α}
  {a_len: (a_h::a_tail).length = n+1}:
  Vector.tail (⟨a_h:: a_tail, a_len⟩: Vector α (n+1)) =  ⟨a_tail, by simp at a_len; rw [a_len]; simp⟩ := by
  rw [Vector.tail]

@[simp]
lemma ls_zero_tail_zipWith {k: Nat} {x: Vector Int (k)}:
 (Vector.zipWith (fun x l ↦ x - l) x (@ls_zero (k+1)).tail = x) := by
  rw [ls_zero]
  conv =>
    pattern List.replicate _ _
    rw [List.replicate_succ]
  simp
  rw [<- ls_zero]
  simp

lemma Vector.drop_eq_get_cons {a: Vector α (k+1)} (h : i < k+1):
  Vector.drop i a = (a.get ⟨i,h⟩  ::ᵥ Vector.drop (i+1) a).congr (drop_congr h) := by
    match a with
    | ⟨a::as, al⟩ =>
    apply Vector.toList_injective
    simp
    rw [<- al] at h
    rw [List.drop_eq_getElem_cons h]
    rfl

@[simp]
lemma Vector.congr_zipWith {f : α → β → γ} {a: Mathlib.Vector α n} {x: Mathlib.Vector β n} (h : n = m) :
    Vector.zipWith f (a.congr h) (x.congr h) = (Vector.zipWith f a x).congr h := by
  subst h
  rfl

@[simp]
lemma Vector.zipWith_cons {f : α → β → γ} {a: Mathlib.Vector α n} {x: Mathlib.Vector β n} :
    Vector.zipWith f (a' ::ᵥ a) (x' ::ᵥ x) = f a' x' ::ᵥ (Vector.zipWith f a x) := by
  rfl



@[simp]
lemma Vector.tail_last {n: Nat} (v: Vector α (n+1+1)): v.tail.last = v.last := by
  repeat rw [Vector.last]
  rw [Mathlib.Vector.get_tail]
  rfl

lemma Vector.drop_all_but_one {a: Vector α (k+1)}:
  Vector.drop k a = (a.last ::ᵥ Vector.nil).congr
    ((rfl: Nat.succ 0 = Nat.succ 0) ▸ Nat.one_eq_succ_zero ▸ (Nat.add_sub_self_left k 1).symm) := by
  induction k
  case zero =>
    apply Vector.toList_injective
    rw [Vector.drop, Vector.last]
    simp
    match a with | ⟨_::_, _⟩ => rfl
  case succ k ih =>
    rw [Vector.drop_tail]
    have ih' := @ih a.tail
    rw [ih']
    simp
    rfl

@[simp]
lemma Vector.tail_last' {α: Type} {n: Nat} {a_h: α} {a_tail: List α}
  {a_len: (a_h::a_tail).length = n+1+1} {a_tail_len: a_tail.length = n+1}:
  Vector.last (⟨a_h :: a_tail, a_len⟩: Vector α (n+1+1)) =
  Vector.last (⟨a_tail, a_tail_len⟩: Vector α (n+1)) := by
  rw [Vector.last, Vector.last]
  rw [Vector.get, Vector.get]
  simp
  conv =>
    lhs
    arg 2
    rw [a_tail_len]
  simp

lemma Vector.tail_get_head {α: Type} {n: Nat} (v: Vector α (n+1+1)): v.get 1 = v.tail.head := by
  rw [← Vector.get_zero, Vector.get_tail]
  rfl

@[simp]
lemma Vector.get_head {α: Type} {a: α} {n: Nat} {as: List α} {a_len: (a::as).length = n+1}
: @Vector.head α n ⟨a:: as, a_len⟩ = a := by
  rw [Vector.head]

@[simp]
lemma Vector.get_head' {α: Type} {a: α} {n: Nat} {as: List α} {a_len: (a::as).length = n+1}
: @Vector.get α (n+1) ⟨a:: as, a_len⟩ 0 = a := by
  rw [Vector.get_zero]
  rw [Vector.head]

lemma Vector.get_one_cons {α: Type} {a: α} {n: Nat} {as: List α} {a_len: (a::as).length = n+1+1}
: @Vector.get α (n+1+1) ⟨a:: as, a_len⟩ 1 = @Vector.head α n ⟨as, by rw [List.length] at a_len; simp at a_len; exact a_len⟩ := by
  rw [<- Vector.get_zero]
  simp [Vector.get]
  rfl

lemma Vector.get_succ_cons :
 @Vector.get α (n+1) ⟨a_h :: a_tail, a_len⟩ ⟨k + 1, hk⟩ = @Vector.get α (n) ⟨a_tail, by simp at a_len; apply a_len⟩ ⟨k, by omega⟩ := by
  rw [Vector.get, Vector.get]
  simp

lemma upToProd_comp {l a x: Vector Int (k)}:
  upToProd a ls_zero (Vector.zipWith (fun x l ↦ x - l) x l) i = upToProd a l x i := by
  rw [upToProd, upToProd]
  simp
  rw [Vector.drop_zipWith]

lemma Vector.zipWith_tail {f : α → β → γ} {a: Mathlib.Vector α (n+1)} {x: Mathlib.Vector β (n+1)} :
  Vector.zipWith f a.tail x.tail = (Vector.zipWith f a x).tail := by
  apply Vector.toList_injective
  simp


lemma last_zero {a: Vector Int (k+1+1)} (h: 0 ≠ a.last) : 0 ≠ a.tail.last := by
  rw [Vector.last, Vector.get_tail]
  exact h

lemma smaller_n {a: Vector Int (k+1+1)} (h: ∀ i, 0 < a.get i):
  (∀ i, 0 < a.tail.get i) := by
  intro j
  rw [Mathlib.Vector.get_tail]
  apply h

lemma ff_l3 {j k: Nat} (h: j<k) : ((↑j: Fin (k+1)).succ: Fin (k + 1).succ) = ↑(j+ 1) := by
  have jkk: j < k + 1 := by
    exact Nat.lt_trans h (Nat.lt_add_one k)
  simp
  apply Fin.mk_eq_mk.mpr
  simp
  rw [Nat.mod_eq_of_lt]
  rw [Nat.mod_eq_of_lt]
  simp
  repeat assumption

lemma ff_l4 (h: j<k) : j+1 < k+1 := by
  exact Nat.add_lt_add_right h 1

lemma ff_l5 {j k: Nat} (h: j<k) : (↑(j + 1) + 1: Fin (k + 1 + 1)) = ((↑j: Fin (k+1)) + 1).succ := by
  simp
  apply Fin.mk_eq_mk.mpr
  simp
  repeat rw [Nat.mod_eq_of_lt]
  exact Nat.add_lt_add_right h 1

  apply @ff_l4 (j+1) (k+1)
  exact Nat.add_lt_add_right h 1

lemma Vector.head_last {a: Vector Int 1}: a.head = a.last := by
  rw [Mathlib.Vector.last, ← Mathlib.Vector.get_zero]
  rfl

@[simp]
lemma vector_head_1 {head: Int}:
  Vector.head ⟨head :: xs, by rw[List.length]⟩ = head := by
    rw [Vector.head]

@[simp]
lemma vector_last_1 {head: Int}:
  Vector.last ⟨[head], by rw[List.length]⟩ = head := by
    rw [Vector.last, Vector.get]
    simp

lemma Vector.take_one (l: Vector Int (1)):
    Vector.take 1 l = l := by
    apply Vector.toList_injective
    rw [Mathlib.Vector.toList_take]
    simp

lemma Mathlib.Vector.get_cons_succ' {α : Type u_1} {n : ℕ} (i : Nat) {Lt: i < n} (a : α) (v : Mathlib.Vector α n)  :
(a ::ᵥ v).get ⟨i+1, Nat.add_one_lt_add_one_iff.mpr Lt⟩ = v.get ⟨i, Lt⟩ := by
  have eq: (⟨i+1, Nat.add_one_lt_add_one_iff.mpr Lt⟩: Fin (n+1)) = (⟨i, Lt⟩ : Fin n).succ := by
    apply Fin.mk_eq_mk.mpr
    simp
  rw [eq, Mathlib.Vector.get_cons_succ]

lemma f_get_is_f_inv_el' {k: Nat} {l a: Vector Int (k+1)} {j: Fin (k+1)} (i: Fin (↑j+1)):
  (f_inv'' b a l x j).get i = f_inv_el b a l x ⟨k-j+↑i, by omega⟩ := by
  cases' j with j isLt
  induction j
  case zero =>
    rw [f_inv'']
    simp
  case succ j ih =>
    simp_all
    cases' i with i isLtI
    match i with
    | 0 =>
      rw [f_inv'']
      simp
    | i+1 =>
      rw [f_inv'']
      rw [Mathlib.Vector.get_cons_succ']
      simp_all
      apply congrArg
      apply Fin.mk_eq_mk.mpr
      simp_all
      omega
      omega

lemma f_get_is_f_inv_el {l a: Vector Int (k+1)}:
  (f_inv' b a l x).get i = f_inv_el b a l x i := by
  rw [f_inv']
  rw [f_get_is_f_inv_el']
  simp

@[simp]
lemma prodSum_cons : prodSum (a' ::ᵥ a) (x' ::ᵥ x) = a'*x' + prodSum a x := by
  match a, x with
  | ⟨_, _⟩, ⟨_,_⟩ =>
  rw [Vector.cons, Vector.cons]
  rw [prodSum]

lemma prodSum_cons' : prodSum a x = a.head*x.head + prodSum a.tail x.tail := by
  match a, x with
  | ⟨_::_, _⟩, ⟨_::_,_⟩ =>
  rw [prodSum]
  rfl

lemma upToPredRec {as ls xs : Vector Int (k+1)} (i': Nat) (i: Fin k) (h: i' = i):
  (upToProd as ls xs (i'+1: Nat)) =
  (upToProd as.tail ls.tail xs.tail i) := by
  cases' as using Vector.casesOn with cons a as
  cases' ls using Vector.casesOn with cons l ls
  cases' xs using Vector.casesOn with cons x xs
  rw [Vector.tail_cons, Vector.tail_cons, Vector.tail_cons, upToProd, upToProd]
  have eq: ↑(↑(i' + 1): Fin (k+1)) = i'+1 := by rw [h]; simp
  rw [eq, h, Vector.drop_tail, Vector.drop_tail, Vector.drop_tail]
  simp

lemma upToPredRec2 {as ls xs : Vector Int (k+1)} (i: Fin (k+1)) (h: ↑i<k):
  (upToProd as ls xs (i+1)) =
  (upToProd as.tail ls.tail xs.tail ⟨↑i,h⟩) := by
  rw [<- upToPredRec (↑i)]
  simp
  simp



lemma upToPredRec' {as ls xs : Vector Int (k+1)} (i: Fin (k+1)) (h1: ↑i<k):
  (upToProd as ls xs i) =
  as.get i * (xs.get i - ls.get i) + upToProd as ls xs (i+1) := by
  rw [upToProd, upToProd]
  have h': ↑i < k + 1 := by omega
  rw [Vector.drop_eq_get_cons h', Vector.drop_eq_get_cons h', Vector.drop_eq_get_cons h']
  have eq: (↑(i + 1): Nat) = (↑i + 1) := by
    rw [Fin.val_add]
    simp
    omega
  rw [eq]
  simp

lemma upToProd_size2 {as ls xs : Vector Int (k+1)}:
  upToProd as ls xs k = as.last * (xs.last - ls.last) := by
  induction k
  case zero =>
    match as, ls, xs with
    | ⟨[a1], a_l⟩, ⟨[l1], l_l⟩, ⟨[x1], x_l⟩ =>
    rw [upToProd, Vector.drop, Vector.drop, Vector.drop, Vector.last, Vector.last, Vector.last, Vector.get, Vector.get, Vector.get]
    simp
    conv =>
      lhs
      arg 2
      rw [Vector.zipWith]
      simp
    rw [prodSum, prodSum]
    simp
  case succ k ih =>
    have ih' := @ih as.tail ls.tail xs.tail
    rw [upToPredRec k k (by simp)]
    rw [ih', Vector.tail_last, Vector.tail_last, Vector.tail_last]

lemma bounded {a b c: Int} (h0: b ≠ 0) (h0': 0 < b) (h1: a*b < c) : a < (c+b-1)/b := by
  have h3 := Int.le_ediv_of_mul_le h0' (Int.le_sub_one_of_lt h1)
  rw [Int.add_comm, Int.add_sub_assoc]
  rw [Int.add_ediv_of_dvd_left (by simp)]
  rw [Int.ediv_self h0]
  rw [Int.lt_iff_add_one_le]
  nth_rewrite 2 [Int.add_comm]
  apply Int.add_le_add_right h3 1

lemma a_same_sign_head (as: Vector Int (k+1)) (h: ∀ i, i<k → Int.sign (as.get i) = Int.sign (as.get (i+1))):
  ∀ j, Int.sign as.head = Int.sign (as.get j) := by
  intro j
  match j with
  | ⟨j, lt⟩ =>
  induction j
  case zero =>
    simp
  case succ j ih =>
    have lt' : j<k+1 := Nat.lt_of_succ_lt lt
    have ih' := ih lt'
    have lt'' := Nat.lt_of_add_lt_add_right lt
    have h' := h j lt''
    have eq: (⟨j + 1, lt⟩: Fin (k+1)) = (↑j + 1) := by
      have h'' := Nat.zero_lt_of_lt lt''
      apply Fin.mk_eq_mk.mpr
      repeat rw [Nat.mod_eq_of_lt]
      simp
      repeat assumption
      repeat rw [Nat.mod_eq_of_lt]
      repeat assumption
      simp
      repeat assumption
    have eq2: (⟨j, lt'⟩: Fin (k+1)) = (↑j) := by
      apply Fin.mk_eq_mk.mpr
      repeat rw [Nat.mod_eq_of_lt]
      assumption
    rw [eq, ← h', ← eq2, ih']

lemma a_same_sign_last (as: Vector Int (k+1)) (h: ∀ i, i<k → Int.sign (as.get i) = Int.sign (as.get (i+1))):
  ∀ j, Int.sign as.last = Int.sign (as.get j) := by
  intro j
  match j with
  | ⟨j, lt⟩ =>
  induction j
  case zero =>
    rw [Vector.last]
    simp
    exact (a_same_sign_head as h (Fin.last k)).symm
  case succ j ih =>
    have lt' : j<k+1 := Nat.lt_of_succ_lt lt
    have ih' := ih lt'
    have lt'' := Nat.lt_of_add_lt_add_right lt
    have h' := h j lt''
    have eq: (⟨j + 1, lt⟩: Fin (k+1)) = (↑j + 1) := by
      have h'' := Nat.zero_lt_of_lt lt''
      apply Fin.mk_eq_mk.mpr
      repeat rw [Nat.mod_eq_of_lt]
      simp
      repeat assumption
      repeat rw [Nat.mod_eq_of_lt]
      repeat assumption
      simp
      repeat assumption
    have eq2: (⟨j, lt'⟩: Fin (k+1)) = (↑j) := by
      apply Fin.mk_eq_mk.mpr
      repeat rw [Nat.mod_eq_of_lt]
      assumption
    rw [eq, ← h', ← eq2, ih']

lemma same_pos (h: Int.sign a = Int.sign b) (h2: 0 < a) : 0 < b := by
  rw [(Int.sign_eq_one_iff_pos a).mpr h2 ] at h
  exact (Int.sign_eq_one_iff_pos b).mp h.symm

lemma same_neg (h: Int.sign a = Int.sign b) (h2: a < 0) : b < 0 := by
  rw [(Int.sign_eq_neg_one_iff_neg  a).mpr h2 ] at h
  exact (Int.sign_eq_neg_one_iff_neg b).mp h.symm

lemma a_same_pos (as: Vector Int (k+1)) (h: ∀ i, i<k → Int.sign (as.get i) = Int.sign (as.get (i+1))) (h2: 0 < as.last):
  ∀ j, 0 < as.get j := by
  intro j
  have h3 := a_same_sign_last as h j
  exact same_pos h3 h2

lemma a_same_neg (as: Vector Int (k+1)) (h: ∀ i, i<k → Int.sign (as.get i) = Int.sign (as.get (i+1))) (h2: as.last < 0):
  ∀ j, as.get j < 0 := by
  intro j
  have h3 := a_same_sign_last as h j
  exact same_neg h3 h2



lemma upToProdSign {as ls: Vector Int (k+1)} (p: Props as n):
  ∀ xs ∈ X2 as ls n,
  ∀ (j: Fin (k+1)),
  (as.last > 0 → 0 ≤ upToProd as ls xs j) ∧
  (as.last < 0 → upToProd as ls xs j ≤ 0) := by
  intro xs xinX j
  match xinX, p with
  | ⟨_ ,h2, _⟩, ⟨_, _, h6⟩ =>
  match j with
  | ⟨j,lt⟩ =>
  have t: j ≤ k := Nat.le_of_lt_add_one lt
  induction t using Nat.decreasingInduction
  case self _ =>
    rw [upToProd]
    rw [Vector.drop_all_but_one, Vector.drop_all_but_one, Vector.drop_all_but_one]
    simp
    rw [Vector.nil, Vector.zipWith]
    simp
    rw [prodSum]
    simp
    constructor
    case left =>
      intro a_pos
      apply Int.mul_nonneg
      · exact Int.le_of_lt a_pos
      · have h2' := h2 (Fin.last k)
        exact Int.sub_nonneg_of_le h2'
    case right =>
      intro a_neg
      apply Int.mul_nonpos_of_nonpos_of_nonneg
      · exact Int.le_of_lt a_neg
      · have h2' := h2 (Fin.last k)
        exact Int.sub_nonneg_of_le h2'
  case of_succ _ j lt' ih =>
    have ih' := ih (Nat.add_one_lt_add_one_iff.mpr lt')
    have eq: (⟨j + 1, Nat.add_one_lt_add_one_iff.mpr lt'⟩: Fin (k + 1)) = (⟨j, lt⟩ + 1) := by
      apply Fin.mk_eq_mk.mpr
      simp
      rw [Nat.mod_eq_of_lt]
      simp
      assumption
    rw [upToPredRec']
    · simp
      constructor
      case left =>
        intro a_pos
        apply Int.add_nonneg
        · apply Int.mul_nonneg
          · have a_pos' := a_same_pos as h6 a_pos ⟨j, lt⟩
            exact Int.le_of_lt a_pos'
          · have h2' := h2 ⟨j, lt⟩
            exact Int.sub_nonneg_of_le h2'
        · rw [← eq]
          exact ih'.left a_pos
      case right =>
        intro a_neg
        apply Int.add_nonpos
        · apply Int.mul_nonpos_of_nonpos_of_nonneg
          · have a_neg' := a_same_neg as h6 a_neg ⟨j, lt⟩
            exact Int.le_of_lt a_neg'
          · have h2' := h2 ⟨j, lt⟩
            exact Int.sub_nonneg_of_le h2'
        · rw [← eq]
          exact ih'.right a_neg
    · simp
      assumption

lemma prodSumSign (as xs: Vector Int (k+1)) (p: Props as n):
  xs ∈ X2 as ls_zero n →
  (0 < as.last → 0 ≤ prodSum as xs) ∧
  (as.last < 0 → prodSum as xs ≤ 0) := by
  intro xsinX
  have almost := upToProdSign p xs xsinX 0
  rw [upToProd] at almost
  simp at almost
  exact almost

lemma my_lemma {a b c: Int}: 0≤b → a+b<c → a<c := by
  intro h1 h2
  omega

lemma my_lemma_neg {a b c: Int}: b≤0 → c<a+b → c<a := by
  intro h1 h2
  omega

lemma contr_lemma {j k : Nat} (h: j < k) (h': k < j+1) : False := by
  omega

lemma upToPred_lemma (as ls : Vector Int (k+1)) (p: Props as n):
  ∀ (j: Fin (k+1)), ∀ xs ∈ X2 as ls n, ↑j<k →
  (as.last > 0 → as.get (j+1) * (xs.get (j+1) - ls.get (j+1)) < as.get j) ∧
  (as.last < 0 → as.get j < as.get (j+1) * (xs.get (j+1) - ls.get (j+1)))
   := by
  intro j x xinX jk
  match xinX with
  | ⟨_ ,_, h3⟩ =>
  match Nat.lt_trichotomy (j+1) k with
  | Or.inl jk2 =>
    have eq': (↑(j + 1): Nat) = j + 1 := by
      rw [Fin.val_add]
      simp
      exact jk
    have jk'': ↑(j + 1) < k := by
      rw [<- eq'] at jk2
      assumption
    have h3':= (h3 j jk)
    rw [upToPredRec' (j+1) jk''] at h3'
    have h' := (upToProdSign p x xinX (j+1+1))
    constructor
    case left =>
      intro a_pos
      have h3':= h3'.left a_pos
      apply my_lemma (h'.left a_pos) at h3'
      exact h3'
    case right =>
      intro a_neg
      have h3':= h3'.right a_neg
      apply my_lemma_neg (h'.right a_neg) at h3'
      exact h3'
  | Or.inr (Or.inr jkk) =>
    absurd (contr_lemma jk jkk)
    simp
  | Or.inr (Or.inl jkk) =>
    have eq: (j + 1) = k := by
      apply Fin.mk_eq_mk.mpr
      simp
      rw [jkk]
      simp
    have h3':= (h3 j jk)
    have eq': ↑(↑k: Fin (k+1)) = k := by simp
    rw [eq, upToProd, eq'] at h3'
    rw [Vector.drop_all_but_one, Vector.drop_all_but_one, Vector.drop_all_but_one] at h3'
    simp at h3'
    rw [Vector.nil, Vector.zipWith] at h3'
    simp at h3'
    rw [prodSum] at h3'
    simp at h3'
    rw [eq]
    simp
    constructor
    case left =>
      intro a_pos
      exact h3'.left a_pos
    case right =>
      intro a_neg
      exact h3'.right a_neg

lemma x_bounded (as ls : Vector Int (k+1)) (n : Int)
  (p: Props as n):
  ∀ (j: Fin (k+1)), ∀ xs ∈ X2 as ls n, ↑j<k →
  (xs.get (j+1) - ls.get (j+1)  <
   (|as.get j| + |as.get (j+1)| -1) / |as.get (j+1)|)
  := by
  intro j x xinX jk'
  have h := upToPred_lemma as ls p j x xinX jk'
  match p with
  | ⟨_, h5, h6⟩ =>
  match Int.lt_or_lt_of_ne (h5 (Fin.last k)) with
  | Or.inr a_pos =>
    have h:= h.left a_pos
    have a1_pos := a_same_pos as h6 a_pos (j+1)
    have a0_pos := a_same_pos as h6 a_pos j
    rw [abs_of_pos a1_pos, abs_of_pos a0_pos]
    apply bounded
    · apply h5 (j+1)
    · apply a1_pos
    · rw [Int.mul_comm]
      exact h
  | Or.inl a_neg =>
    have h:= h.right a_neg
    have a1_neg := a_same_neg as h6 a_neg (j+1)
    have a0_neg := a_same_neg as h6 a_neg j
    rw [abs_of_neg a1_neg, abs_of_neg a0_neg]
    apply bounded
    · simp
      apply h5 (j+1)
    · simp
      apply a1_neg
    · rw [Int.mul_comm]
      simp
      exact h

lemma base_lemma (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1)
 (h2: as.head ≠ 0):
  base 0 as x' ⟨i, by omega⟩ % as.get ⟨i, by omega⟩ =
  base 0 as.tail (|x'| % as.head) ⟨i, h⟩ := by
    revert x'
    induction i
    case zero =>
      intro x'
      rw [base, base]
      simp
      have h' := Int.emod_nonneg (|x'|) h2
      rw [abs_of_nonneg h']
    case succ i ih =>
      intro x'
      have h': i < k+1 := by omega
      rw [base, base]
      simp
      rw [ih h']


lemma base_lemma2 (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  base 0 as x' ⟨i, by omega⟩ % as.get ⟨i, by omega⟩ =
  base 0 as.tail (-(- (x') % as.head)) ⟨i, h⟩ := by
    revert x'
    induction i
    case zero =>
      intro x' x3
      rw [base, base]
      simp
      have h' := Int.emod_nonneg ((-x')) h2
      rw [abs_of_nonpos x3]
      rw [abs_of_nonneg h']
    case succ i ih =>
      intro x' x3
      have h': i < k+1 := by omega
      rw [base, base]
      simp
      rw [ih h']
      omega


lemma f_inv_h_pred {k: Nat} (i: Nat) (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0):
  f_inv'' 0 as ls_zero x' ⟨i, by omega⟩ = f_inv'' 0 as.tail ls_zero (|x'| % as.head) ⟨i, h⟩ := by
    revert x' as
    induction i
    case zero =>
      intro as x' h2
      rw [f_inv'', f_inv'', f_inv_el, f_inv_el]
      simp
      rw [base]
      rw [base_lemma as x']
      simp
      exact h2
    case succ i ih =>
      intro as x' h2
      rw [f_inv'', f_inv'', f_inv_el, f_inv_el]
      have eq: k + 1 - (i + 1) = k -(i+1) + 1 := by omega
      conv =>
        pattern k + 1 - (i + 1)
        rw [eq]
      rw [base]
      rw [base_lemma as x']
      simp
      have h': i < k+1 := Nat.lt_trans (Nat.lt_add_one i) h
      rw [ih h' as x' h2]
      have eq2: k - (i + 1) + 1 = k - i := by omega
      conv =>
        pattern k - (i + 1) + 1
        rw [eq2]
      omega

lemma f_inv_h_pred2 {k: Nat} (i: Nat) (as: Mathlib.Vector Int (k+1+1)) (x': Int) (h: i < k+1) (h2: as.head ≠ 0) (h3: x' ≤ 0):
  f_inv'' 0 as ls_zero x' ⟨i, by omega⟩ = f_inv'' 0 as.tail ls_zero (-(- (x') % as.head)) ⟨i, h⟩ := by
    revert x' as
    induction i
    case zero =>
      intro as x' h2 h3
      rw [f_inv'', f_inv'', f_inv_el, f_inv_el]
      simp
      rw [base]
      rw [base_lemma2 as x']
      simp
      exact h2
      exact h3
    case succ i ih =>
      intro as x' h2 h3
      rw [f_inv'', f_inv'', f_inv_el, f_inv_el]
      have eq: k + 1 - (i + 1) = k -(i+1) + 1 := by omega
      conv =>
        pattern k + 1 - (i + 1)
        rw [eq]
      rw [base]
      rw [base_lemma2 as x']
      simp
      have h': i < k+1 := Nat.lt_trans (Nat.lt_add_one i) h
      rw [ih h' as x' h2]
      have eq2: k - (i + 1) + 1 = k - i := by omega
      conv =>
        pattern k - (i + 1) + 1
        rw [eq2]
      omega
      omega
      exact h3

lemma f_inv_pred {as: Mathlib.Vector Int (k+1+1)} {x': Int} (h2: as.head ≠ 0):
  (f_inv' 0 as ls_zero x') = |x'| / |as.head| ::ᵥ f_inv' 0 as.tail ls_zero (|x'| % as.head) := by
  rw [f_inv', f_inv', f_inv'']

  rw [f_inv_h_pred k as x' (by simp) h2]
  rw [f_inv_el, ]
  -- simp
  conv =>
    lhs
    arg 1
    arg 1
    arg 1
    arg 4
    arg 1
    simp
  rw [base]
  simp


lemma f_inv_pred2 {as: Mathlib.Vector Int (k+1+1)} {x': Int} (h2: as.head ≠ 0) (h3: x' ≤ 0):
  (f_inv' 0 as ls_zero x') = |x'| / |as.head| ::ᵥ f_inv' 0 as.tail ls_zero (-(- x' % as.head)) := by
  rw [f_inv', f_inv', f_inv'']
  rw [f_inv_h_pred2 k as x' (by simp) h2 h3]
  rw [f_inv_el, ]
  conv =>
    lhs
    arg 1
    arg 1
    arg 1
    arg 4
    arg 1
    simp
  rw [base]
  simp


theorem ediv_nonneg' {a b : Int} (Ha : a ≤ 0) (Hb : b ≤ 0) : 0 ≤ a / b := by
  match a, b with
  | Int.ofNat a, b =>
    match Int.le_antisymm Ha (Int.ofNat_zero_le a) with
    | h1 =>
      rw [h1, Int.zero_ediv]
  | a, Int.ofNat b =>
    match Int.le_antisymm Hb (Int.ofNat_zero_le  b) with
    | h1 =>
      rw [h1, Int.ediv_zero]
  | Int.negSucc a, Int.negSucc b =>
    exact Int.le_add_one (Int.ediv_nonneg (Int.ofNat_zero_le a) (Int.le_trans (Int.ofNat_zero_le b) (Int.le.intro 1 rfl)))

lemma Int.mul_add_lt {a x b n: Int} (h1: x<n) (h2: 0 < a) (h3: b < a) :
  a*x+b < a*n := by
  have h5: a*(x+1) ≤ a*n := Int.mul_le_mul_of_nonneg_left
     (Int.add_one_le_of_lt h1) (Int.le_of_lt h2)
  rw [Int.mul_add, Int.mul_one] at h5
  have h6: a*x + b < a*x + a := by
    apply Int.add_lt_add_left h3
  apply Int.lt_of_lt_of_le h6 h5

lemma Int.mul_add_lt2 {a x b n: Int} (h1: x<n) (h2: a < 0) (h3: a < b) :
  a*n < a*x+b := by
  have rev: -a*x-b < -a*n := by
    apply Int.mul_add_lt h1 (Int.neg_pos_of_neg h2)
    apply Int.lt_of_neg_lt_neg
    simp
    exact h3
  apply Int.lt_of_neg_lt_neg
  rw [Int.neg_add]
  simp at rev
  exact rev

lemma a_sign_tail {a: Vector Int (k+1+1)} {atail: Vector Int (k+1)}
  (h1: atail = a.tail)
  (h: ∀ i, i<k+1 → (a.get i).sign = (a.get (i+1)).sign):
  (∀ i, i<k → (atail.get i).sign = (atail.get (i+1)).sign) := by
  intro j jk
  rw [h1]
  rw [Mathlib.Vector.get_tail_succ, Mathlib.Vector.get_tail_succ]
  have l3: ((↑j: Fin (k+1)).succ: Fin (k + 1).succ) = ↑(j+1) := ff_l3 jk
  have l5: (↑(j + 1) + 1: Fin (k + 1 + 1)) = ((↑j: Fin (k+1)) + 1).succ := ff_l5 jk
  rw [l3, h, l5]
  exact Nat.add_lt_add_right jk 1

lemma a_not_zero_tail {a: Vector Int (k+1+1)} {atail: Vector Int (k+1)}
  (h1: atail = a.tail)
  (h: ∀ i, a.get i ≠ 0):
  (∀ i, atail.get i ≠ 0) := by
  intro j
  rw [h1, Mathlib.Vector.get_tail]
  apply h

lemma lem_div_pos (a b: Int): (a > 0) →  (b > 0) → 0 <(a + b -1) / b := by
  intro h1 h2
  match a with
  | Int.ofNat 0 =>
    simp_all
  | Int.ofNat 1 =>
    simp_all
    rw [Int.ediv_self]
    simp
    omega
  | Int.ofNat (a+1) =>
    simp_all
    rw [Int.add_sub_assoc ]
    simp
    nth_rewrite 1 [(by simp: b = (1:Int)*b)]
    rw [Int.add_mul_ediv_right]
    have h' := @Int.ediv_nonneg (a) b
    omega
    omega
  | Int.negSucc a =>
    simp_all

lemma lem_div_pos' (a b: Int): (a ≠ 0) →  (b ≠ 0) → 0 <(|a| + |b| -1) / |b| := by
  intro h1 h2
  apply lem_div_pos |a| |b|
  simp_all
  simp_all

lemma Prop_prev_prop
  {a_tail: Vector Int (k+1)}
  {a: Vector Int (k+1+1)}
  (aeq: a_tail = a.tail)
  (h: Props a n):
  Props a_tail ((|a.head| + |a.get 1| -1) / |a.get 1|) := by
    match h with
    | ⟨_, h2, h3⟩ =>
    have h1': 0 < ((|a.head| + |a.get 1| -1) / |a.get 1|) := by
      apply lem_div_pos' (a.head) (a.get 1)
      rw [<- Vector.get_zero]
      exact h2 0
      exact h2 1
    have h2' := a_not_zero_tail aeq h2
    have h3' := a_sign_tail aeq h3
    exact ⟨h1', h2', h3'⟩

lemma xInX_prev
  {a_tail l_tail x_tail: Vector Int (k+1)}
  {a l x: Vector Int (k+1+1)}
  {n: Int}
  (aeq: a_tail = a.tail)
  (xeq: x_tail = x.tail)
  (leq: l_tail = l.tail)
  (p : Props a n)
  (h: x ∈ X2 a l n):
  (x_tail ∈ X2 a_tail l_tail ((|a.head| + |a.get 1| -1) / |a.get 1|)) := by
  match h with
  | ⟨_, h2, h3⟩ =>
  have h1': x_tail.head < l_tail.head + ((|a.head| + |a.get 1| -1) / |a.get 1|) := by
    have x' := x_bounded a l n p 0 x h (by simp)
    rw [xeq, leq]
    rw [<- Vector.get_zero, <- Vector.get_zero]
    rw [Mathlib.Vector.get_tail, Mathlib.Vector.get_tail]
    simp
    simp at x'
    rw [Int.add_comm, <- Int.sub_lt_iff]
    exact x'
  have h2': ∀ i, l_tail.get i ≤ x_tail.get i := by
    intro i
    rw [xeq, leq]
    rw [Mathlib.Vector.get_tail, Mathlib.Vector.get_tail]
    exact h2 ⟨↑i + 1, by omega⟩
  have h3': ∀ (i : Fin (k + 1)),↑i < k →
    (a_tail.last > 0 → upToProd a_tail l_tail x_tail (i + 1) < a_tail.get i) ∧
    (a_tail.last < 0 → a_tail.get i < upToProd a_tail l_tail x_tail (i + 1)) := by
    intro i ik
    have h3'' := h3 (i+1) (by simp; omega)
    rw [@upToPredRec2 (k+1) a l x _ (by simp; exact ik)] at h3''
    simp
    simp at h3''
    rw [aeq, leq, xeq]
    rw [Mathlib.Vector.get_tail]
    rw [Vector.tail_last]
    simp
    have eq: (⟨↑i + 1, (by simp; exact ik)⟩: Fin (k+1)) = (i+1) := by
      rw [Fin.add_def]
      simp
      rw [Nat.mod_eq_of_lt]
      simp
      assumption
    rw [eq] at h3''
    have eq2: i.succ = ⟨↑i + 1, (by simp)⟩ := by
      rw [<- Fin.succ_mk]
    rw [<- eq2]
    exact h3''
  exact ⟨h1', h2', h3'⟩

lemma base_zero {a: Vector Int (k+1)} {i:Fin (k+1)} : (i=0) → base offs a x' i = |x'-offs| := by
  intro h
  have eq: 0 = (⟨0, by omega⟩: Fin (k+1)) := by simp
  rw [h, eq, base]

lemma f_pos_bound: ∀ a x: Vector Int (k+1), ∀n: Int,
  Props a n →
  x ∈ X2 a ls_zero n →
  (0<a.last → 0 ≤ f' 0 a ls_zero x ∧ f' 0 a ls_zero x < a.head*n) := by
  induction k
  case zero =>
    intro a x n props xinX a_pos
    match props, xinX with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>
    match a, x with
    | ⟨[a_h], _⟩, ⟨[x_h], _⟩ =>
    simp
    rw [f']
    simp
    rw [prodSum, prodSum]
    rw [Vector.head] at h4
    have h5 := h5 0
    simp at h5
    simp at h4
    simp at a_pos
    simp
    constructor
    case left =>
      apply mul_nonneg
      omega
      assumption
    case right =>
      apply Int.mul_lt_mul_of_pos_left h4 a_pos
  case succ k ih =>
    intro a x n props xinX a_pos
    match props, xinX with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>
    match a, x with
    | ⟨a_h::a_tail, a_len⟩, ⟨x_h::x_tail, x_len⟩ =>
    let a_tail_v: Vector Int (k+1) := ⟨a_tail, by
      have a_len' := a_len
      simp at a_len'
      exact a_len'⟩
    let x_tail_v: Vector Int (k+1) := ⟨x_tail, by
      have x_len' := x_len
      simp at x_len'
      exact x_len'⟩
    have aeq: a_tail_v =
      Vector.tail ⟨a_h::a_tail, a_len⟩ := by
      rw [Vector.tail]
    have xeq: x_tail_v =
      Vector.tail ⟨x_h::x_tail, x_len⟩ := by
      rw [Vector.tail]
    have aNotZ := h2 0
    rw [Vector.get_zero] at aNotZ
    simp [f', prodSum]
    have prevProp := Prop_prev_prop (aeq) props
    have prevxinX := (xInX_prev (by rfl) (by rfl) (by rfl) props xinX)
    let n' := ((|Vector.head ⟨a_h :: a_tail, a_len⟩| + |Vector.get ⟨a_h :: a_tail, a_len⟩ 1| - 1) /
      |Vector.get ⟨a_h :: a_tail, a_len⟩ 1|)
    rw [← Vector.tail_last, Vector.tail] at a_pos
    simp at a_pos
    have ih' := ih a_tail_v x_tail_v n' prevProp prevxinX a_pos
    rw [f'] at ih'
    simp at ih'

    have h5' := h5 0
    rw [Vector.get_zero, Vector.get_zero, Vector.get_head] at h5'
    simp at h5'
    simp at h4
    have ah_pos := a_same_pos ⟨a_h :: a_tail, a_len⟩ h3 a_pos 0

    constructor
    case left =>
      apply Int.add_nonneg
      exact Int.mul_nonneg (Int.le_of_lt ah_pos) (h5')
      exact ih'.left
    case right =>
      have h2' := h2 0
      simp at h2'
      apply Int.mul_add_lt h4 ah_pos
      have h6' := (h6 0 (by simp)).left a_pos
      simp at h6'
      rw [upToProd] at h6'
      simp at h6'
      exact h6'

lemma f_neg_bound: ∀ a x: Vector Int (k+1), ∀n: Int,
  Props a n →
  x ∈ X2 a ls_zero n →
  (a.last<0 → a.head*n < f' 0 a ls_zero x ∧ f' 0 a ls_zero x ≤ 0 ) := by
  induction k
  case zero =>
    intro a x n props xinX a_neg
    match props, xinX with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>
    match a, x with
    | ⟨[a_h], _⟩, ⟨[x_h], _⟩ =>
    simp [f', Vector, prodSum]
    rw [Vector.head] at h4
    have h5 := h5 0
    simp at h5
    simp at h4
    simp at a_neg
    constructor
    case left =>
      apply Int.mul_lt_mul_of_neg_left h4 a_neg
    case right =>
      apply mul_nonpos_of_nonpos_of_nonneg (by omega) h5
  case succ k ih =>
    intro a x n props xinX a_neg
    match props, xinX with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>
    match a, x with
    | ⟨a_h::a_tail, a_len⟩, ⟨x_h::x_tail, x_len⟩ =>
    let a_tail_v: Vector Int (k+1) := ⟨a_tail, by
      have a_len' := a_len
      simp at a_len'
      exact a_len'⟩
    let x_tail_v: Vector Int (k+1) := ⟨x_tail, by
      have x_len' := x_len
      simp at x_len'
      exact x_len'⟩
    have aeq: a_tail_v =
      Vector.tail ⟨a_h::a_tail, a_len⟩ := by
      rw [Vector.tail]
    have xeq: x_tail_v =
      Vector.tail ⟨x_h::x_tail, x_len⟩ := by
      rw [Vector.tail]
    have aNotZ := h2 0
    rw [Vector.get_zero] at aNotZ
    simp [f', prodSum]
    have prevProp := Prop_prev_prop (aeq) props
    have prevxinX := (xInX_prev (by rfl) (by rfl) (by rfl) props xinX)
    let n' := ((|Vector.head ⟨a_h :: a_tail, a_len⟩| + |Vector.get ⟨a_h :: a_tail, a_len⟩ 1| - 1) /
      |Vector.get ⟨a_h :: a_tail, a_len⟩ 1|)
    rw [← Vector.tail_last, Vector.tail] at a_neg
    simp at a_neg
    have ih' := ih a_tail_v x_tail_v n' prevProp prevxinX a_neg
    rw [f'] at ih'
    simp at ih'

    have h5' := h5 0
    rw [Vector.get_zero, Vector.get_zero, Vector.get_head] at h5'
    simp at h5'
    simp at h4
    have ah_neg := a_same_neg ⟨a_h :: a_tail, a_len⟩ h3 a_neg 0
    constructor
    case right =>
      apply Int.add_nonpos
      apply Int.mul_nonpos_of_nonpos_of_nonneg (Int.le_of_lt ah_neg) h5'
      exact ih'.right
    case left =>
      have h2' := h2 0
      simp at h2'
      apply Int.mul_add_lt2 h4 ah_neg

      have h6' := (h6 0 (by simp)).right a_neg
      simp at h6'
      rw [upToProd] at h6'
      simp at h6'
      exact h6'

lemma f_mod_bound: ∀ a x: Vector Int (k+1), ∀n: Int,
  Props a n →
  x ∈ X2 a ls_zero n →
  (base 0 a (f' 0 a ls_zero x) k) % a.last  = 0 := by
  induction k
  case zero =>
    intro a x n props xinX
    match a, x with
    | ⟨[a_h], _⟩, ⟨[x_h], _⟩ =>
    simp [f', prodSum]
    rw [base_zero (by simp)]
    simp
  case succ k ih =>
    intro a x n props xinX
    match props, xinX with
    | ⟨_, h2, _⟩, ⟨h4, h5, h6⟩ =>
    have aNotZ := h2 0
    rw [Vector.get_zero] at aNotZ
    simp [f', prodSum]
    have prevProp := Prop_prev_prop (by rfl) props
    have prevxinX := (xInX_prev (by rfl) (by rfl) (by rfl) props xinX)
    let n' := ((|a.head| + |a.get 1| - 1) / |a.get 1|)

    have ih' := ih a.tail x.tail n' prevProp prevxinX
    rw [f'] at ih'
    simp at ih'
    have h5' := h5 0
    rw [Vector.get_zero, Vector.get_zero] at h5'
    simp at h5'
    simp at h4

    rw [Vector.last, Fin.last]
    have eq: (↑k + 1) = (⟨k+1, Nat.lt_succ_self (k + 1)⟩: Fin (k+1+1)) := by
      apply Fin.mk_eq_mk.mpr
      simp
    rw [eq]
    match Int.lt_or_lt_of_ne (Vector.last_def ▸ h2 (Fin.last (k+1))) with
    | Or.inr a_pos =>
      have eq: |(a.head * x.head + prodSum a.tail x.tail)| % a.head = prodSum a.tail x.tail := by
        have pos := (prodSumSign a x props xinX).left a_pos
        rw [prodSum_cons'] at pos
        rw [abs_of_nonneg pos, Int.add_comm]
        simp
        rw [Int.emod_eq_of_lt]
        apply (prodSumSign a.tail x.tail prevProp prevxinX).left
        simp
        exact a_pos

        have h6' := (h6 0 (by simp)).left a_pos
        simp at h6'
        rw [upToProd] at h6'
        simp at h6'
        exact h6'
      rw [<- eq] at ih'
      have ih3': base 0 a.tail (|(a.head * x.head + prodSum a.tail x.tail)| % a.head) (Fin.last k) =
        base 0 a (a.head * x.head + prodSum a.tail x.tail) ⟨k, by omega⟩ %
        Vector.get (a : Vector Int (k+1+1)) ⟨k, by omega⟩
        := by
        have eq: Vector.head (a : Vector Int (k+1+1)) = a.head := by simp
        nth_rewrite 2 [<- eq]
        have eq2: (Fin.last k) = ⟨↑k, by omega⟩ := by
          rw [Fin.last]
        rw [eq2, <- base_lemma]
        simp
        have aNotZ := h2 0
        simp
        simp at aNotZ
        exact aNotZ

      rw [ih3', Mathlib.Vector.last_def, Fin.last] at ih'
      rw [base]
      simp at ih'
      rw [<- prodSum_cons'] at ih'
      exact ih'
    | Or.inl a_neg =>
      have neg := (prodSumSign a x props xinX).right a_neg

      have eq: (-((-(a.head * x.head + prodSum a.tail x.tail)) % a.head)) = prodSum a.tail x.tail := by
        simp
        rw [<-Int.mul_neg, Int.add_mul_emod_self_left, ← Int.emod_neg, Int.emod_eq_of_lt]
        simp
        apply Int.neg_nonneg_of_nonpos
        apply (prodSumSign a.tail x.tail prevProp prevxinX).right
        simp
        exact a_neg

        have h6' := (h6 0 (by simp)).right a_neg
        simp at h6'
        rw [upToProd] at h6'
        simp at h6'
        simp
        exact h6'
      rw [<- eq] at ih'
      have ih3': base 0 a.tail (-((-(a.head * x.head + prodSum a.tail x.tail)) % a.head)) (Fin.last k) =
        base 0 a (a.head * x.head + prodSum a.tail x.tail) ⟨k, by omega⟩ %
        Vector.get (a : Vector Int (k+1+1)) ⟨k, by omega⟩
        := by
        have eq: Vector.head (a : Vector Int (k+1+1)) = a.head := by simp
        nth_rewrite 2 [<- eq]
        have eq2: (Fin.last k) = ⟨↑k, by omega⟩ := by
          rw [Fin.last]
        rw [eq2]
        rw [<- base_lemma2]
        simp
        have aNotZ := h2 0
        simp
        simp at aNotZ
        exact aNotZ

        simp
        rw [prodSum_cons'] at neg
        exact neg
      rw [ih3', Mathlib.Vector.last_def, Fin.last] at ih'
      rw [base, prodSum_cons']

      simp at ih'
      exact ih'

lemma f_in_bounds: ∀ a x: Vector Int (k+1), ∀n: Int,
  Props a n →
  x ∈ X2 a ls_zero n →
  (0<a.last → 0 ≤ f' 0 a ls_zero x ∧ f' 0 a ls_zero x < a.head*n) ∧
  (a.last<0 → a.head*n < f' 0 a ls_zero x ∧ f' 0 a ls_zero x ≤ 0 ) ∧
  (base 0 a (f' 0 a ls_zero x) k) % a.last  = 0 := by
  intro a x n p xinX
  exact ⟨f_pos_bound a x n p xinX, f_neg_bound a x n p xinX, f_mod_bound a x n p xinX⟩


theorem f_inv_f:
  ∀ a x: Vector Int (k+1),
  ∀ n: Int,
  Props a n →
  x ∈ X2 a ls_zero n →
  f_inv' 0 a ls_zero (f' 0 a ls_zero x) = x := by
  induction k
  case zero =>
    intro a x n props xinX
    match props, xinX with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>
    match a, x with
    | ⟨[a_h], al⟩, ⟨[x_h], xl⟩ =>
    rw [f',f_inv']
    have baseCase: |a_h * x_h| / |a_h| = x_h := by
      rw [Int.mul_comm, abs_mul, Int.mul_ediv_cancel (|x_h|)]
      have x_not_zero := (h5 0)
      rw [ls_zero_get] at x_not_zero
      rw [Vector.get_zero, Vector.get_head] at x_not_zero
      exact (abs_of_nonneg x_not_zero)
      have a_not_zero := (h2 0)
      rw [Vector.get_zero, Vector.get_head] at a_not_zero
      simp
      exact a_not_zero
    rw [f_inv'', f_inv_el, base]
    simp
    simp [prodSum, prodSum, f_inv_el, base, Vector.nil, Vector.cons]
    conv =>
      pattern |a_h * x_h| / |a_h|
      rw [baseCase]
  case succ k ih =>
    intro a x n props xinX
    match props, xinX with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>
    match a, x with
    | ⟨a_h::a_tail, a_len⟩, ⟨x_h::x_tail, x_len⟩ =>
    let a_tail_v: Vector Int (k+1) := ⟨a_tail, prodSum.proof_1 a_h a_tail a_len⟩
    let x_tail_v: Vector Int (k+1) := ⟨x_tail, prodSum.proof_2 x_h x_tail x_len⟩
    have aeq: a_tail_v =
      Vector.tail ⟨a_h::a_tail, a_len⟩ := by
      rw [Vector.tail]
    have xeq: x_tail_v =
      Vector.tail ⟨x_h::x_tail, x_len⟩ := by
      rw [Vector.tail]
    have aNotZ := h2 0

    rw [Vector.get_zero] at aNotZ
    rw [f']
    have prevProp := Prop_prev_prop aeq props
    let n' := ((|Vector.head ⟨a_h :: a_tail, a_len⟩| + |Vector.get ⟨a_h :: a_tail, a_len⟩ 1| - 1) /
        |Vector.get ⟨a_h :: a_tail, a_len⟩ 1|)
    match f_in_bounds ⟨a_h :: a_tail, a_len⟩ ⟨x_h::x_tail, x_len⟩ n props xinX with
    | ⟨bounds1a, bounds2a, bounds3a⟩ =>
    match f_in_bounds a_tail_v x_tail_v n' prevProp (xInX_prev (by rfl) (by rfl) (by rfl) props xinX) with
    | ⟨bounds1b, bounds2b, bounds3b⟩ =>
    simp
    rw [prodSum]
    match Int.lt_or_lt_of_ne (h2 (Fin.last (k+1))) with
    | Or.inr a_pos =>
      have a_h_pos : 0 < a_h := by
        have same := a_same_pos ⟨a_h::a_tail, a_len⟩ h3 a_pos 0
        rw [Vector.get_zero, Vector.get_head] at same
        exact same
      rw [f_inv_pred aNotZ]
      rw [Vector.get_head] at aNotZ
      rw [Vector.tail, Vector.get_head]
      simp
      have bounds1a := bounds1a a_pos
      have bounds1b := bounds1b a_pos
      have f_pos: 0 ≤ prodSum a_tail_v x_tail_v := by
        have almost := bounds1b.left
        rw [f'] at almost
        simp at almost
        exact almost
      have arg_pos: 0 ≤ a_h * x_h + prodSum a_tail_v x_tail_v := by
        have almost := bounds1a.left
        rw [f'] at almost
        simp [prodSum] at almost
        exact almost
      have f_smaller: prodSum a_tail_v x_tail_v < a_h := by
        have almost := h6 0 (by simp)
        rw [Vector.last] at almost
        have almost := almost.left a_pos
        rw [upToProd] at almost
        simp at almost
        have eq: ↑(0 + 1: Fin (k+1+1)) = (1: Nat) := by
          simp
        rw [eq, Vector.drop_one] at almost
        simp at almost
        rw [aeq, xeq]
        exact almost
      rw [abs_of_nonneg arg_pos]

      have x_h_eq: (a_h * x_h + prodSum a_tail_v x_tail_v) / |a_h| = x_h := by
        rw [abs_of_pos a_h_pos, Int.add_comm]
        rw [Int.add_mul_ediv_left (prodSum a_tail_v x_tail_v) x_h aNotZ]

        rw [Int.ediv_eq_zero_of_lt f_pos f_smaller]
        simp
      conv =>
        lhs; arg 2; arg 4
        rw [Int.add_comm, Int.add_mul_emod_self_left]
        rw [Int.emod_eq_of_lt f_pos f_smaller]
        rw [← Int.zero_add (prodSum a_tail_v x_tail_v)]
        rw [← ls_zero_zipWith x_tail_v]
        rw [← f']
      rw [ih a_tail_v x_tail_v n' prevProp (xInX_prev (by rfl) (by rfl) (by rfl) props xinX)]
      rw [x_h_eq]
      rfl
    | Or.inl a_neg =>
      have a_h_neg : a_h < 0 := by
        have same := a_same_neg ⟨a_h::a_tail, a_len⟩ h3 a_neg 0
        rw [Vector.get_zero, Vector.get_head] at same
        exact same
      have bounds2a := bounds2a a_neg
      have bounds2b := bounds2b a_neg
      have arg_neg: (a_h * x_h + prodSum a_tail_v x_tail_v) ≤ 0 := by
        have almost := bounds2a.right
        rw [f'] at almost
        simp [prodSum] at almost
        simp
        exact almost
      simp

      rw [f_inv_pred2 aNotZ arg_neg]
      have min_a_not_zero: -a_h ≠ 0 := by
       simp
       assumption
      rw [Vector.tail, Vector.get_head]
      simp
      have f_neg: 0 ≤ -prodSum a_tail_v x_tail_v  := by
        apply Int.neg_nonneg_of_nonpos
        have almost := bounds2b.right
        rw [f'] at almost
        simp at almost
        exact almost
      have f_smaller: -prodSum a_tail_v x_tail_v < -a_h := by
        have almost := h6 0 (by simp)
        rw [Vector.last] at almost
        have almost := almost.right a_neg
        rw [upToProd] at almost
        simp at almost
        have eq: ↑(0 + 1: Fin (k+1+1)) = (1: Nat) := by
          simp
        rw [eq, Vector.drop_one] at almost
        simp at almost
        rw [aeq, xeq]
        simp
        exact almost
      simp at arg_neg
      rw [abs_of_nonpos arg_neg]

      have x_h_eq: -(a_h * x_h + prodSum a_tail_v x_tail_v) / |a_h| = x_h := by
        rw [abs_of_neg a_h_neg, Int.add_comm, Int.neg_add, ← Int.neg_mul]
        rw [Int.add_mul_ediv_left (-(prodSum a_tail_v x_tail_v)) x_h min_a_not_zero]
        rw [Int.ediv_eq_zero_of_lt f_neg f_smaller]
        simp
      conv =>
        lhs; arg 2; arg 4
        simp
        rw [← Int.mul_neg, Int.add_mul_emod_self_left, ← Int.emod_neg]
        rw [Int.emod_eq_of_lt f_neg f_smaller]
        simp
      have prevProp := Prop_prev_prop aeq props
      conv =>
        lhs;
        arg 2
        rw [← Int.zero_add (prodSum a_tail_v x_tail_v)]
        rw [← ls_zero_zipWith x_tail_v]
        rw [← f']
      rw [ih a_tail_v x_tail_v n' prevProp (xInX_prev (by rfl) (by rfl) (by rfl) props xinX)]
      rw [x_h_eq]
      rfl


lemma fin_zero:  (↑(0: Nat): Fin (k+1)) = ⟨0, by simp⟩ := by
  simp


@[simp]
lemma off_zero {a: Vector Int k}: offset b a ls_zero = b := by
  rw [offset]
  simp
  induction a using Vector.inductionOn
  case nil =>
    rw [Vector.nil, ls_zero]
    simp
    rw [prodSum]
  case cons k a as ih =>
    rw [ls_zero_cons]
    simp
    exact ih


lemma ab_bound {a b: Int} (ha: 0<a) (hb: 0<b): a ≤ b * ((a+b-1) / b) := by
  match a, b with
  | Int.negSucc a, b =>
    contrapose ha
    simp_all
  | a, Int.negSucc b =>
    contrapose hb
    simp_all
  | Int.ofNat 0, Int.ofNat b =>
    simp_all
  | Int.ofNat a+1, Int.ofNat b =>
    simp_all
    have h: (↑b: Int) ≠ 0 := by omega
    rw [Int.add_assoc, Int.add_sub_assoc]
    simp
    rw [Int.add_ediv_of_dvd_right (by simp)]
    rw [Int.ediv_self h]
    rw [Int.mul_add]
    simp
    nth_rewrite 1 [<- Int.ediv_add_emod ↑a ↑b]
    apply Int.add_lt_add_left
    apply Int.emod_lt_of_pos
    omega

lemma xInY_prev {x: Int}
  {a_tail: Vector Int (k+1)}
  {a: Vector Int (k+1+1)}
  (aeq: a_tail = a.tail)
  (p: Props a n)
  (h: x ∈ Y2 a 0 n):
  (0<a.last → |x| % a.head ∈ Y2 a_tail 0 ((|a.head| + |a.get 1| - 1) /
      |a.get 1|)) ∧
  (a.last<0 → -(-x % a.head) ∈ Y2 a_tail 0 ((|a.head| + |a.get 1| - 1) /
      |a.get 1|))
  := by
  match h with
  | ⟨h1, h2, h3⟩ =>
  simp at h2
  simp at h3
  have h_nz := p.right.left 0
  rw [Vector.get_zero] at h_nz

  have h1_pos': base 0 a_tail (|x| % a.head) (↑k: Fin (k+1)) % a_tail.last = 0:= by
    simp
    rw [aeq, Fin.last]
    rw [<- base_lemma a x (by simp) h_nz]
    have eq: (↑(k + 1): Fin (k + 1 + 1))  = ⟨k+1, by omega⟩ := by
      apply Fin.mk_eq_mk.mpr
      simp
    rw [eq, base] at h1
    simp at h1
    rw [Vector.tail_last]
    exact h1
  have h1_neg': a.last<0 → base 0 a_tail  (-(-x % a.head)) (↑k: Fin (k+1)) % a_tail.last = 0:= by
    intro a_neg
    simp
    rw [aeq, Fin.last]
    rw [<- base_lemma2 a x (by simp) h_nz (h3 a_neg).right]
    have eq: (↑(k + 1): Fin (k + 1 + 1))  = ⟨k+1, by omega⟩ := by
      apply Fin.mk_eq_mk.mpr
      simp
    rw [eq, base] at h1
    simp at h1
    rw [Vector.tail_last]
    exact h1
  let n' := ((|a.head| + |a.get 1| - 1) / |a.get 1|)
  have neq: n' = ((|a.head| + |a.get 1| - 1) / |a.get 1|) := by
      rfl
  have h2_pos':  0<a_tail.last →
      0 ≤ (|x| % a.head - 0) ∧ (|x| % a.head - 0) < a_tail.head * n' := by
    intro a_pos
    simp
    constructor
    · apply Int.emod_nonneg |x| h_nz
    · rw [neq, aeq, Vector.tail_get_head]
      have ah_pos: a.head > 0 := by
        rw [<- Vector.get_zero]
        rw [aeq, Vector.tail_last] at a_pos
        apply a_same_pos a p.right.right a_pos 0
      have a1_pos: a.tail.head > 0 := by
        rw [<- Vector.get_zero]
        rw [aeq, Vector.tail_last] at a_pos
        rw [Mathlib.Vector.get_tail_succ]
        simp
        apply a_same_pos a p.right.right a_pos 1
      have bound1 := Int.emod_lt_of_pos |x| ah_pos
      have bound2 := @ab_bound a.head a.tail.head ah_pos a1_pos
      rw [abs_of_pos ah_pos, abs_of_pos a1_pos]
      apply Int.lt_of_lt_of_le bound1 bound2
  have h2_neg':  a.last<0 → 0<a_tail.last →
      0 ≤ -(-x % a.head) - 0 ∧ -(-x % a.head) - 0 < a_tail.head * n' := by
    intro a_neg a_pos
    rw [aeq, Vector.tail_last] at a_pos
    omega
  have  h3_pos': 0<a.last → a_tail.last<0 →
      a_tail.head * n' < (|x| % a.head)-0 ∧ (|x| % a.head)-0 ≤ 0  := by
    intro a_pos a_neg
    rw [aeq, Vector.tail_last] at a_neg
    omega
  have h3_neg':  a_tail.last<0 →
      a_tail.head * n' < -(-x % a.head)-0 ∧ -(-x % a.head)-0 ≤ 0  := by
    intro a_neg
    constructor
    · rw [neq, aeq, Vector.tail_get_head]
      have ah_neg: a.head < 0 := by
        rw [<- Vector.get_zero]
        rw [aeq, Vector.tail_last] at a_neg
        apply a_same_neg a p.right.right a_neg 0
      have a1_neg: a.tail.head < 0 := by
        rw [<- Vector.get_zero]
        rw [aeq, Vector.tail_last] at a_neg
        rw [Mathlib.Vector.get_tail_succ]
        simp
        apply a_same_neg a p.right.right a_neg 1
      simp
      apply Int.lt_neg_of_lt_neg
      have bound1 := Int.emod_lt_of_pos (-x) (Int.lt_neg_of_lt_neg ah_neg)
      simp at bound1

      have bound2 := @ab_bound (-a.head) (-a.tail.head)
        (Int.lt_neg_of_lt_neg ah_neg)
        (Int.lt_neg_of_lt_neg a1_neg)
      rw [abs_of_neg ah_neg, abs_of_neg a1_neg, ← Int.neg_mul]
      apply Int.lt_of_lt_of_le bound1 bound2
    · simp
      apply Int.emod_nonneg (-x) h_nz
  constructor
  case left =>
    intro a_pos
    exact ⟨h1_pos', h2_pos', h3_pos' a_pos⟩
  case right =>
    intro a_neg
    exact ⟨h1_neg' a_neg, h2_neg' a_neg, h3_neg'⟩

lemma x_bound {a : Vector Int (k+1)} (x n: Int)
  (p: Props a n)
  (xinY: x ∈ Y2 a 0 n):
  |x| / |a.head| < n  := by
  have a_last := Vector.last_def ▸ (p.right.left (Fin.last k))
  match Int.lt_or_lt_of_ne a_last with
  | Or.inr a_pos =>
    have head_pos := a_same_pos a p.right.right a_pos 0
    rw [Vector.get_zero] at head_pos
    rw [abs_of_pos head_pos]
    have h' := (xinY.right.left a_pos).left
    simp at h'
    rw [abs_of_nonneg h']
    have h' := (xinY.right.left a_pos).right
    simp at h'
    apply Int.ediv_lt_of_lt_mul head_pos (Int.mul_comm n a.head ▸ h')
  | Or.inl a_neg =>
    have head_neg := a_same_neg a p.right.right a_neg 0
    rw [Vector.get_zero] at head_neg
    rw [abs_of_neg head_neg]
    have h' := (xinY.right.right a_neg).right
    simp at h'
    rw [abs_of_nonpos h']
    have h' := (xinY.right.right a_neg).left
    rw [← Int.neg_mul_neg] at h'
    apply Int.ediv_lt_of_lt_mul
    omega
    simp
    simp at h'
    rw [Int.mul_comm]
    apply h'

-- F applied to F_inv gives back the same answer
theorem f_f_inv :
  ∀ a: Vector Int (k+1), ∀ n x': Int,
  Props a n →
  x' ∈ Y2 a 0 n →
  f' 0 a ls_zero (f_inv' 0 a ls_zero x') = x' := by
  induction k
  case zero =>
    intro a n x' p xInY
    simp
    rw [f_inv', f_inv'', f_inv_el, base]
    simp
    match a with
    | ⟨head::[], a_length⟩ =>
      match p, xInY with
      | ⟨_, h2, _⟩, ⟨h4, h5, h6⟩ =>
      simp [f', Vector.head, Vector.cons, prodSum, prodSum]
      -- simp
      have h2' := (h2 0)
      simp at h2'
      rw [fin_zero, base] at h4
      simp at h4
      match Int.lt_or_lt_of_ne h2' with
      | Or.inr hl =>
        cases' h5 hl with left right
        simp at left
        simp at right
        rw [abs_of_nonneg left, abs_of_pos hl]
        apply Int.mul_ediv_cancel'
        exact h4
      | Or.inl hr =>
        cases' h6 hr with left right
        simp at left
        simp at right
        rw [abs_of_neg hr, abs_of_nonpos right]
        simp
        apply Int.neg_eq_comm.mp
        symm
        apply Int.mul_ediv_cancel'
        apply Int.dvd_neg.mpr
        exact h4
  case succ k ih =>
    intro a n x' p xInY
    let a_tail := a.tail
    have aeq: a_tail = a.tail := by rfl
    match xInY_prev aeq p xInY with
    | ⟨inPrev_pos, inPrev_neg⟩ =>
    match p, xInY with
    | ⟨_, h2, h3⟩, ⟨h4, h5, h6⟩ =>

    have aheadnzero := h2 0
    rw [Vector.get_zero] at aheadnzero

    have a_nzero := (h2 (Fin.last (k+1)))
    rw [<- Vector.last] at a_nzero
    match Int.lt_or_lt_of_ne a_nzero with

    | Or.inr a_pos =>
      have hhead := a_same_pos a h3 a_pos 0
      have inPrev := inPrev_pos a_pos
      let n' := ((|a.head| + |a.get 1| - 1) / |a.get 1|)
      have ih_applied := ih a.tail n' (|x'| % a.head) (Prop_prev_prop (aeq) p) inPrev
      have f_inv_pred' := @f_inv_pred k a x' aheadnzero

      cases' a using Vector.casesOn with cons a as
      rw [f_inv_pred']
      simp
      rw [f']
      simp
      rw [f'] at ih_applied
      simp at ih_applied
      rw [ih_applied]

      simp at hhead
      have h' := (h5 a_pos).left
      simp at h'
      rw [abs_of_pos hhead, abs_of_nonneg h']
      rw [Int.ediv_add_emod]
    | Or.inl a_neg =>
      have hhead := a_same_neg a h3 a_neg 0
      have inPrev := inPrev_neg a_neg
      let n' := ((|a.head| + |a.get 1| - 1) / |a.get 1|)
      have ih_applied := ih a.tail n' (-(-x' % a.head)) (Prop_prev_prop (aeq) p) inPrev
      have f_inv_pred' := @f_inv_pred2 k a x' aheadnzero

      cases' a using Vector.casesOn with cons a as
      have h' := (h6 a_neg).right
      simp at h'
      rw [f_inv_pred']
      simp
      rw [f']
      simp
      rw [f'] at ih_applied
      simp at ih_applied
      rw [ih_applied]
      simp at hhead
      rw [abs_of_neg hhead, abs_of_nonpos h']
      rw [Int.ediv_neg, ← Int.neg_mul_comm]
      simp
      rw [← Int.neg_add]
      rw [Int.ediv_add_emod]
      simp
      exact h'

theorem left_invf_f {a : Vector Int (k+1)} (p: Props a n) :
  Set.LeftInvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (Y2 a 0 n) := by
  rw [Set.LeftInvOn]
  intro xy xyInSet
  apply f_f_inv a n xy p xyInSet

theorem right_invf_f {a : Vector Int (k+1)} (p: Props a n):
  Set.RightInvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (X2 a ls_zero n) := by
  rw [Set.RightInvOn]
  intro x xInSet
  apply f_inv_f a x n p xInSet

lemma f_maps_to {a : Vector Int (k+1)} (p: Props a n):
  Set.MapsTo (f' 0 a ls_zero) (X2 a ls_zero n) (Y2 a 0 n) := by
  intro xy xyInX
  have f_in_bounds := f_in_bounds a xy n p xyInX
  match f_in_bounds with
  | ⟨h4, h5, h6⟩ =>
  constructor
  · exact h6
  · simp
    exact ⟨h4, h5⟩

lemma f_inv_maps_to {a : Vector Int (k+1)} (p: Props a n):
  Set.MapsTo (f_inv' 0 a ls_zero) (Y2 a 0 n) (X2 a ls_zero n) := by
  revert a n
  induction k
  case zero =>
    intro n a p x xinY
    constructor
    case left =>
      rw [f_inv', f_inv'', f_inv_el, base]
      simp
      exact x_bound x n p xinY
    case right =>
      constructor
      case left =>
        simp
        intro i
        rw [f_inv', f_inv'', f_inv_el, base]
        simp
        apply Int.ediv_nonneg (abs_nonneg x) (abs_nonneg a.head)
      case right =>
        simp_all
  case succ k ih =>
    intro n a p x xinY
    match xinY with
    | ⟨_, _, h3⟩ =>
    let n' := ((|a.head| + |a.get 1| - 1) / |a.get 1|)
    have prevProp := Prop_prev_prop (by rfl) p
    match (@ih n' a.tail prevProp) with
    | ih'  =>
    rw [Set.MapsTo] at ih'
    have aheadnzero := Vector.get_zero a ▸ (p.right.left 0)
    constructor
    case left =>
      simp
      rw [f_inv', f_inv'', f_inv_el]
      simp
      have eq0: 0 = (⟨0, by simp⟩: Fin (k+1+1)) := by simp
      rw [eq0, base]
      simp
      exact x_bound x n p xinY
    case right =>
      have a_last := Vector.last_def ▸ (p.right.left (Fin.last (k+1)))
      have inPrev := xInY_prev (by rfl) p xinY
      constructor
      case left =>
        intro i
        match i, Int.lt_or_lt_of_ne a_last with
        | 0, Or.inr _ =>
          rw [f_inv_pred aheadnzero, Mathlib.Vector.get_cons_zero, Vector.get_zero]
          simp
          exact Int.ediv_nonneg (abs_nonneg x) (abs_nonneg a.head)
        | 0, Or.inl a_neg =>
          simp
          have h' := (h3 a_neg).right
          simp at h'
          rw [f_inv_pred2 aheadnzero h']
          simp
          exact Int.ediv_nonneg (abs_nonneg x) (abs_nonneg a.head)
        | ⟨i+1, isLt⟩, Or.inr a_pos =>
          let i': Fin (k+1) := ⟨i, by simp at isLt; exact isLt⟩
          rw [f_inv_pred aheadnzero] --, Vector.get_cons_succ]
          have ih' := (ih' (inPrev.left a_pos)).right.left i'
          simp
          simp at ih'
          exact ih'
        | ⟨i+1, isLt⟩, Or.inl a_neg =>
          let i': Fin (k+1) := ⟨i, by simp at isLt; exact isLt⟩
          have h' := (h3 a_neg).right
          simp at h'
          rw [f_inv_pred2 aheadnzero h']
          have ih' := (ih' (inPrev.right a_neg)).right.left i'
          simp
          simp at ih'
          exact ih'
      case right =>
        intro i
        match i with
        | 0 =>
          have eq: (↑(0 + 1: Fin (k+1+1)): Nat) = (1: Nat) := by simp
          rw [upToProd, eq]
          simp
          constructor
          case left =>
            intro a_pos
            rw [f_inv_pred (Vector.get_zero a ▸ (p.right.left 0))]
            simp
            rw [← Int.zero_add (prodSum a.tail (f_inv' 0 a.tail ls_zero (|x| % a.head)))]
            rw [← ls_zero_zipWith (f_inv' 0 a.tail ls_zero (|x| % a.head))]
            rw [← f']
            rw [f_f_inv a.tail ((|a.head| + |a.get 1| - 1) / |a.get 1|) (|x| % a.head) prevProp (inPrev.left a_pos)]
            apply Int.emod_lt_of_pos
            apply Vector.get_zero a ▸ a_same_pos a p.right.right a_pos 0
          case right =>
            intro a_neg
            rw [f_inv_pred2 (Vector.get_zero a ▸ (p.right.left 0))]
            simp
            rw [← Int.zero_add (prodSum a.tail (f_inv' 0 a.tail ls_zero (-(-x % a.head))))]
            rw [← ls_zero_zipWith (f_inv' 0 a.tail ls_zero (-(-x % a.head)))]
            rw [<- f']
            rw [f_f_inv a.tail ((|a.head| + |a.get 1| - 1) / |a.get 1|) (-(-x % a.head)) prevProp (inPrev.right a_neg)]
            rw [← Int.emod_neg]
            apply Int.lt_neg_of_lt_neg
            apply Int.emod_lt_of_pos
            simp
            apply Vector.get_zero a ▸ a_same_neg a p.right.right a_neg 0
            have h' := (h3 a_neg).right
            simp at h'
            apply h'
        | ⟨i+1, lt⟩ =>
          simp
          intro h'
          have eq1: (⟨i + 1, lt⟩ + 1) = (↑((i+1) + 1): Fin (k+1+1)) := by
              apply Fin.mk_eq_mk.mpr
              simp
          have eq2: i + 1 = ↑(↑(i + 1): Fin (k+1)) := by
            rw[Fin.natCast_def];
            simp
            rw [Nat.mod_eq_of_lt]
            simp
            apply h'
          have eq3: ↑(↑i: Fin (k+1)) < k := by
            rw [Fin.natCast_def]
            simp
            rw [Nat.mod_eq_of_lt]
            apply h'
            omega
          have eq4: (⟨i + 1, lt⟩: Fin (k+1+1)) = (↑i: Fin (k+1)).succ := by
              apply Fin.mk_eq_mk.mpr
              simp
              rw [Nat.mod_eq_of_lt]
              omega
          constructor
          case left =>
            intro a_pos
            rw [eq1]
            rw [upToPredRec (i+1) (i+1) eq2]
            rw [f_inv_pred (Vector.get_zero a ▸ (p.right.left 0))]
            simp
            have ih' := (ih' (inPrev.left a_pos)).right.right i eq3
            simp at ih'
            have ih' := ih'.left a_pos
            rw [eq4]
            apply ih'
          case right =>
            intro a_neg
            rw [eq1]
            rw [upToPredRec (i+1) (i+1) eq2]
            rw [f_inv_pred2 (Vector.get_zero a ▸ (p.right.left 0))]
            simp
            have ih' := (ih' (inPrev.right a_neg)).right.right i eq3
            simp at ih'
            have ih' := ih'.right a_neg
            rw [eq4]
            apply ih'
            have h' := (h3 a_neg).right
            simp at h'
            apply h'

theorem f_is_bijection {a : Vector Int (k+1)} {n: Int} (p: Props a n):
  Set.BijOn (f' 0 a ls_zero) (X2 a ls_zero n) (Y2 a 0 n) := by
  have left: Set.LeftInvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (Y2 a 0 n) := left_invf_f p
  have right: Set.RightInvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (X2 a ls_zero n) := right_invf_f p
  have h4 : Set.InvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (Y2 a 0 n) (X2 a ls_zero n) := by
    exact ⟨left, right⟩
  have h4 : Set.InvOn (f_inv' 0 a ls_zero) (f' 0 a ls_zero) (X2 a ls_zero n)  (Y2 a 0 n) := by
    exact Set.InvOn.symm h4
  have hf : Set.MapsTo (f' 0 a ls_zero) (X2 a ls_zero n) (Y2 a 0 n) :=
    f_maps_to p
  have hf' : Set.MapsTo (f_inv' 0 a ls_zero) (Y2 a 0 n) (X2 a ls_zero n) :=
    f_inv_maps_to p
  exact Set.InvOn.bijOn h4 hf hf'

def g (l x: Vector Int k) := Vector.zipWith (λ x l ↦ x-l) x l
def g' (l x: Vector Int k) := Vector.zipWith (λ x l ↦ x+l) x l
def h (b x: Int) := x+b
def h' (b x: Int) := x-b

lemma g_inv_on {l a: Vector Int (k+1)}: Set.InvOn (g l) (g' l) (X2 a ls_zero n) (X2 a l n) := by
  constructor
  case left =>
    rw [Set.LeftInvOn]
    intro x _
    rw [g, g']
    apply Vector.toList_injective
    simp
    rw [zipWithWith]
    simp
    simp
  case right =>
    rw [Set.RightInvOn]
    intro x _
    rw [g, g']
    apply Vector.toList_injective
    simp
    rw [zipWithWith]
    simp
    simp

lemma h_maps_to': Set.MapsTo (h' off) (Y2 a off n) (Y2 a 0 n) := by
      intro xy xyInX
      match xyInX with
      | ⟨h1, h2, h3⟩ =>
      constructor
      · rw [h']
        rw [<- base_off]
        exact h1
      · constructor
        · intro i
          rw [h']
          simp
          simp at h2
          exact h2 i
        · intro i
          rw [h']
          simp
          simp at h3
          apply h3 i

lemma h_maps_to: Set.MapsTo (h off) (Y2 a 0 n) (Y2 a off n) := by
      intro xy xyInX
      match xyInX with
      | ⟨h1, h2, h3⟩ =>
      constructor
      · rw [h]
        rw [base_off]
        simp
        simp at h1
        exact h1
      · constructor
        · intro i
          rw [h]
          simp
          simp at h2
          exact h2 i
        · intro i
          rw [h]
          simp
          simp at h3
          apply h3 i

lemma g_maps_to: Set.MapsTo (g l) (X2 a l n) (X2 a ls_zero n) := by
    intro xy xyInX
    match xyInX with
    | ⟨h1, h2, h3⟩ =>
    constructor
    · rw [g, ← Vector.get_zero, Mathlib.Vector.zipWith_get]
      simp
      apply Int.sub_left_lt_of_lt_add h1
    · constructor
      · intro i
        rw [g]
        simp
        apply h2 i
      · intro i
        rw [g]
        rw [upToProd_comp]
        apply h3 i

lemma g_maps_to': Set.MapsTo (g' l) (X2 a ls_zero n) (X2 a l n) := by
    intro xy xyInX
    match xyInX with
    | ⟨h1, h2, h3⟩ =>
    constructor
    · rw [g', ← Vector.get_zero, Mathlib.Vector.zipWith_get]
      simp
      simp at h1
      nth_rewrite 2 [Int.add_comm]
      simp
      exact h1
    · constructor
      · intro i
        rw [g']
        simp
        simp at h2
        apply h2 i
      · intro i Lt
        rw [g']
        have h3' := h3 i Lt
        rw [<- upToProd_comp]
        have eq: (Vector.zipWith (fun x l ↦ x - l) (Vector.zipWith (fun x l ↦ x + l) xy l) l) =
          xy := by
          apply Vector.ext
          intro i
          simp
        rw [eq]
        apply h3'

theorem f_comp_inv_on {l a: Vector Int (k+1)} (p: Props a n):
  Set.InvOn (f' 0 a ls_zero ∘ g l) (g' l ∘ (f_inv' 0 a ls_zero)) (Y2 a 0 n) (X2 a l n) := by

    have left: Set.LeftInvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (Y2 a 0 n) := left_invf_f p
    have right: Set.RightInvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (X2 a ls_zero n) := right_invf_f p
    have hf : Set.InvOn (f' 0 a ls_zero) (f_inv' 0 a ls_zero) (Y2 a 0 n) (X2 a ls_zero n) := by
      exact ⟨left, right⟩

    have hg: Set.InvOn (g l) (g' l) (X2 a ls_zero n) (X2 a l n) := by
      exact g_inv_on

    have fst: Set.MapsTo (f_inv' 0 a ls_zero) (Y2 a 0 n) (X2 a ls_zero n) := f_inv_maps_to p
    have g'pt := @g_maps_to k
    apply Set.InvOn.comp hf hg fst g'pt

theorem f_comp_comp_inv_on {l a: Vector Int (k+1)} {off: Int} (p: Props a n):
  Set.InvOn ((g' l ∘ f_inv' 0 a ls_zero) ∘ h' off) (h off ∘ f' 0 a ls_zero ∘ g l) (X2 a l n) (Y2 a off n) := by
    have hf : Set.InvOn (g' l ∘ f_inv' 0 a ls_zero) (f' 0 a ls_zero ∘ g l) (X2 a l n) (Y2 a 0 n) := (f_comp_inv_on p).symm

    have hg : Set.InvOn (h' (off)) (h (off)) (Y2 a 0 n) (Y2 a off n) := by
      constructor
      case left =>
        intro _ _
        rw [h, h']
        simp
      case right =>
        intro _ _
        rw [h, h']
        simp

    have g'pt := @h_maps_to' off

    have fst: Set.MapsTo (f' 0 a ls_zero ∘ g l) (X2 a l n) (Y2 a 0 n) := by
      apply Set.MapsTo.comp
      apply f_maps_to p
      intro x xinY
      match xinY with
      | ⟨h1, h2, h3⟩ =>
      constructor
      · simp
        rw [g, ← Vector.get_zero, Mathlib.Vector.zipWith_get]
        simp
        apply Int.sub_left_lt_of_lt_add h1
      · constructor
        · intro i
          rw [g]
          simp
          apply h2 i
        · intro i
          rw [g]
          rw [upToProd_comp]
          apply h3 i

    apply Set.InvOn.comp hf hg fst g'pt

theorem f_comp {l a: Vector Int (k+1)}:
  f' b a l = (h b ∘ f' 0 a ls_zero ∘ g l) := by
  rw [funext_iff]
  intro x
  rw [f', Function.comp, Function.comp]
  simp
  rw [f', g, h]
  simp
  rw [Int.add_comm]

theorem f_comp' {l a: Vector Int (k+1)}:
  f_inv' b a l = ((g' l ∘ f_inv' 0 a ls_zero) ∘ h' b) := by
  rw [funext_iff]
  intro x
  rw [Function.comp, Function.comp]
  simp
  rw [g', h']
  apply Mathlib.Vector.ext
  intro i
  simp
  rw [f_get_is_f_inv_el]
  rw [f_get_is_f_inv_el]
  rw [f_inv_el, f_inv_el]
  simp
  rw [base_off]

theorem f_lzero {a: Vector Int (k+1)}:
  f' (offset b a l) a l = f' b a ls_zero := by
  rw [funext_iff]
  intro x
  rw [f', f', offset]
  simp
  rw [add_assoc]
  simp
  apply add_eq_of_eq_neg_add
  induction k
  case zero =>
    rw [prodSum_cons', prodSum_cons', prodSum_cons']
    simp
    rw [Vector.nil]
    rw [prodSum]
    rw [← Vector.get_zero, ← Vector.get_zero, ← Vector.get_zero, ← Vector.get_zero
      , Vector.zipWith_get]
    simp
    rw [Int.mul_sub]
    omega
  case succ k ih =>
    nth_rewrite 1 [prodSum_cons']
    rw [<- Vector.zipWith_tail]
    rw [ih]
    nth_rewrite 4 [prodSum_cons']
    nth_rewrite 3 [prodSum_cons']
    repeat rw [← Vector.get_zero]
    repeat rw [Vector.zipWith_get]
    rw [Int.mul_sub]
    rw [add_comm_sub]
    simp
    omega


lemma fin_sum_prod {k: Nat} (x y: Vector Int k) :
  ∑ i in Fin.FinSet k, x.get i * y.get i = prodSum x y := by
  induction k with
  | zero =>
    match x, y with
    | ⟨[],_⟩, ⟨[],_⟩ =>
    simp [prodSum, Fin.FinSet, Finset.attachFin]
  | succ k ih =>
    cases' x, y using Vector.casesOn₂ with cons x y xs ys
    rw [prodSum_cons]
    rw [<- ih xs ys]
    conv =>
      rw [Fin.FinSet]
      arg 1; arg 1; arg 1
      rw [Finset.range]
      arg 1
      rw [Nat.add_comm, Multiset.range_add]
    rw [Finset.sum, Finset.val, Finset.attachFin]
    simp
    rw [Multiset.map_pmap, Multiset.pmap_map]
    -- Rewrite rhs
    rw[Fin.FinSet, Finset.attachFin, Finset.sum]
    rw [Multiset.map_pmap]
    apply congr_arg
    apply Multiset.pmap_congr
    intro i _ lt lt2
    have eq: (⟨1 + i, lt⟩: Fin (k+1)) = (⟨i, lt2⟩: Fin k).succ := by
      simp
      rw [Nat.add_comm]
    rw [eq, Vector.get_cons_succ, Vector.get_cons_succ]

lemma f_inv_same (k: Nat):
  @f_inv k = @f_inv' k := by
  apply funext
  intro off
  apply funext
  intro as
  apply funext
  intro ls
  apply funext
  intro x
  rw [f_inv]
  apply Mathlib.Vector.ext
  intro i
  rw [f_get_is_f_inv_el]
  simp
  rw [f_inv_el]

lemma f_equiv (b: Int) (as:  Vector Int k):
  f b as = f' b as ls_zero := by
  apply funext
  intro x
  rw [f, f']
  rw [fin_sum_prod]
  simp

theorem f_inv_on {a l: Vector Int (k+1)} (p: Props a n):
  Set.InvOn (f_inv (offset b a l) a l) (f b a) (X2 a l n) (Y2 a (offset b a l) n) := by
  rw [f_equiv, f_inv_same]
  rw [← f_lzero]
  rw [f_comp', f_comp]
  apply f_comp_comp_inv_on p

lemma f_maps_to'{a l: Vector Int (k+1)} (p: Props a n): Set.MapsTo (f b a) (X2 a l n) (Y2 a (offset b a l) n) := by
  rw [f_equiv, ← @f_lzero k b l]
  rw [f_comp]
  have h_m := @h_maps_to (offset b a l) k a n
  apply Set.MapsTo.comp
  · apply h_maps_to
  · apply Set.MapsTo.comp
    · apply (f_maps_to p)
    · apply g_maps_to

lemma f_inv_maps_to'{a l: Vector Int (k+1)} (p: Props a n): Set.MapsTo (f_inv (offset b a l) a l) (Y2 a (offset b a l) n) (X2 a l n) := by
  rw [f_inv_same, f_comp']
  apply Set.MapsTo.comp
  · apply Set.MapsTo.comp
    · apply g_maps_to'
    · apply f_inv_maps_to p
  · apply  h_maps_to'

theorem f_bij_on {l a: Vector Int (k+1)} (p: Props a n):
  Set.BijOn (f b a) (X2 a l n) (Y2 a (offset b a l) n) := by
  exact Set.InvOn.bijOn (f_inv_on p) (f_maps_to' p) (f_inv_maps_to' p)

lemma implies_eq_and{a b: Prop}: ((a → b) ∧ a) = (b ∧ a) := by
  apply Eq.propIntro
  tauto
  tauto

lemma set_implies' {a b: α → Prop} {s : α}: {s: α | b s ∧ a s} = {s: α | (a s → b s) ∧ a s} := by
  conv =>
    -- rhs
    -- rw [setOf]
    -- arg 2
    pattern (_ → _) ∧ _
    rw [implies_eq_and]


lemma X3_subset_X2 (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  X a l n C ⊆ X2 a l n := by
  -- rw [Set.inter_comm, Set.left_eq_inter]
  intro xs
  intro h
  constructor
  apply h.left
  constructor
  apply h.right.left
  apply h.right.right.left

lemma Y3_subset_Y2 (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  Y a l off n C = Y2 a off n ∩ Y a l off n C := by
  rw [Set.inter_comm, Set.left_eq_inter]
  intro xs
  intro h
  constructor
  apply h.left
  constructor
  apply h.right.left
  apply h.right.right.left

lemma Y3_subset_Y2' (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  Y a l off n C = Y2 a off n ∩ {x : Int | C (f_inv off a l x)}  := by
  rw [Y]
  conv =>
    lhs
    pattern _ ∧ _
    tactic =>
      nth_rewrite 2 [← and_assoc]
      nth_rewrite 1 [← and_assoc]
  rw [Set.setOf_and]
  rw [Y2]

lemma X3_subset_X3' (a l: Vector Int (k+1)) (n: Int) (C: Vector Int (k+1) → Prop):
  X a l n C = X2 a l n ∩ {x : Vector Int (k+1) | C x}  := by
  rw [X]
  conv =>
    lhs
    pattern _ ∧ _
    tactic =>
      nth_rewrite 2 [← and_assoc]
      nth_rewrite 1 [← and_assoc]
  rw [Set.setOf_and]
  rw [X2]

lemma cond_image  {α : Type u_1} {β : Type u_2} {f : α → β} {f_inv : β → α} {s : Set α} {t : Set β} {p : α → Prop}
  (inv: Set.InvOn f_inv f s t) (bij: Set.BijOn f s t):
  f '' ((s ∩ {x : α | p x})) = t ∩ {y : β | p (f_inv y)} := by
  apply Set.Subset.antisymm
  case h₁ =>
    intro y yinIm
    match yinIm with
    | ⟨x, xin, h⟩ =>
    have xinS: x ∈ s := by
      apply Set.mem_of_mem_inter_left xin
    have xinPx: x ∈ {x | p x} := by
      apply Set.mem_of_mem_inter_right xin
    apply Set.mem_inter
    have h1 := Set.BijOn.image_eq bij
    rw [← h, ← h1]
    use x
    apply Set.mem_setOf.mpr
    have eq: f_inv y = x := by
      rw [← h]
      apply Set.RightInvOn.eq inv.left xinS
    rw [eq]
    apply Set.mem_setOf.mp xinPx
  case h₂ =>
    intro y yinInter
    match yinInter with
    | ⟨yinT, yinP⟩ =>
    use (f_inv y)
    constructor
    apply Set.mem_inter
    have h1 := Set.BijOn.image_eq (Set.BijOn.symm inv.symm bij)
    rw [← h1]
    use y
    apply yinP
    apply Set.RightInvOn.eq inv.right yinT

theorem equiv_quantifier --{α β γ: Type u}
  (s: Set α) (t: Set β)
  (A: β → γ) -- This models an array/arbitrary data structure which is indexed by an integer
  (R: γ → α → Prop) -- This models a random property, which takes an array value
  (f: α → β) (f_inv: β → α) -- This models a bijection between α and β
  (inv: Set.InvOn f_inv f s t) (bij: Set.BijOn f s t):
  (∀ xs: α, xs ∈ s → R (A (f xs)) xs) =
  (∀ x: β, x ∈ t → R (A x) (f_inv x)) := by
  apply Eq.propIntro
  case h₁ =>
    intro xsinS x xinT
    have mapsTo: Set.MapsTo f_inv t s := (bij.symm inv.symm).left
    have h1 := mapsTo xinT
    have g := xsinS (f_inv x) h1
    have h2 := inv.right
    rw [h2 xinT] at g
    exact g
  case h₂ =>
    intro xinT xs xsinS
    have h1 := bij.left xsinS
    have g := xinT (f xs) h1
    have h2 := inv.left
    rw [h2 xsinS] at g
    exact g
