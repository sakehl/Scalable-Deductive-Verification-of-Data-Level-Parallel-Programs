import Mathlib.Data.Vector.Defs
import Mathlib.Tactic

open Mathlib

-- FinRange n is the numbers from 0 to n exclusive, in increasing order.
-- FinRange 5 = [0, 1, 2, 3, 4]
def Vector.FinRange (n : Nat) : Vector (Fin n) n :=
  ⟨(List.range n).pmap (fun i h => ⟨i, h⟩) (by simp), by simp⟩

-- FinSet n is the numbers from 0 to n exclusive
-- FinSet 5 = {0, 1, 2, 3, 4}
def Fin.FinSet (n: Nat): Finset (Fin n) :=
  Finset.attachFin (Finset.range n) (by intro m; simp)

lemma Vector.get_FinRange (n: Nat) (i: Fin n): (Vector.FinRange n).get i = i := by
  simp [Vector.FinRange]
  rw [Vector.get]
  simp
  rw [List.getElem_pmap]
  simp


@[inline] def Vector.fin_range (n : Nat) : Vector (Fin n) n :=
  ⟨(List.range n).pmap (fun i h => ⟨i, h⟩) (by simp), by simp⟩

@[simp]
lemma Vector.get_fin_range (n: Nat) (i: Fin n): (Vector.fin_range n).get i = i := by
  simp [Vector.fin_range]
  rw [Vector.get]
  simp
  rw [List.getElem_pmap]
  simp

lemma Multiset.pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) (s) :
    ∀ H, (pmap g (map f s) H) = pmap (fun a h => g (f a) h) s fun _ h => H _ (mem_map_of_mem _ h):= by
    induction s using Quot.inductionOn with
    | h l =>
      intro H
      apply congr_arg _ (List.pmap_map g f l H)
