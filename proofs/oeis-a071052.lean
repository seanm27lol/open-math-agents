import OMAStatements.S_oeis_a071052
import Mathlib.Tactic

/-!
# Doubling time in Rule 150

After two updates, exactly the three parents separated by two lattice sites
survive the XOR. Induction gives a copy of row n at the even sites of row 2n
and off-cells at all odd sites.
-/

open OMA.S_oeis_a071052
namespace Rule150Doubling

private lemma cancelTwoSteps (a b c d e : Bool) :
    xor (xor (xor (xor a b) c) (xor (xor b c) d)) (xor (xor c d) e) =
      xor (xor a c) e := by
  decide +revert

private lemma twoSteps (n : ℕ) (i : ℤ) :
    cell (n + 2) i = xor (xor (cell n (i - 4)) (cell n (i - 2))) (cell n i) := by
  simp only [cell, show i-2-2=i-4 by omega, show i-2-1=i-3 by omega,
    show i-1-2=i-3 by omega, show i-1-1=i-2 by omega]
  exact cancelTwoSteps (cell n (i - 4)) (cell n (i - 3)) (cell n (i - 2))
    (cell n (i - 1)) (cell n i)

private lemma doubledCells (n : ℕ) : ∀ i : ℤ,
    cell (2*n) (2*i) = cell n i ∧ cell (2*n) (2*i+1) = false := by
  induction n with
  | zero =>
    intro i
    change (decide (2*i = 0) = decide (i = 0)) ∧ (decide (2*i+1 = 0) = false)
    simp [show 2*i = 0 ↔ i = 0 by omega, show 2*i+1 ≠ 0 by omega]
  | succ n ih =>
    intro i
    rw [Nat.mul_succ]
    constructor
    · rw [twoSteps, show 2*i-4 = 2*(i-2) by omega, show 2*i-2 = 2*(i-1) by omega,
        (ih (i-2)).1, (ih (i-1)).1, (ih i).1]
      rfl
    · rw [twoSteps, show 2*i+1-4 = 2*(i-2)+1 by omega, show 2*i+1-2 = 2*(i-1)+1 by omega,
        (ih (i-2)).2, (ih (i-1)).2, (ih i).2]
      rfl

/-- The first `2*k+1` sites contain the first `k+1` original sites and `k` additional zeros. -/
private lemma prefixZeros (n k : ℕ) :
    (∑ i ∈ Finset.range (2*k+1), if cell (2*n) i then 0 else 1) =
      (∑ i ∈ Finset.range (k+1), if cell n i then 0 else 1) + k := by
  induction k with
  | zero =>
    have atZero : cell (2*n) 0 = cell n 0 := by simpa using (doubledCells n 0).1
    simp [atZero]
  | succ k ih =>
    rw [Nat.mul_succ]
    rw [Finset.sum_range_succ _ (2*k+2), Finset.sum_range_succ _ (2*k+1),
      Finset.sum_range_succ _ (k+1), ih]
    push_cast
    rw [(doubledCells n k).2, show (2:ℤ)*k+2 = 2*(k+1) by omega, (doubledCells n (k+1)).1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

end Rule150Doubling

theorem OMA.solution : type_of% @OMA.S_oeis_a071052.main := by
  intro n
  exact Rule150Doubling.prefixZeros n (2*n)
