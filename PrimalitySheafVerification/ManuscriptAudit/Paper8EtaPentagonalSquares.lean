import Lean.Util.CollectAxioms
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Tactic.Linarith

/-! The exact unary theta indices and signs of eta's native pentagonal coefficients. -/

namespace ManuscriptAudit.Paper8EtaPentagonalSquares

def squareIndex (k : ℤ) : ℕ := (6 * k - 1).natAbs

private theorem cast_natAbs_square (k : ℤ) : (k.natAbs : ℤ) ^ 2 = k ^ 2 := by
  apply Int.natAbs_eq_iff_sq_eq.mp
  simp

theorem squareIndex_sq (k : ℤ) : squareIndex k ^ 2 = 24 * pentagonal k + 1 := by
  apply Int.ofNat.inj
  push_cast
  rw [squareIndex, cast_natAbs_square]
  nlinarith only [two_mul_natCast_pentagonal k]

private theorem cast_squareIndex_cases (k : ℤ) :
    (squareIndex k : ℤ) = 6 * k - 1 ∨ (squareIndex k : ℤ) = -(6 * k - 1) := by
  by_cases h : 0 ≤ 6 * k - 1
  · exact Or.inl (Int.natAbs_of_nonneg h)
  · right
    calc
      (squareIndex k : ℤ) = ((-(6 * k - 1)).natAbs : ℤ) := by simp [squareIndex]
      _ = _ := Int.natAbs_of_nonneg (by omega)

theorem squareIndex_mod_six (k : ℤ) : squareIndex k % 6 = 1 ∨ squareIndex k % 6 = 5 := by
  rcases cast_squareIndex_cases k with h | h <;> omega

theorem squareIndex_injective : Function.Injective squareIndex := by
  intro a b hab
  have hSq : (6 * a - 1) ^ 2 = (6 * b - 1) ^ 2 := Int.natAbs_eq_iff_sq_eq.mp hab
  have hProd : ((6 * a - 1) - (6 * b - 1)) * ((6 * a - 1) + (6 * b - 1)) = 0 := by
    nlinarith only [hSq]
  rcases mul_eq_zero.mp hProd with h | h <;> omega

abbrev SquareIndices := { n : ℕ // n % 6 = 1 ∨ n % 6 = 5 }

noncomputable def squareIndexEquiv : ℤ ≃ SquareIndices :=
  Equiv.ofBijective (fun k => ⟨squareIndex k, squareIndex_mod_six k⟩) (by
    refine ⟨fun a b h => squareIndex_injective (congrArg Subtype.val h), ?_⟩
    intro n
    rcases n.property with hn | hn
    · refine ⟨-((n.val / 6 : ℕ) : ℤ), Subtype.ext ?_⟩
      have h : 6 * (-((n.val / 6 : ℕ) : ℤ)) - 1 = -(n.val : ℤ) := by omega
      simp only [squareIndex, h, Int.natAbs_neg, Int.natAbs_natCast]
    · refine ⟨((n.val / 6 : ℕ) : ℤ) + 1, Subtype.ext ?_⟩
      have h : 6 * (((n.val / 6 : ℕ) : ℤ) + 1) - 1 = (n.val : ℤ) := by omega
      simp only [squareIndex, h, Int.natAbs_natCast])

theorem squareIndexEquiv_apply (k : ℤ) :
    (squareIndexEquiv k).val = squareIndex k := rfl

def characterTwelve (n : ℕ) : ℤ :=
  if n % 12 = 1 ∨ n % 12 = 11 then 1
  else if n % 12 = 5 ∨ n % 12 = 7 then -1
  else 0

theorem characterTwelve_squareIndex (k : ℤ) :
    characterTwelve (squareIndex k) = (k.negOnePow : ℤ) := by
  by_cases hE : Even k
  · rw [Int.negOnePow_even k hE]
    obtain ⟨j, hj⟩ := hE
    have hM : squareIndex k % 12 = 1 ∨ squareIndex k % 12 = 11 := by
      rcases cast_squareIndex_cases k with h | h <;> omega
    simp [characterTwelve, hM]
  · have hO := Int.not_even_iff_odd.mp hE
    rw [Int.negOnePow_odd k hO]
    obtain ⟨j, hj⟩ := hO
    have hM : squareIndex k % 12 = 5 ∨ squareIndex k % 12 = 7 := by
      rcases cast_squareIndex_cases k with h | h <;> omega
    have hNot : ¬ (squareIndex k % 12 = 1 ∨ squareIndex k % 12 = 11) := by omega
    simp [characterTwelve, hM, hNot]

end ManuscriptAudit.Paper8EtaPentagonalSquares

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8EtaPentagonalSquares.squareIndex_sq,
      ``ManuscriptAudit.Paper8EtaPentagonalSquares.squareIndex_mod_six,
      ``ManuscriptAudit.Paper8EtaPentagonalSquares.squareIndexEquiv,
      ``ManuscriptAudit.Paper8EtaPentagonalSquares.characterTwelve_squareIndex] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
