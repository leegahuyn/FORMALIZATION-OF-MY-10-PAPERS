import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Algebraic.Integral
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFiniteFieldTate

/-! Canonical algebraic-closure coefficients for the actual nonsplit Tate action. -/

namespace ManuscriptAudit.CubicNonsplitCanonicalTate

open CubicNonsplitThreeAdicTrace CubicNonsplitFiniteFieldTate
open PowerTateModule Polynomial
open scoped Classical

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Fintype E] [CharP E p]
variable (l : ℕ) [Fact l.Prime]

private theorem char_mod_three (hE : Fintype.card E % 3 = 2) : p % 3 = 2 := by
  obtain ⟨d, _, hd⟩ := FiniteField.card E p
  have hD : (d : ℕ) ≠ 0 := Nat.ne_of_gt d.property
  have hCases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hCases with h | h | h
  · rw [hd, Nat.pow_mod, h, zero_pow hD] at hE
    omega
  · rw [hd, Nat.pow_mod, h, one_pow] at hE
    omega
  · exact h

private theorem small_cast_ne_zero (hp : 5 ≤ p) (n : ℕ) (hn₀ : 0 < n) (hn₅ : n < 5) :
    (n : E) ≠ 0 := by
  intro h
  have hd := (CharP.cast_eq_zero_iff E p n).mp h
  have hn := Nat.le_of_dvd hn₀ hd
  omega

theorem exists_basis_charpoly_det (hp : 5 ≤ p) (hlp : l ≠ p) {A : E} (hA : A ≠ 0)
    (hE : Fintype.card E % 3 = 2) :
    ∃ B : Module.Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints E (AlgebraicClosure E) A)),
      letI := Module.Free.of_basis B
      letI := Module.Finite.of_basis B
      (endMap l (arithmeticPointFrobenius E (AlgebraicClosure E) A)).charpoly = X ^ 2 + C (Fintype.card E : ℤ_[l]) ∧
      LinearMap.det (endMap l (arithmeticPointFrobenius E (AlgebraicClosure E) A)) = (Fintype.card E : ℤ_[l]) := by
  classical
  let L := AlgebraicClosure E
  letI : Algebra (ZMod p) E := (ZMod.castHom dvd_rfl E).toAlgebra
  letI : Module.Finite (ZMod p) E := inferInstance
  letI : Algebra.IsAlgebraic (ZMod p) L := Algebra.IsAlgebraic.trans (ZMod p) E L
  have hq := char_mod_three p E hE
  have h₂ : (2 : E) ≠ 0 := by simpa using small_cast_ne_zero p E hp 2 (by decide) (by decide)
  have h₃ : (3 : E) ≠ 0 := by simpa using small_cast_ne_zero p E hp 3 (by decide) (by decide)
  exact ⟨actualBasis p L l E hp hq hlp h₂ h₃ hA,
    charpoly p L l E hp hq hlp h₂ h₃ hA hE,
    determinant p L l E hp hq hlp h₂ h₃ hA hE⟩

end
end ManuscriptAudit.CubicNonsplitCanonicalTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicNonsplitCanonicalTate.exists_basis_charpoly_det
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
