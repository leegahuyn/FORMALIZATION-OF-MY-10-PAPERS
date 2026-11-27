import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationTateRankTwo
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.RankTwoQuadraticOperator

/-! The exact actual characteristic-nineteen Frobenius coefficients on the 2-adic and 3-adic Tate modules. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTate

open Polynomial Module Paper5OrdinaryNineteenAlgebra
open Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenFrobenius
open PowerTateModule RankTwoQuadraticOperator

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

/-- The actual geometric endomorphism satisfies its integral characteristic identity. -/
theorem native_quadratic :
    nativeFrobenius L ^ 2 - (8 : AddMonoid.End (Points L)) * nativeFrobenius L + 19 = 0 := by
  have hF (P : Points L) : nativeFrobenius L P = (5 : ℕ) • P + (2 : ℕ) • rotation L P :=
    congrArg (fun f : AddMonoid.End (Points L) => f P) (native_eq_rotation L)
  apply AddMonoidHom.ext
  intro P
  change nativeFrobenius L (nativeFrobenius L P) -
    (8 : ℕ) • nativeFrobenius L P + (19 : ℕ) • P = 0
  rw [hF, hF]
  simp only [map_add, map_nsmul, rotation_sq]
  abel

variable (l : ℕ) [Fact l.Prime]

abbrev action : Module.End ℤ_[l] (Tate l (Points L)) := endMap l (nativeFrobenius L)

theorem tate_quadratic :
    action L l ^ 2 - (8 : Module.End ℤ_[l] (Tate l (Points L))) * action L l + 19 = 0 := by
  simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_zero] using
    congrArg (endMap l) (native_quadratic L)

def tateBasis (hl : l = 2 ∨ l = 3) : Basis (Fin 2) ℤ_[l] (Tate l (Points L)) :=
  CubicRotationTateRankTwo.tateBasis (A := (1 : L)) (z := (7 : L))
    (numeral_ne_zero 2 (by decide)) (numeral_ne_zero 3 (by decide))
    one_ne_zero rotation_cube rotation_ne_one l hl

theorem trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) = 8 ∧
      LinearMap.det (action L l) = 19 := by
  let B := tateBasis L l hl
  let F := action L l
  let S := endMap l (rotation L)
  let I : Module.End ℤ_[l] (Tate l (Points L)) := 1
  have hS : ¬∃ c : ℤ_[l], S = c • I :=
    CubicRotationTateRankTwo.rotation_not_scalar (A := (1 : L)) (z := (7 : L))
      (numeral_ne_zero 2 (by decide)) (numeral_ne_zero 3 (by decide))
      one_ne_zero rotation_cube rotation_ne_one l hl
  have hF : F = (5 : ℤ_[l]) • I + (2 : ℤ_[l]) • S := by
    change _ = ((5 : ℕ) : ℤ_[l]) • I + ((2 : ℕ) : ℤ_[l]) • S
    simpa only [Nat.cast_smul_eq_nsmul, F, I, S, action, map_add, map_one, map_nsmul] using
      congrArg (endMap l) (native_eq_rotation L)
  have hN : ¬∃ c : ℤ_[l], F = c • I := by
    rintro ⟨c, hc⟩
    have hRel : ((5 : ℤ_[l]) - c) • I + (2 : ℤ_[l]) • S = 0 := by
      have hs : ((5 : ℤ_[l]) - c) • I = (5 : ℤ_[l]) • I - c • I :=
        sub_smul (5 : ℤ_[l]) c I
      rw [hs]
      calc
        _ = ((5 : ℤ_[l]) • I + (2 : ℤ_[l]) • S) - c • I := by abel
        _ = 0 := sub_eq_zero.mpr (hF.symm.trans hc)
    exact hS (scalar_of_linear_relation B S (by norm_num : (2 : ℤ_[l]) ≠ 0) hRel)
  have h₈ : (8 : ℤ_[l]) • F = (8 : Module.End ℤ_[l] (Tate l (Points L))) * F := by
    rw [Algebra.smul_def, map_ofNat]
  have h₁₉ : (19 : ℤ_[l]) • I = (19 : Module.End ℤ_[l] (Tate l (Points L))) := by
    change (19 : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (Points L))) = _
    rw [← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have hQ : F ^ 2 - (8 : ℤ_[l]) • F + (19 : ℤ_[l]) • I = 0 := by
    rw [h₈, h₁₉]
    exact tate_quadratic L l
  exact trace_det_of_quadratic B F hN 8 19 hQ

/-- The true geometric Tate characteristic polynomial at both coefficient primes. -/
theorem charpoly (hl : l = 2 ∨ l = 3) :
    letI := Module.Free.of_basis (tateBasis L l hl)
    letI := Module.Finite.of_basis (tateBasis L l hl)
    (action L l).charpoly = X ^ 2 - C (8 : ℤ_[l]) * X + C (19 : ℤ_[l]) := by
  let B := tateBasis L l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl
  change (action L l).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end
end ManuscriptAudit.Paper5OrdinaryNineteenTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenTate.native_quadratic,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTate.tate_quadratic,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTate.tateBasis,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTate.trace_det,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
