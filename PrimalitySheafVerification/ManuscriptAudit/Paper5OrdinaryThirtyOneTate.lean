import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationTateRankTwo
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryThirtyOneFrobenius
import PrimalitySheafVerification.ManuscriptAudit.RankTwoQuadraticOperator

/-! The exact actual characteristic-thirty-one Frobenius coefficients on the 2-adic and 3-adic Tate modules. -/

namespace ManuscriptAudit.Paper5OrdinaryThirtyOneTate

open Polynomial Module
open Paper5OrdinaryThirtyOneCoordinates Paper5OrdinaryThirtyOneFrobenius
open PowerTateModule RankTwoQuadraticOperator

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 31) L] [CharP L 31] [IsAlgClosed L] [DecidableEq L]

/-- The actual geometric endomorphism satisfies its integral characteristic identity. -/
theorem native_quadratic :
    nativeFrobenius L ^ 2 + (4 : AddMonoid.End (Points L)) * nativeFrobenius L + 31 = 0 := by
  have hF (P : Points L) : nativeFrobenius L P = P + (6 : ℕ) • rotation L P :=
    congrArg (fun f : AddMonoid.End (Points L) => f P) (native_eq_rotation L)
  apply AddMonoidHom.ext
  intro P
  change nativeFrobenius L (nativeFrobenius L P) +
    (4 : ℕ) • nativeFrobenius L P + (31 : ℕ) • P = 0
  rw [hF, hF]
  simp only [map_add, map_nsmul, rotation_sq]
  abel

variable (l : ℕ) [Fact l.Prime]

abbrev action : Module.End ℤ_[l] (Tate l (Points L)) := endMap l (nativeFrobenius L)

theorem tate_quadratic :
    action L l ^ 2 + (4 : Module.End ℤ_[l] (Tate l (Points L))) * action L l + 31 = 0 := by
  simpa only [map_add, map_mul, map_pow, map_ofNat, map_zero] using
    congrArg (endMap l) (native_quadratic L)

def tateBasis (hl : l = 2 ∨ l = 3) : Basis (Fin 2) ℤ_[l] (Tate l (Points L)) :=
  CubicRotationTateRankTwo.tateBasis (A := a L) (z := (5 : L))
    (numeral_ne_zero L 2 (by decide)) (numeral_ne_zero L 3 (by decide))
    (a_ne_zero L) (cube_rotation L) (rotation_ne_one L) l hl

theorem trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) = -4 ∧
      LinearMap.det (action L l) = 31 := by
  let B := tateBasis L l hl
  let F := action L l
  let S := endMap l (rotation L)
  let I : Module.End ℤ_[l] (Tate l (Points L)) := 1
  have hS : ¬∃ c : ℤ_[l], S = c • I :=
    CubicRotationTateRankTwo.rotation_not_scalar (A := a L) (z := (5 : L))
      (numeral_ne_zero L 2 (by decide)) (numeral_ne_zero L 3 (by decide))
      (a_ne_zero L) (cube_rotation L) (rotation_ne_one L) l hl
  have hF : F = I + (6 : ℤ_[l]) • S := by
    change _ = I + ((6 : ℕ) : ℤ_[l]) • S
    simpa only [Nat.cast_smul_eq_nsmul, F, I, S, action, map_add, map_one, map_nsmul] using
      congrArg (endMap l) (native_eq_rotation L)
  have hN : ¬∃ c : ℤ_[l], F = c • I := by
    rintro ⟨c, hc⟩
    have hRel : ((1 : ℤ_[l]) - c) • I + (6 : ℤ_[l]) • S = 0 := by
      have hs : ((1 : ℤ_[l]) - c) • I = (1 : ℤ_[l]) • I - c • I :=
        sub_smul (1 : ℤ_[l]) c I
      rw [hs, one_smul]
      calc
        _ = (I + (6 : ℤ_[l]) • S) - c • I := by abel
        _ = 0 := sub_eq_zero.mpr (hF.symm.trans hc)
    exact hS (scalar_of_linear_relation B S (by norm_num : (6 : ℤ_[l]) ≠ 0) hRel)
  have h₄ : (-4 : ℤ_[l]) • F = -((4 : Module.End ℤ_[l] (Tate l (Points L))) * F) := by
    have h₄plus : (4 : ℤ_[l]) • F =
        (4 : Module.End ℤ_[l] (Tate l (Points L))) * F := by
      rw [Algebra.smul_def, map_ofNat]
    exact (neg_smul (4 : ℤ_[l]) F).trans (congrArg Neg.neg h₄plus)
  have h₃₁ : (31 : ℤ_[l]) • I = (31 : Module.End ℤ_[l] (Tate l (Points L))) := by
    change (31 : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (Points L))) = _
    rw [← Algebra.algebraMap_eq_smul_one, map_ofNat]
  have hQ : F ^ 2 - (-4 : ℤ_[l]) • F + (31 : ℤ_[l]) • I = 0 := by
    rw [h₄, h₃₁]
    calc
      _ = F ^ 2 + (4 : Module.End ℤ_[l] (Tate l (Points L))) * F + 31 := by abel
      _ = 0 := tate_quadratic L l
  exact trace_det_of_quadratic B F hN (-4) 31 hQ

/-- The true geometric Tate characteristic polynomial at both coefficient primes. -/
theorem charpoly (hl : l = 2 ∨ l = 3) :
    letI := Module.Free.of_basis (tateBasis L l hl)
    letI := Module.Finite.of_basis (tateBasis L l hl)
    (action L l).charpoly = X ^ 2 - C (-4 : ℤ_[l]) * X + C (31 : ℤ_[l]) := by
  let B := tateBasis L l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl
  change (action L l).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end
end ManuscriptAudit.Paper5OrdinaryThirtyOneTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTate.native_quadratic,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTate.tate_quadratic,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTate.tateBasis,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTate.trace_det,
      ``ManuscriptAudit.Paper5OrdinaryThirtyOneTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
