import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicTateRotationCoefficients
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySixtyOneFrobenius

/-! The exact characteristic-61 geometric Tate trace, determinant, and polynomial. -/

namespace ManuscriptAudit.Paper5OrdinarySixtyOneTate

open Polynomial Module PowerTateModule
open Paper5OrdinarySixtyOneFrobenius

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 61) L] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

abbrev action : Module.End ℤ_[l] (Tate l (Points L)) := endMap l (nativeFrobenius L)

def tateBasis (hl : l = 2 ∨ l = 3) : Basis (Fin 2) ℤ_[l] (Tate l (Points L)) :=
  CubicRotationTateRankTwo.tateBasis (two_ne_zero L) (three_ne_zero L) (by simp [a])
    (cube_rotation L) (rotation_ne_one L) l hl

theorem trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) = 14 ∧
      LinearMap.det (action L l) = 61 := by
  have hF : nativeFrobenius L = (5 : ℤ) • (1 : AddMonoid.End (Points L)) +
      (-4 : ℤ) • rotation L := by
    change nativeFrobenius L = ((5 : ℕ) : ℤ) • (1 : AddMonoid.End (Points L)) +
      Int.negSucc 3 • rotation L
    simp only [negSucc_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    exact native_eq_rotation L
  obtain ⟨ht, hd⟩ := CubicTateRotationCoefficients.trace_det
    (two_ne_zero L) (three_ne_zero L) (by simp [a]) (cube_rotation L) (rotation_ne_one L)
    (discriminant_ne_zero L) l hl (nativeFrobenius L) (5) (-4) hF
  have ht' : (2 * (5 : ℤ) - (-4 : ℤ)) = 14 := by decide
  have hd' : ((5 : ℤ) ^ 2 - (5 : ℤ) * (-4 : ℤ) + (-4 : ℤ) ^ 2) = 61 := by decide
  rw [ht'] at ht
  rw [hd'] at hd
  exact ⟨by simpa only [Int.cast_neg, Int.cast_ofNat] using ht,
    by simpa only [Int.cast_ofNat] using hd⟩

theorem charpoly (hl : l = 2 ∨ l = 3) :
    letI := Module.Free.of_basis (tateBasis L l hl)
    letI := Module.Finite.of_basis (tateBasis L l hl)
    (action L l).charpoly = X ^ 2 - C (14 : ℤ_[l]) * X + C (61 : ℤ_[l]) := by
  let B := tateBasis L l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl
  change (action L l).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B, ht, hd]

end
end ManuscriptAudit.Paper5OrdinarySixtyOneTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.Paper5OrdinarySixtyOneTate.tateBasis,
      ``ManuscriptAudit.Paper5OrdinarySixtyOneTate.trace_det,
      ``ManuscriptAudit.Paper5OrdinarySixtyOneTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun name => !allowed.contains name
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
