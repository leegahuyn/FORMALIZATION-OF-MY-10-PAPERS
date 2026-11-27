import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.CubicTriplingSurjective
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenFrobenius
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenRotation
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective
import PrimalitySheafVerification.ManuscriptAudit.RankTwoQuadraticOperator

/-! The actual ordinary seven Frobenius has characteristic polynomial T²−T+7 on both Tate modules. -/

namespace ManuscriptAudit.Paper5OrdinarySevenTate

open Polynomial Module WeierstrassCurve CubicThreeTorsionOrdinate
open CubicDoublingSurjective CubicTriplingSurjective
open Paper5OrdinarySeven Paper5OrdinarySevenGeometry Paper5OrdinarySevenSecant
open Paper5OrdinarySevenFrobenius Paper5OrdinarySevenRotation
open PowerTateModule PowerTorsionTower PowerTateRankTwo PowerTateEvaluationSurjective
open RankTwoQuadraticOperator

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 7) L] [CharP L 7] [IsAlgClosed L] [DecidableEq L]
variable (l : ℕ) [Fact l.Prime]

private def firstBasis (hl : l = 2 ∨ l = 3) :
    Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l (Points L) 1) := by
  apply Classical.choice
  rcases hl with rfl | rfl
  · let P (W : Affine L) := Basis (Fin 2) (ZMod (2 ^ 1)) (PowerTorsion 2 W.Point 1)
    exact ⟨Eq.mpr (congrArg P (ordinary_eq_centered L))
      (CubicTwoPowerTorsionBasis.affineBasis two_ne (three_ne L) (five_ne L) 1)⟩
  · let P (W : Affine L) := Basis (Fin 2) (ZMod (3 ^ 1)) (PowerTorsion 3 W.Point 1)
    let D := Classical.choice (CubicThreeTorsionBasis.flexPair_nonempty two_ne (five_ne L))
    exact ⟨Eq.mpr (congrArg P (ordinary_eq_centered L))
      (CubicThreeTorsionBasis.basis two_ne (three_ne L) (five_ne L) D)⟩

private theorem nsmul_surjective (hl : l = 2 ∨ l = 3) :
    Function.Surjective (fun P : Points L => l • P) := by
  let P (W : Affine L) := Function.Surjective (fun Q : W.Point => l • Q)
  apply Eq.mpr (congrArg P (ordinary_eq_centered L))
  rcases hl with rfl | rfl
  · exact affine_doubling_surjective two_ne (three_ne L) (five_ne L)
  · exact affine_tripling_surjective two_ne (three_ne L) (five_ne L)

def tateBasis (hl : l = 2 ∨ l = 3) : Basis (Fin 2) ℤ_[l] (Tate l (Points L)) :=
  (Basis.finTwoProd ℤ_[l]).map
    (padicPairEquiv l (Points L) (firstBasis L l hl) (nsmul_surjective L l hl))

abbrev action : Module.End ℤ_[l] (Tate l (Points L)) := endMap l (nativeFrobenius L)

theorem rotation_not_scalar (hl : l = 2 ∨ l = 3) :
    ¬∃ c : ℤ_[l], endMap l (rotation L) = c • (1 : Module.End ℤ_[l] (Tate l (Points L))) := by
  rintro ⟨c, h⟩
  have h₁ := scalar_reduction l (Points L) (firstBasis L l hl) (nsmul_surjective L l hl)
    (rotation L) c h 1
  rcases hl with rfl | rfl
  · exact not_scalar_two L ⟨_, h₁⟩
  · exact not_scalar_three L ⟨_, h₁⟩

theorem point_rotation_quadratic :
    rotation L ^ 2 + rotation L + (1 : AddMonoid.End (Points L)) = 0 := by
  apply AddMonoidHom.ext
  intro P
  change rotation L (rotation L P) + rotation L P + P = 0
  rw [add_comm (rotation L (rotation L P)), rotation_sum, neg_add_cancel]

private theorem point_frobenius_quadratic :
    nativeFrobenius L ^ 2 - nativeFrobenius L + (7 : AddMonoid.End (Points L)) = 0 := by
  have hF (P : Points L) : nativeFrobenius L P = -P - (3 : ℕ) • rotation L P :=
    congrArg (fun m : AddMonoid.End (Points L) => m P) (native_eq_rotation L)
  have hR (P : Points L) : rotation L (rotation L P) = -P - rotation L P := by
    calc
      _ = (rotation L P + rotation L (rotation L P)) - rotation L P := by abel
      _ = _ := by rw [rotation_sum]
  apply AddMonoidHom.ext
  intro P
  change nativeFrobenius L (nativeFrobenius L P) - nativeFrobenius L P + (7 : ℕ) • P = 0
  rw [hF, hF]
  simp only [map_sub, map_neg, map_nsmul, hR]
  abel

theorem trace_det (hl : l = 2 ∨ l = 3) :
    LinearMap.trace ℤ_[l] (Tate l (Points L)) (action L l) = 1 ∧
      LinearMap.det (action L l) = 7 := by
  let S := endMap l (rotation L)
  let F := action L l
  let B := tateBasis L l hl
  have hF : F = -(1 : Module.End ℤ_[l] (Tate l (Points L))) - (3 : ℤ_[l]) • S := by
    change _ = -(1 : Module.End ℤ_[l] (Tate l (Points L))) - ((3 : ℕ) : ℤ_[l]) • S
    rw [Nat.cast_smul_eq_nsmul]
    exact by
      simpa only [map_sub, map_neg, map_one, map_nsmul] using
        congrArg (endMap l) (native_eq_rotation L)
  have hn : ¬∃ c : ℤ_[l], F = c • (1 : Module.End ℤ_[l] (Tate l (Points L))) := by
    rintro ⟨c, hc⟩
    have he := hc.symm.trans hF
    have hRel : (c + 1) • (1 : Module.End ℤ_[l] (Tate l (Points L))) + (3 : ℤ_[l]) • S = 0 := by
      rw [add_smul, one_smul]
      calc
        _ = c • (1 : Module.End ℤ_[l] (Tate l (Points L))) - (-1 - (3 : ℤ_[l]) • S) := by abel
        _ = 0 := sub_eq_zero.mpr he
    exact rotation_not_scalar L l hl
      (scalar_of_linear_relation B S (by norm_num : (3 : ℤ_[l]) ≠ 0) hRel)
  have hq : F ^ 2 - (1 : ℤ_[l]) • F + (7 : ℤ_[l]) • (1 : Module.End ℤ_[l] (Tate l (Points L))) = 0 := by
    rw [one_smul, ← Algebra.algebraMap_eq_smul_one, map_ofNat]
    exact by
      simpa only [map_add, map_sub, map_pow, map_ofNat, map_zero] using
        congrArg (endMap l) (point_frobenius_quadratic L)
  exact trace_det_of_quadratic B F hn 1 7 hq

/-- The native ordinary Frobenius polynomial includes both its exact integral trace and determinant. -/
theorem charpoly (hl : l = 2 ∨ l = 3) :
    letI := Module.Free.of_basis (tateBasis L l hl)
    letI := Module.Finite.of_basis (tateBasis L l hl)
    (action L l).charpoly = X ^ 2 - X + C (7 : ℤ_[l]) := by
  let B := tateBasis L l hl
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det L l hl
  change (action L l).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L l) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B,
    ht, hd, map_one, one_mul]

end
end ManuscriptAudit.Paper5OrdinarySevenTate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenTate.tateBasis,
      ``ManuscriptAudit.Paper5OrdinarySevenTate.trace_det,
      ``ManuscriptAudit.Paper5OrdinarySevenTate.charpoly] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
