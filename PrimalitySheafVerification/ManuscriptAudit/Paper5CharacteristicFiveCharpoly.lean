import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5CharacteristicFiveFrobenius
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicTwoPowerTorsionBasis
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools

/-! In characteristic five the actual characteristic polynomial is T²+5 at every positive two-power level. -/

namespace ManuscriptAudit.Paper5CharacteristicFiveCharpoly

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate TorsionFrobeniusModule
open CubicNonsplitFrobeniusTrace FourTorsionDeterminantTools

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [DecidableEq L]

abbrev Level (A : ZMod 5) (n : ℕ) := geometricTorsion (2 ^ (n + 1)) 5 L (Curve A)

abbrev action (A : ZMod 5) (n : ℕ) := frobeniusLinear (2 ^ (n + 1)) 5 L (Curve A)

theorem square_on_torsion (A : ZMod 5) (hA : A ≠ 0) (n : ℕ) (v : Level L A n) :
    action L A n (action L A n v) =
      -((5 : ℕ) : ZMod (2 ^ (n + 1))) • v := by
  apply Subtype.ext
  change WeierstrassFrobeniusFixed.frobeniusOnPoints 5 L (Curve A)
      (WeierstrassFrobeniusFixed.frobeniusOnPoints 5 L (Curve A) v.val) = _
  rw [neg_smul, Nat.cast_smul_eq_nsmul]
  exact Paper5CharacteristicFiveFrobenius.frobenius_sq_eq_neg_five L hA v.val

variable [IsAlgClosed L]

def levelBasis (A : ZMod 5) (hA : A ≠ 0) (n : ℕ) :
    Module.Basis (Fin 2) (ZMod (2 ^ (n + 1))) (Level L A n) := by
  let a := algebraMap (ZMod 5) L A
  letI : CharP L 5 := charP_of_injective_algebraMap (algebraMap (ZMod 5) L).injective 5
  have ha : a ≠ 0 := (map_ne_zero (algebraMap (ZMod 5) L)).mpr hA
  change Module.Basis _ _ (Torsion _ ((Curve A).baseChange L).Point)
  rw [Paper5CharacteristicFiveFrobenius.centered_baseChange]
  exact CubicTwoPowerTorsionBasis.affineBasis CubicCharacteristicFiveDouble.two_ne
    CubicCharacteristicFiveDouble.three_ne ha (n + 1)

private theorem trace_zero (A : ZMod 5) (hA : A ≠ 0) (n : ℕ) :
    LinearMap.trace (ZMod (2 ^ (n + 1))) (Level L A n) (action L A n) = 0 := by
  have hcard : Fintype.card (ZMod 5) % 3 = 2 := by rw [ZMod.card]; decide
  exact actual_trace_zero (ZMod 5) L (by decide) (by decide) hA hcard (n + 1)

private theorem level_nontrivial (n : ℕ) : Nontrivial (ZMod (2 ^ (n + 1))) := by
  have h : 1 < (2 : ℕ) ^ (n + 1) := by
    rw [pow_succ]
    have hz : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    omega
  letI : Fact (1 < (2 : ℕ) ^ (n + 1)) := ⟨h⟩
  infer_instance

/-- The actual determinant is five at every positive two-power level. -/
theorem determinant_eq_five (A : ZMod 5) (hA : A ≠ 0) (n : ℕ) :
    LinearMap.det (action L A n) = ((5 : ℕ) : ZMod (2 ^ (n + 1))) := by
  letI := level_nontrivial n
  let B := levelBasis L A hA n
  let F := action L A n
  have hSquare := square_apply_of_trace_zero B F (trace_zero L A hA n) (B 0)
  have hActual := square_on_torsion L A hA n (B 0)
  change F (F (B 0)) = _ at hActual
  have h := congrArg (fun v : Level L A n => B.repr v (0 : Fin 2)) (hSquare.symm.trans hActual)
  apply neg_injective
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using h

/-- The genuine finite-level characteristic polynomial is the predicted reduction of T²+5. -/
theorem charpoly_eq (A : ZMod 5) (hA : A ≠ 0) (n : ℕ) :
    letI := Module.Free.of_basis (levelBasis L A hA n)
    letI := Module.Finite.of_basis (levelBasis L A hA n)
    (action L A n).charpoly = X ^ 2 + C ((5 : ℕ) : ZMod (2 ^ (n + 1))) := by
  letI := level_nontrivial n
  let B := levelBasis L A hA n
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  change (action L A n).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L A n) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod (2 ^ (n + 1))) B, LinearMap.det_toMatrix B,
    trace_zero L A hA n, determinant_eq_five L A hA n, map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.Paper5CharacteristicFiveCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5CharacteristicFiveCharpoly.square_on_torsion,
      ``ManuscriptAudit.Paper5CharacteristicFiveCharpoly.determinant_eq_five,
      ``ManuscriptAudit.Paper5CharacteristicFiveCharpoly.charpoly_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
