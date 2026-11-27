import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools
import PrimalitySheafVerification.ManuscriptAudit.Paper5CharacteristicFivePrimeAdicSquare

/-! The exact characteristic polynomial of actual prime-five Frobenius over the 3-adic integers. -/

namespace ManuscriptAudit.Paper5CharacteristicFiveThreeAdic

open Polynomial Module CubicThreeAdicTate FourTorsionDeterminantTools
open PowerTateModule Paper5CharacteristicFivePrimeAdicSquare

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [DecidableEq L] [IsAlgClosed L]

private theorem two_ne : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 5) L)).mpr (by decide : (2 : ZMod 5) ≠ 0)

private theorem three_ne : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using
    (map_ne_zero (algebraMap (ZMod 5) L)).mpr (by decide : (3 : ZMod 5) ≠ 0)

abbrev action (A : ZMod 5) : Module.End ℤ_[3] (Tate 3 (Points L A)) :=
  endMap 3 (pointFrobenius L A)

def tateBasis {A : ZMod 5} (hA : A ≠ 0) : Basis (Fin 2) ℤ_[3] (Tate 3 (Points L A)) :=
  (Basis.finTwoProd ℤ_[3]).map
    (affinePadicCoordinates (two_ne L) (three_ne L)
      ((map_ne_zero (algebraMap (ZMod 5) L)).mpr hA))

theorem trace_zero {A : ZMod 5} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[3] (Tate 3 (Points L A)) (action L A) = 0 :=
  CubicNonsplitThreeAdicTrace.actual_trace_zero (ZMod 5) L (by decide) (by decide) hA
    (by norm_num [ZMod.card])

theorem determinant_eq_five {A : ZMod 5} (hA : A ≠ 0) :
    LinearMap.det (action L A) = ((5 : ℕ) : ℤ_[3]) := by
  let B := tateBasis L hA
  let F := action L A
  have hSquare := square_apply_of_trace_zero B F (trace_zero L hA) (B 0)
  have hActual := square_on_tate L 3 hA (B 0)
  change F (F (B 0)) = _ at hActual
  have h := congrArg (fun v : Tate 3 (Points L A) => B.repr v (0 : Fin 2))
    (hSquare.symm.trans hActual)
  apply neg_injective
  simpa only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using h

theorem charpoly_eq {A : ZMod 5} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (tateBasis L hA)
    letI := Module.Finite.of_basis (tateBasis L hA)
    (action L A).charpoly = X ^ 2 + C ((5 : ℕ) : ℤ_[3]) := by
  let B := tateBasis L hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  change (action L A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[3] B, LinearMap.det_toMatrix B,
    trace_zero L hA, determinant_eq_five L hA, map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.Paper5CharacteristicFiveThreeAdic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5CharacteristicFiveThreeAdic.trace_zero,
      ``ManuscriptAudit.Paper5CharacteristicFiveThreeAdic.determinant_eq_five,
      ``ManuscriptAudit.Paper5CharacteristicFiveThreeAdic.charpoly_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
