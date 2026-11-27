import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5CharacteristicFiveTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5NonsplitTwoAdicTrace
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools

/-! The exact 2-adic characteristic polynomial of actual prime-five Frobenius. -/

namespace ManuscriptAudit.Paper5CharacteristicFiveTateCharpoly

open Polynomial Module TwoPowerTateModule Paper5TwoPowerFrobenius Paper5TwoAdicFrobenius
open FourTorsionDeterminantTools

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable (L : Type*) [Field L] [Algebra (ZMod 5) L] [DecidableEq L] [IsAlgClosed L]

abbrev action {A : ZMod 5} (hA : A ≠ 0) :
    Module.End ℤ_[2] (Tate (GeometricPoints 5 L A)) :=
  (frobenius 5 L (by decide) hA).toLinearMap

def tateBasis {A : ZMod 5} (hA : A ≠ 0) :
    Module.Basis (Fin 2) ℤ_[2] (Tate (GeometricPoints 5 L A)) :=
  (Module.Basis.finTwoProd ℤ_[2]).map (padicCoordinates 5 L (by decide) hA)

private theorem coordinate_eq_conj {A : ZMod 5} (hA : A ≠ 0) :
    (padicCoordinates 5 L (by decide) hA).symm.conj (action L hA) =
      (coordinateFrobeniusPadic 5 L (by decide) hA).toLinearMap := by
  ext a
  rfl

theorem native_trace_zero {A : ZMod 5} (hA : A ≠ 0) :
    LinearMap.trace ℤ_[2] (Tate (GeometricPoints 5 L A)) (action L hA) = 0 := by
  rw [← LinearMap.trace_conj' (action L hA) (padicCoordinates 5 L (by decide) hA).symm,
    coordinate_eq_conj L hA]
  exact Paper5NonsplitTwoAdicTrace.trace_eq_zero 5 L (by decide) hA (by decide)

theorem native_determinant_eq_five {A : ZMod 5} (hA : A ≠ 0) :
    LinearMap.det (action L hA) = ((5 : ℕ) : ℤ_[2]) := by
  let B := tateBasis L hA
  let F := action L hA
  have hSquare := square_apply_of_trace_zero B F (native_trace_zero L hA) (B 0)
  have hActual := Paper5CharacteristicFiveTate.square_on_tate L hA (B 0)
  change F (F (B 0)) = _ at hActual
  have h := congrArg (fun v : Tate (GeometricPoints 5 L A) => B.repr v (0 : Fin 2))
    (hSquare.symm.trans hActual)
  apply neg_injective
  simpa only [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using h

theorem coordinate_determinant_eq_five {A : ZMod 5} (hA : A ≠ 0) :
    Paper5TwoAdicCoefficients.determinant 5 L (by decide) hA = ((5 : ℕ) : ℤ_[2]) := by
  change LinearMap.det (coordinateFrobeniusPadic 5 L (by decide) hA).toLinearMap = _
  rw [← coordinate_eq_conj L hA, LinearMap.det_conj]
  exact native_determinant_eq_five L hA

/-- Frobenius on the actual compatible Tate module has characteristic polynomial T²+5. -/
theorem native_charpoly_eq {A : ZMod 5} (hA : A ≠ 0) :
    letI := Module.Free.of_basis (tateBasis L hA)
    letI := Module.Finite.of_basis (tateBasis L hA)
    (action L hA).charpoly = X ^ 2 + C ((5 : ℕ) : ℤ_[2]) := by
  let B := tateBasis L hA
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  change (action L hA).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (action L hA) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[2] B, LinearMap.det_toMatrix B,
    native_trace_zero L hA, native_determinant_eq_five L hA, map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.Paper5CharacteristicFiveTateCharpoly

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5CharacteristicFiveTateCharpoly.native_trace_zero,
      ``ManuscriptAudit.Paper5CharacteristicFiveTateCharpoly.native_determinant_eq_five,
      ``ManuscriptAudit.Paper5CharacteristicFiveTateCharpoly.coordinate_determinant_eq_five,
      ``ManuscriptAudit.Paper5CharacteristicFiveTateCharpoly.native_charpoly_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
