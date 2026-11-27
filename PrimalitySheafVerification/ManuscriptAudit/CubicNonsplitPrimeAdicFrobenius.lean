import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicHermitianFrobeniusSquare
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitThreeAdicTrace
import PrimalitySheafVerification.ManuscriptAudit.FourTorsionDeterminantTools

/-! The native Frobenius square and characteristic polynomial on prime-adic limits. -/

namespace ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate Module
open CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace
open PowerTateModule TorsionFrobeniusModule FourTorsionDeterminantTools
open CubicHermitianFrobeniusSquare

noncomputable section

variable (E L : Type*) [Field E] [Fintype E] [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

local notation "q" => Fintype.card E

private theorem pointMapAt_sq {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1)
    {V : Affine L} (hV : (Curve A).baseChange L = V) (P : V.Point) :
    let F := pointMapAt E L (Curve A) V hV (FiniteField.frobeniusAlgHom E L)
    F (F P) = -(q • P) := by
  subst V
  exact frobenius_sq_eq_neg_card E L h₂ h₃ hA hq3 hq2 P

theorem point_square {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1) (P : GeometricPoints E L A) :
    arithmeticPointFrobenius E L A (arithmeticPointFrobenius E L A P) = -(q • P) :=
  pointMapAt_sq E L h₂ h₃ hA hq3 hq2 (centered_baseChange E L A) P

variable (l : ℕ) [Fact l.Prime]

abbrev Action (A : E) : Module.End ℤ_[l] (Tate l (GeometricPoints E L A)) :=
  endMap l (arithmeticPointFrobenius E L A)

/-- The square identity on the actual compatible geometric torsion module at any prime. -/
theorem square_on_tate {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1) (x : Tate l (GeometricPoints E L A)) :
    Action E L l A (Action E L l A x) = -(q : ℤ_[l]) • x := by
  rw [neg_smul, Nat.cast_smul_eq_nsmul]
  apply PowerTateModule.ext l _
  intro n
  rw [evaluate_endMap, evaluate_endMap, map_neg, map_nsmul]
  apply Subtype.ext
  exact point_square E L h₂ h₃ hA hq3 hq2 (evaluate l _ n x).val

/-- A rank-two native Tate module has determinant q in the nonsplit centered family. -/
theorem determinant_eq_card {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1)
    (B : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints E L A))) :
    LinearMap.det (Action E L l A) = (q : ℤ_[l]) := by
  let F := Action E L l A
  have ht : LinearMap.trace ℤ_[l] (Tate l (GeometricPoints E L A)) F = 0 :=
    actual_prime_adic_trace_zero E L l h₂ h₃ hA hq3
  have hNative := square_on_tate E L l h₂ h₃ hA hq3 hq2 (B 0)
  have hSquare := square_apply_of_trace_zero B F ht (B 0)
  change F (F (B 0)) = _ at hNative
  have h := congrArg (fun v : Tate l (GeometricPoints E L A) => B.repr v (0 : Fin 2))
    (hSquare.symm.trans hNative)
  apply neg_injective
  simpa only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using h

theorem charpoly_eq {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq3 : q % 3 = 2) (hq2 : q % 2 = 1)
    (B : Basis (Fin 2) ℤ_[l] (Tate l (GeometricPoints E L A))) :
    letI := Module.Free.of_basis B
    letI := Module.Finite.of_basis B
    (Action E L l A).charpoly = X ^ 2 + C (q : ℤ_[l]) := by
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  change (Action E L l A).charpoly = _
  rw [← LinearMap.charpoly_toMatrix (Action E L l A) B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace ℤ_[l] B, LinearMap.det_toMatrix B,
    actual_prime_adic_trace_zero E L l h₂ h₃ hA hq3,
    determinant_eq_card E L l h₂ h₃ hA hq3 hq2 B, map_zero, zero_mul, sub_zero]

end
end ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius.point_square,
      ``ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius.square_on_tate,
      ``ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius.determinant_eq_card,
      ``ManuscriptAudit.CubicNonsplitPrimeAdicFrobenius.charpoly_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
