import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitCanonicalTate
import PrimalitySheafVerification.ManuscriptAudit.Paper5LinearTraceRecurrence
import PrimalitySheafVerification.ManuscriptAudit.Paper5RelativeNonsplitCounts

/-! Actual prime-adic Frobenius power traces equal the relative extension point counts. -/

namespace ManuscriptAudit.Paper5RelativeNonsplitTateTrace

open FiniteFieldPointCount CubicNonsplitCanonicalTate CubicNonsplitThreeAdicTrace
open PowerTateModule Paper5LinearTraceRecurrence
open scoped Classical

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (F E : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F] [CharP F p]
variable [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Algebra (ZMod p) E]
variable [CharP E p] [IsScalarTower (ZMod p) F E]
variable (l : ℕ) [Fact l.Prime]

theorem trace_pow_eq_relative_point_count (hp : 5 ≤ p) (hP : p % 3 = 2)
    (hQ : Fintype.card F % 3 = 2) (hlp : l ≠ p) {a : F} (ha : a ≠ 0) :
    LinearMap.trace ℤ_[l] (Tate l (GeometricPoints F (AlgebraicClosure F) a))
        ((endMap l (arithmeticPointFrobenius F (AlgebraicClosure F) a)) ^
          (Module.finrank F E)) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) (algebraMap F E a)).toProjective.Point : ℤ)) : ℤ_[l]) := by
  let L := AlgebraicClosure F
  let T := endMap l (arithmeticPointFrobenius F L a)
  have small_ne (b : ℕ) (hb : 0 < b) (hb' : b < 5) : (b : F) ≠ 0 := by
    intro h
    have hle := Nat.le_of_dvd hb ((CharP.cast_eq_zero_iff F p b).mp h)
    omega
  have h₂ : (2 : F) ≠ 0 := by simpa using small_ne 2 (by decide) (by decide)
  have h₃ : (3 : F) ≠ 0 := by simpa using small_ne 3 (by decide) (by decide)
  obtain ⟨B, h⟩ := exists_basis_charpoly_det p F l hp hlp ha hQ
  have hDet : LinearMap.det T = (Fintype.card F : ℤ_[l]) := h.2
  have hTrace : LinearMap.trace ℤ_[l] (Tate l (GeometricPoints F L a)) T = 0 :=
    actual_prime_adic_trace_zero F L l h₂ h₃ ha hQ
  have hPow := trace_pow_eq_recurrence B T (Fintype.card F) 0
    (by simpa only [Int.cast_zero] using hTrace) hDet (Module.finrank F E)
  have hCount := Paper5RelativeNonsplitCounts.signed_counts p F E hp hP hQ ha
  exact hPow.trans (by simpa only [Int.cast_sub, Int.cast_add, Int.cast_one] using
    (congrArg (fun m : ℤ => (m : ℤ_[l])) hCount).symm)

end
end ManuscriptAudit.Paper5RelativeNonsplitTateTrace

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5RelativeNonsplitTateTrace.trace_pow_eq_relative_point_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
