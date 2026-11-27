import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFiniteFieldLocalZeta
import PrimalitySheafVerification.ManuscriptAudit.CubicAllGoodFiniteFieldTate

/-! The same integer Euler numerator describes the complex zeta and the native Tate determinant. -/

namespace ManuscriptAudit.CubicFiniteFieldZetaTate

open Polynomial PowerTateModule
open CubicNonsplitThreeAdicTrace (GeometricPoints)
open CubicSplitExtensionTraceRecurrence (signedTrace)
open CubicFiniteFieldLocalZeta (pointTerm actual_local_zeta)
open CubicAllGoodFiniteFieldTate (actual euler_numerator)
open Paper5GoodPrimeTateEuler (localNumerator localNumerator_eval)
open scoped Padic

noncomputable section

variable (p : ℕ) [Fact p.Prime] (E L : Type) [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod p) E] [CharP E p]
  [Field L] [DecidableEq L] [Algebra E L] [Algebra (ZMod p) L]
  [IsAlgClosed L] [Algebra.IsAlgebraic (ZMod p) L]
variable (l : ℕ) [Fact l.Prime]

/-- At every good finite base and coefficient prime, one integral polynomial gives
both the actual Tate determinant and the convergent projective point-count zeta. -/
theorem shared_numerator (hp : 5 ≤ p) {A : E} (hA : A ≠ 0) (hl : p ≠ l)
    (t : ℤ_[l]) {z : ℂ} (hz : ‖z‖ < 1 / (Fintype.card E : ℝ)) :
    Summable (fun n : ℕ => ‖pointTerm p E A z n‖) ∧
    Complex.exp (∑' n : ℕ, pointTerm p E A z n) =
      (localNumerator (signedTrace A) (Fintype.card E)).eval₂ (Int.castRingHom ℂ) z /
        ((1-z) * (1-(Fintype.card E : ℂ)*z)) ∧
    LinearMap.det ((1 : Module.End ℤ_[l] (Tate l (GeometricPoints E L A))) - t • actual E L l A) =
      (localNumerator (signedTrace A) (Fintype.card E)).eval₂ (Int.castRingHom ℤ_[l]) t := by
  obtain ⟨hSum, hExp⟩ := actual_local_zeta p E hp hA hz
  refine ⟨hSum, ?_, euler_numerator p E L l hp hA hl t⟩
  rw [localNumerator_eval, hExp]

end
end ManuscriptAudit.CubicFiniteFieldZetaTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicFiniteFieldZetaTate.shared_numerator
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
