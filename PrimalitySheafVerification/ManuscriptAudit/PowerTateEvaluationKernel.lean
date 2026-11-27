import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationSurjective

/-! The kernel of native finite-level evaluation is exactly p^n times the Tate module. -/

namespace ManuscriptAudit.PowerTateEvaluationKernel

open Module TorsionFrobeniusModule PowerTorsionTower PowerTateModule
open PowerTateRankTwo PowerTorsionCompatibleBasis

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (B : Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1))
variable (h : Function.Surjective (fun P : G => l • P))

local instance finiteLevelModule (n : ℕ) : Module ℤ_[l] (PowerTorsion l G n) :=
  Module.compHom (PowerTorsion l G n) (PadicInt.toZModPow n : ℤ_[l] →+* ZMod (l ^ n))

include B h in
/-- Native evaluation is reduction by a power of the coefficient prime. -/
theorem ker_evaluate (n : ℕ) :
    LinearMap.ker (evaluate l G n) =
      LinearMap.range (((l : ℤ_[l]) ^ n) • (1 : Module.End ℤ_[l] (Tate l G))) := by
  let a := (l : ℤ_[l]) ^ n
  let E := padicPairEquiv l G B h
  let e := levelEquiv l G B (Fact.out : l.Prime).pos h n
  let f : ℤ_[l] →+* ZMod (l ^ n) := PadicInt.toZModPow n
  have hDvd (y : ℤ_[l]) (hy : f y = 0) : a ∣ y := by
    apply Ideal.mem_span_singleton.mp
    change y ∈ Ideal.span ({(l : ℤ_[l]) ^ n} : Set ℤ_[l])
    rw [← PadicInt.ker_toZModPow n, RingHom.mem_ker]
    exact hy
  have hA : f a = 0 := by
    apply RingHom.mem_ker.mp
    change a ∈ RingHom.ker (PadicInt.toZModPow n)
    rw [PadicInt.ker_toZModPow]
    exact Ideal.subset_span (Set.mem_singleton_iff.mpr rfl)
  apply Submodule.ext
  intro x
  change evaluate l G n x = 0 ↔ ∃ y, a • y = x
  constructor
  · intro hx
    let y := E.symm x
    have hEval : evaluate l G n (E y) = 0 := by
      rw [show E y = x from E.apply_symm_apply x, hx]
    change evaluate l G n (padicPairEquiv l G B h y) = 0 at hEval
    rw [evaluate_padicPairEquiv] at hEval
    have he : e (f y.1, f y.2) = e (0, 0) := hEval.trans (map_zero e).symm
    have hy := e.injective he
    obtain ⟨y₁, hy₁⟩ := hDvd y.1 (congrArg Prod.fst hy)
    obtain ⟨y₂, hy₂⟩ := hDvd y.2 (congrArg Prod.snd hy)
    have hPair : a • (y₁, y₂) = y := Prod.ext hy₁.symm hy₂.symm
    exact ⟨E (y₁, y₂), (map_smul E a (y₁, y₂)).symm.trans
      ((congrArg E hPair).trans (E.apply_symm_apply x))⟩
  · rintro ⟨y, rfl⟩
    rw [evaluate_smul]
    change f a • evaluate l G n y = 0
    rw [hA, zero_smul]

end
end ManuscriptAudit.PowerTateEvaluationKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PowerTateEvaluationKernel.ker_evaluate
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
