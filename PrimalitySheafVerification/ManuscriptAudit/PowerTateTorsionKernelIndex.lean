import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PadicDeterminantIndex
import PrimalitySheafVerification.ManuscriptAudit.PowerTateEvaluationKernel
import PrimalitySheafVerification.ManuscriptAudit.ReducedLinearKernelCard

/-! The determinant index is the exact cardinality of the sufficiently deep native torsion kernel. -/

namespace ManuscriptAudit.PowerTateTorsionKernelIndex

open Module TorsionFrobeniusModule PowerTorsionTower PowerTateModule
open PowerTateRankTwo PowerTorsionCompatibleBasis PowerTateEvaluationSurjective

noncomputable section

variable (l : ℕ) [Fact l.Prime] (G : Type*) [AddCommGroup G]
variable (B : Basis (Fin 2) (ZMod (l ^ 1)) (PowerTorsion l G 1))
variable (h : Function.Surjective (fun P : G => l • P))

include B h in
/-- At any depth at least the determinant valuation, the native finite kernel
has exactly the same order as the full Tate cokernel. -/
theorem card_finite_kernel (f : AddMonoid.End G) (hf : Function.Injective (endMap l f))
    (n : ℕ) (hn : (LinearMap.det (endMap l f)).valuation ≤ n) :
    Nat.card ↥(LinearMap.ker (mapLinear (l ^ n) f)) =
      l ^ (LinearMap.det (endMap l f)).valuation := by
  let T := Tate l G
  let V := PowerTorsion l G n
  let F := endMap l f
  let d := (LinearMap.det F).valuation
  let Q := T ⧸ LinearMap.range F
  let R : ℤ_[l] →+* ZMod (l ^ n) := PadicInt.toZModPow n
  letI : Module ℤ_[l] V := Module.compHom V R
  letI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e := levelEquiv l G B (Fact.out : l.Prime).pos h n
  letI : Finite V := Finite.of_injective e.symm e.symm.injective
  let F₀ : V →ₗ[ℤ_[l]] V :=
    { toFun := mapLinear (l ^ n) f
      map_add' := map_add (mapLinear (l ^ n) f)
      map_smul' r x := (mapLinear (l ^ n) f).map_smul (R r) x }
  let Bt := (Basis.finTwoProd ℤ_[l]).map (padicPairEquiv l G B h)
  have hCard : Nat.card Q = l ^ d :=
    PadicDeterminantIndex.card_quotient_range l Bt F hf
  letI : Finite Q := Nat.finite_of_card_ne_zero (by
    rw [hCard]
    exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have hKill (x : T) : ((l : ℤ_[l]) ^ n) • x ∈ LinearMap.range F := by
    have hQ : (Nat.card Q) • (LinearMap.range F).mkQ x = 0 := card_nsmul_eq_zero'
    have hMul : (l ^ n) • (LinearMap.range F).mkQ x = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show d ≤ n from hn)
      rw [hk, pow_add, mul_nsmul, ← hCard, hQ, nsmul_zero]
    have hZero : (LinearMap.range F).mkQ (((l : ℤ_[l]) ^ n) • x) = 0 := by
      rw [map_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact hMul
    have hMem := LinearMap.mem_ker.mpr hZero
    rwa [Submodule.ker_mkQ] at hMem
  have hKer : LinearMap.ker (evaluate l G n) ≤ LinearMap.range F := by
    rw [PowerTateEvaluationKernel.ker_evaluate l G B h n]
    rintro _ ⟨x, rfl⟩
    exact hKill x
  let eK : ↥(LinearMap.ker (mapLinear (l ^ n) f)) ≃ ↥(LinearMap.ker F₀) :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr eK).trans
    ((ReducedLinearKernelCard.card_ker_of_reduction (evaluate l G n)
      (evaluate_surjective l G B h n) F F₀ (fun x => evaluate_endMap l f n x) hKer).trans hCard)

end
end ManuscriptAudit.PowerTateTorsionKernelIndex

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PowerTateTorsionKernelIndex.card_finite_kernel
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
