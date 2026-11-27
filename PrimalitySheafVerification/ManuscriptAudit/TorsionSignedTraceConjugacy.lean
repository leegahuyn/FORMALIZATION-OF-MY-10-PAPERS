import Lean.Util.CollectAxioms
import Mathlib.LinearAlgebra.Trace
import PrimalitySheafVerification.ManuscriptAudit.TorsionFrobeniusModule

/-! Signed conjugacy of actual points transfers to the trace on native torsion. -/

namespace ManuscriptAudit.TorsionSignedTraceConjugacy

open TorsionFrobeniusModule

noncomputable section

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

private def torsionEquiv (m : ℕ) (e : G ≃+ H) :
    Torsion m G ≃ₗ[ZMod m] Torsion m H :=
  LinearEquiv.ofBijective (mapLinear m e.toAddMonoidHom) ⟨
    mapLinear_injective m _ e.injective, by
      intro y
      refine ⟨mapLinear m e.symm.toAddMonoidHom y, ?_⟩
      exact Subtype.ext (e.apply_symm_apply y.val)⟩

theorem mapLinear_sq (m : ℕ) (r : AddMonoid.End G) :
    mapLinear m (r ^ 2) = (mapLinear m r) ^ 2 := by
  apply LinearMap.ext
  intro P
  exact Subtype.ext rfl

/-- An actual signed point conjugacy gives the corresponding linear trace identity. -/
theorem trace_eq_of_signed_conjugacy (m : ℕ) (e : G ≃+ H)
    (f r : AddMonoid.End G) (g : AddMonoid.End H) (ε : ℤ)
    (he : ∀ P, g (e P) = e (ε • r (f P))) :
    LinearMap.trace (ZMod m) (Torsion m H) (mapLinear m g) =
      (ε : ZMod m) * LinearMap.trace (ZMod m) (Torsion m G) (mapLinear m r * mapLinear m f) := by
  let μ := torsionEquiv m e
  let F := mapLinear m f
  let R := mapLinear m r
  let S : Module.End (ZMod m) (Torsion m G) := (ε : ZMod m) • (R * F)
  have hconj : μ.conj S = mapLinear m g := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := μ.surjective y
    change μ (S (μ.symm (μ x))) = mapLinear m g (μ x)
    rw [μ.symm_apply_apply]
    change μ ((ε : ZMod m) • R (F x)) = mapLinear m g (μ x)
    rw [Int.cast_smul_eq_zsmul]
    exact Subtype.ext ((he x.val).symm)
  rw [← hconj, LinearMap.trace_conj' S μ]
  simp only [S, R, F, map_smul, smul_eq_mul]

end
end ManuscriptAudit.TorsionSignedTraceConjugacy

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TorsionSignedTraceConjugacy.trace_eq_of_signed_conjugacy
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
