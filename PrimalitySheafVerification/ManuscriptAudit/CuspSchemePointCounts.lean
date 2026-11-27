import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspPointCounts
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.NodalSchemePointCounts

/-! The point count of the cusp is the count of its actual scheme-valued rational points. -/

namespace ManuscriptAudit.CuspSchemePointCounts

open AlgebraicGeometry CategoryTheory Polynomial
open CuspPunctured CuspPointCounts SchemeRationalPointsOpen
open CuspProperCompactification

noncomputable section

universe u

variable (K : Type u) [Field K]

private def cube : CuspSubalgebra K :=
  ⟨(X : Polynomial K) ^ 3, Algebra.subset_adjoin (by simp)⟩

private theorem equation : cube K ^ 2 = cuspSquare K ^ 3 := by
  apply Subtype.ext
  change ((X : Polynomial K) ^ 3) ^ 2 = (X ^ 2) ^ 3
  ring

private def coordinates (f : CuspSubalgebra K →ₐ[K] K) : curvePoints K :=
  ⟨(f (cuspSquare K), f (cube K)), by
    change f (cube K) ^ 2 = f (cuspSquare K) ^ 3
    rw [← map_pow, ← map_pow, equation]⟩

private theorem coordinates_injective : Function.Injective (coordinates K) := by
  intro f g h
  apply AlgHom.adjoin_ext
  intro a ha
  change a ∈ ({(X : Polynomial K) ^ 2, X ^ 3} : Set (Polynomial K)) at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact congrArg (fun c : curvePoints K => c.val.1) h
  · exact congrArg (fun c : curvePoints K => c.val.2) h

private def evaluate (t : K) : CuspSubalgebra K →ₐ[K] K :=
  (Polynomial.aeval t).comp (CuspSubalgebra K).val

private theorem coordinates_evaluate (t : K) :
    coordinates K (evaluate K t) = parameterEquiv K t := by
  apply Subtype.ext
  change (Polynomial.aeval t ((X : Polynomial K) ^ 2),
      Polynomial.aeval t ((X : Polynomial K) ^ 3)) = (t ^ 2, t ^ 3)
  simp

def affineEquiv :
    PointsOver (CuspProperCompactification.affineOpen K ≫ projectiveCuspToBase K) ≃ curvePoints K := by
  rw [CuspProperCompactification.affineOpen_toBase]
  refine (NodalSchemePointCounts.ringPoints K).trans (Equiv.ofBijective (coordinates K)
    ⟨coordinates_injective K, ?_⟩)
  intro c
  exact ⟨evaluate K ((parameterEquiv K).symm c),
    (coordinates_evaluate K _).trans ((parameterEquiv K).apply_symm_apply c)⟩

theorem affine_card :
    Nat.card (PointsOver (CuspProperCompactification.affineOpen K ≫ projectiveCuspToBase K)) =
      Nat.card K :=
  (Nat.card_congr (affineEquiv K)).trans (curve_card K)

end
end ManuscriptAudit.CuspSchemePointCounts

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspSchemePointCounts.affineEquiv,
      ``ManuscriptAudit.CuspSchemePointCounts.affine_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
