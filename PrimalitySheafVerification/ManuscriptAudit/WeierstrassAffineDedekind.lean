import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NoetherianDedekindMaximals
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineClosedPoints

/-! The literal geometric affine coordinate ring of a smooth Weierstrass curve is Dedekind. -/

namespace ManuscriptAudit.WeierstrassAffineDedekind

open WeierstrassCurve.Affine FractionalIdeal WeierstrassAffineClosedPoints
open scoped nonZeroDivisors

noncomputable section

universe u
variable {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

/-- The verified closed point description and invertible point ideals
give the Dedekind property of the actual affine coordinate ring. -/
theorem coordinateRing_isDedekindDomain : IsDedekindDomain W.CoordinateRing := by
  classical
  letI : IsNoetherianRing W.CoordinateRing :=
    inferInstanceAs (IsNoetherianRing (AdjoinRoot W.polynomial))
  apply NoetherianDedekindMaximals.isDedekindDomain_of_maximal_units (K := W.FunctionField)
  intro M hM
  obtain ⟨x, y, hxy, hm⟩ := maximalIdeal_is_point W M hM
  have hn : W.Nonsingular x y := (equation_iff_nonsingular (W := W)).mp hxy
  refine ⟨CoordinateRing.XYIdeal' hn, ?_⟩
  rw [hm, CoordinateRing.XYIdeal'_eq]

end

end ManuscriptAudit.WeierstrassAffineDedekind

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.WeierstrassAffineDedekind.coordinateRing_isDedekindDomain
  let ax ← collectAxioms name
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
