import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import PrimalitySheafVerification.ManuscriptAudit.CechNerveLowDegrees

/-! Every term of the actual native Čech nerve of an affine-to-affine
arrow is again an affine native site object. -/

namespace ManuscriptAudit.ProetaleAffineCechTerms

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CechNerveLowDegrees (N)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}} {U T : X.ProEt} (f : U ⟶ T)
  [IsAffine U.left] [IsAffine T.left]

set_option maxHeartbeats 1700000 in
/-- Affineness holds for every degree of the real Čech nerve.
The forgetful functor preserves its connected finite wide pullback. -/
theorem isAffine_term (n : ℕ) : IsAffine (N f n).left := by
  let F := Scheme.ProEt.forget X ⋙ Over.forget X
  let P := WidePullbackShape.wideCospan T (fun _ : Fin (n + 1) ↦ U) (fun _ ↦ f)
  let D := P ⋙ F
  have h (j : WidePullbackShape (Fin (n + 1))) : IsAffine (D.obj j) := by
    cases j with
    | none => exact inferInstanceAs (IsAffine T.left)
    | some j => exact inferInstanceAs (IsAffine U.left)
  let E : WidePullbackShape (Fin (n + 1)) ⥤ AffineScheme.{u} :=
    { obj := fun j ↦ AffineScheme.mk (D.obj j) (h j)
      map := fun g ↦ InducedCategory.homMk (D.map g)
      map_id := fun j ↦ InducedCategory.hom_ext (D.map_id j)
      map_comp := fun g k ↦ InducedCategory.hom_ext (D.map_comp g k) }
  have e : E ⋙ AffineScheme.forgetToScheme = D := rfl
  let a := preservesLimitIso F P
  let b := (preservesLimitIso AffineScheme.forgetToScheme E).trans (HasLimit.isoOfNatIso (eqToIso e))
  letI : IsAffine (AffineScheme.forgetToScheme.obj (limit E)) := isAffine_affineScheme _
  exact IsAffine.of_isIso (a.hom ≫ b.inv)

end
end ManuscriptAudit.ProetaleAffineCechTerms

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAffineCechTerms.isAffine_term
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
