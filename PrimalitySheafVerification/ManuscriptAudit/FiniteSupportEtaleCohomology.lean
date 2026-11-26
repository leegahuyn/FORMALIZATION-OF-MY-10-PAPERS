import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import PrimalitySheafVerification.ManuscriptAudit.ClosedPointCoproduct
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportEtaleCoproduct

/-!
# Cohomology of finite sums on the affine étale site

The native cohomology functor preserves finite biproducts. A finite
pointwise direct sum of sheaves with vanishing cohomology consequently
has vanishing cohomology in the same degree.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CategoryTheory.Preadditive

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (S : Scheme.{0}) {I : Type}
variable [HasExt.{0} (Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0})]

/-- A finite sum of acyclic affine étale sheaves remains acyclic in the given degree. -/
theorem finiteDirectSum_H_subsingleton [Finite I]
    (P : I → Sheaf (Scheme.AffineEtale.topology S) AddCommGrpCat.{0})
    (n : ℕ) (h : ∀ i, Subsingleton (Sheaf.H (P i) n)) :
    Subsingleton (Sheaf.H (affineEtaleDirectSum S P) n) := by
  let T := Scheme.AffineEtale.topology S
  let H := Sheaf.functorH T n
  letI : H.Additive := inferInstanceAs ((Sheaf.functorH T n).Additive)
  let c := affineEtaleDirectSumIsColimit S P
  letI : HasCoproduct P := HasColimit.mk ⟨_, c⟩
  letI := Fintype.ofFinite I
  letI : PreservesBiproduct P H :=
    { preserves := fun hp ↦ ⟨isBilimitOfTotal _ (by
        simp_rw [H.mapBicone_π, H.mapBicone_ι, ← H.map_comp]
        erw [← H.map_sum, ← H.map_id, IsBilimit.total hp])⟩ }
  letI : PreservesColimit (Discrete.functor P) H :=
    preservesCoproduct_of_preservesBiproduct H
  have h₀ (i : I) : IsZero (H.obj (P i)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (h i)
  have h₁ := ClosedPointSupportDetection.mapCoproduct_isZero H P h₀
  have h₂ := AddCommGrpCat.subsingleton_of_isZero h₁
  let e := (H.mapIso (c.coconePointUniqueUpToIso (coproductIsCoproduct P))).addCommGroupIsoToAddEquiv
  exact ⟨fun x y ↦ e.injective (h₂.allEq (e x) (e y))⟩

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FiniteSupportPresheaf.finiteDirectSum_H_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
