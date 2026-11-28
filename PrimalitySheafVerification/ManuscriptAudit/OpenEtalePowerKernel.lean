import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleUnitHOneComposition

/-! The root-of-unity sheaves are the actual power kernels on the
small étale site, with genuinely functorial inclusion into units. -/

namespace ManuscriptAudit.OpenEtalePowerKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OpenEtaleExtension OpenEtaleDegreeOneComposition OpenEtaleDegreeOneCoefficients
open OpenEtaleUnitHOneComposition KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev G (X : Scheme.{0}) := fullCoordinateUnitSheaf X

/-- Multiplication by \(d\) on the actual additive sheaf of units. -/
abbrev power (X : Scheme.{0}) (d : ℕ) : G X ⟶ G X := d • 𝟙 (G X)

/-- The actual sheaf of \(d\)-th roots of unity on the small étale site. -/
abbrev roots (X : Scheme.{0}) (d : ℕ) := kernel (power X d)

/-- Its literal inclusion into the full unit sheaf. -/
abbrev rootsInclusion (X : Scheme.{0}) (d : ℕ) : roots X d ⟶ G X :=
  kernel.ι (power X d)

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j] (d : ℕ)

private abbrev R := restriction j A
private abbrev u := (OpenEtaleUnitComparison.restrictionIso j).hom

local instance : (R j).Additive := restriction_additive j

private theorem power_square :
    (R j).map (power X d) ≫ u j = u j ≫ power U d := by
  simp only [power, Functor.map_nsmul, Functor.map_id, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

private theorem inclusion_zero :
    ((R j).map (rootsInclusion X d) ≫ u j) ≫ power U d = 0 := by
  rw [Category.assoc, ← power_square j d, ← Category.assoc, ← Functor.map_comp,
    kernel.condition, Functor.map_zero, zero_comp]

/-- The literal map of restricted roots induced by the identification of
the actual unit sheaves on the open. -/
def rootsRestriction : (R j).obj (roots X d) ⟶ roots U d :=
  kernel.lift (power U d) ((R j).map (rootsInclusion X d) ≫ u j) (inclusion_zero j d)

theorem rootsRestriction_inclusion :
    rootsRestriction j d ≫ rootsInclusion U d = (R j).map (rootsInclusion X d) ≫ u j :=
  kernel.lift_ι _ _ _

/-- The actual pullback on first étale cohomology with finite roots coefficients. -/
def rootsPullback : Sheaf.H (roots X d) 1 →+ Sheaf.H (roots U d) 1 :=
  pullbackWith j (rootsRestriction j d)

/-- Pullback on true root-of-unity cohomology intertwines the actual unit
cohomology maps. This is the finite-level Kummer action square. -/
theorem rootsPullback_inclusion (c : Sheaf.H (roots X d) 1) :
    Sheaf.H.map (rootsInclusion U d) 1 (rootsPullback j d c) =
      unitPullback j (Sheaf.H.map (rootsInclusion X d) 1 c) := by
  change Sheaf.H.map (rootsInclusion U d) 1
    (Sheaf.H.map (rootsRestriction j d) 1 (pullback j (roots X d) c)) =
      Sheaf.H.map (u j) 1 (pullback j (G X) (Sheaf.H.map (rootsInclusion X d) 1 c))
  rw [← Sheaf.H.map_comp_apply, rootsRestriction_inclusion, Sheaf.H.map_comp_apply,
    pullback_coeff]

end

end ManuscriptAudit.OpenEtalePowerKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtalePowerKernel.rootsRestriction_inclusion,
      ``ManuscriptAudit.OpenEtalePowerKernel.rootsPullback_inclusion] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
