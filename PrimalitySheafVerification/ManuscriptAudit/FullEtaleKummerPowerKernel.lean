import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.OpenEtalePowerKernel

/-! The full Kummer sequence from the affine basis gives the identical
actual root kernel on the full small étale site. -/

namespace ManuscriptAudit.FullEtaleKummerPowerKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KummerUnitsSheaf OpenEtalePowerKernel

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev S := KummerRelativeFull.sequence
private abbrev V (X : Scheme.{0}) := (Scheme.AffineEtale.sheafEquiv X A).functor
private abbrev p := KummerSheafSequence.sheafPower
private abbrev u (X : Scheme.{0}) (d : ℕ) := KummerRelativeFull.unitsIso (X := X) d

variable (X : Scheme.{0}) (d : ℕ)

private def powerArrowIso : Arrow.mk (S X d).g ≅ Arrow.mk (power X d) :=
  Arrow.isoMk (u X d).symm (u X d).symm (by
    change (u X d).inv ≫ power X d = (S X d).g ≫ (u X d).inv
    rw [KummerRelativeFull.power_nsmul]
    simp only [power, Preadditive.comp_nsmul, Preadditive.nsmul_comp,
      Category.id_comp, Category.comp_id])

private def powerKernelIso : kernel (S X d).g ≅ roots X d :=
  KernelFork.mapIsoOfIsLimit (kernelIsKernel (S X d).g) (kernelIsKernel (power X d))
    (powerArrowIso X d)

private theorem powerKernelIso_inclusion :
    (powerKernelIso X d).hom ≫ rootsInclusion X d =
      kernel.ι (S X d).g ≫ (u X d).inv := by
  exact KernelFork.mapOfIsLimit_ι _ _ _

/-- The actual affine-induced and direct full Kummer roots are isomorphic
through preservation of the literal power kernel. -/
def comparison : (S X d).X₁ ≅ roots X d :=
  PreservesKernel.iso (V X) (p X d) ≪≫ powerKernelIso X d

/-- Comparison carries the native Kummer inclusion to the literal
full-site kernel inclusion. -/
theorem comparison_inclusion :
    (comparison X d).hom ≫ rootsInclusion X d = (S X d).f ≫ (u X d).inv := by
  change ((PreservesKernel.iso (V X) (p X d)).hom ≫ (powerKernelIso X d).hom) ≫
      rootsInclusion X d =
    (V X).map (kernel.ι (p X d)) ≫ (u X d).inv
  rw [Category.assoc, powerKernelIso_inclusion, ← Category.assoc,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

end

end ManuscriptAudit.FullEtaleKummerPowerKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleKummerPowerKernel.comparison_inclusion
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
