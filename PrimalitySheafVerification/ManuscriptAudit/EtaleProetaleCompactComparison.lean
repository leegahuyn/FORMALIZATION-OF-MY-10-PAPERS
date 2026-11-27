import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleCohomologyMap
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleOpenComparison

/-! Actual compact-support change-of-site maps on an open compactification in every degree. -/

namespace ManuscriptAudit.EtaleProetaleCompactComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleProetaleInverseImage EtaleProetaleCohomologyMap EtaleProetaleOpenComparison

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{u+1}

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

private def etaleCompact (F : Sheaf U.smallEtaleTopology A.{u}) :=
  (OpenEtaleExtension.extensionByZero j A.{u}).obj F

private def proetaleCompact (F : Sheaf (Scheme.ProEt.topology U) A.{u}) :=
  (OpenProetaleExtension.extensionByZero j A.{u}).obj F

local instance etaleHasExt : HasExt.{u+1} (Sheaf X.smallEtaleTopology A.{u}) := by
  letI : EssentiallySmall.{u+1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  letI := Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology A.{u}
  exact IsGrothendieckAbelian.hasExt _

/-- The actual étale coefficient map induces the comparison on extensions by zero. -/
def compactCoefficientComparison (F : Sheaf U.smallEtaleTopology A.{u})
    (G : Sheaf (Scheme.ProEt.topology U) A.{u}) (f : (inverseImage U).obj F ⟶ G) :
    (inverseImage X).obj (etaleCompact j F) ⟶ proetaleCompact j G :=
  ((inverseImageExtensionIso j).app F).hom ≫ (OpenProetaleExtension.extensionByZero j A.{u}).map f

def compactComparison (F : Sheaf U.smallEtaleTopology A.{u})
    (G : Sheaf (Scheme.ProEt.topology U) A.{u}) (f : (inverseImage U).obj F ⟶ G) (n : ℕ) :
    Sheaf.H (etaleCompact j F) n →+ Sheaf.H (proetaleCompact j G) n :=
  (Sheaf.H.map (compactCoefficientComparison j F G f) n).comp (pullback X (etaleCompact j F) n)

/-- The native compact-support comparison on constant coefficients. -/
def compactConstantComparison (M : A.{u}) (n : ℕ) :
    Sheaf.H (etaleCompact j ((constantSheaf U.smallEtaleTopology A.{u}).obj M)) n →+
      Sheaf.H (proetaleCompact j ((constantSheaf (Scheme.ProEt.topology U) A.{u}).obj M)) n :=
  compactComparison j _ _ ((constantInverseImageIso U).app M).hom n

section Residues

variable {U₀ X₀ : Scheme.{0}} (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev residueCoefficient (r : ℕ) :=
  AddCommGrpCat.uliftFunctor.{1}.obj (AddCommGrpCat.of (ZMod (ℓ^r)))

/-- The target uses the literal native residue sheaf before extension by zero. -/
def compactNativeResidueComparison (r n : ℕ) :
    Sheaf.H (etaleCompact j₀ ((constantSheaf U₀.smallEtaleTopology AddCommGrpCat.{1}).obj
      (residueCoefficient ℓ r))) n →+
    Sheaf.H (proetaleCompact j₀ ((ProetaleCoefficientUniverseLift.lift U₀).obj
      (ProetaleResidueSheaves.residueSheaf U₀ ℓ r))) n :=
  compactComparison j₀ _ _ (((constantInverseImageIso U₀).app (residueCoefficient ℓ r)).hom ≫
    (ProetaleDiscreteConstant.nativeResidueIso U₀ ℓ r).hom) n

end Residues

end
end ManuscriptAudit.EtaleProetaleCompactComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleCompactComparison.compactCoefficientComparison,
      ``ManuscriptAudit.EtaleProetaleCompactComparison.compactComparison,
      ``ManuscriptAudit.EtaleProetaleCompactComparison.compactConstantComparison,
      ``ManuscriptAudit.EtaleProetaleCompactComparison.compactNativeResidueComparison] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
