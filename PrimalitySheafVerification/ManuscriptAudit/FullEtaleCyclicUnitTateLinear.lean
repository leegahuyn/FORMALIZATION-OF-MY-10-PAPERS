import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicUnitTate
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleHOnePadic

/-! The native cyclic Kummer comparison is linear for the actual
prime-adic actions assembled from the finite residue actions. -/

namespace ManuscriptAudit.FullEtaleCyclicUnitTateLinear

open AlgebraicGeometry CategoryTheory
open FullEtaleCyclicUnitTate FullEtaleHOnePadic FullEtaleKummerKernel
open TorsionFrobeniusModule PowerTorsionTower PowerTateModule KummerUnitsSheaf
open scoped Padic

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) (l : ℕ) [Fact l.Prime]
variable {K : Type} [Field K] [IsAlgClosed K] [NeZero (l : K)]
variable (k : X ⟶ Spec (CommRingCat.of K))
variable (hu : ∀ n : ℕ, Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ (l ^ n)))

private abbrev G := Sheaf.H (fullCoordinateUnitSheaf X) 1
private abbrev i := (((Sheaf.functorH X.smallEtaleTopology 1).mapIso
  (KummerRelativeFull.unitsIso (X := X) 1)).addCommGroupIsoToAddEquiv)

private def levelComparison (n : ℕ) :
    FullEtaleCyclicHOneLimit.Level X l n →+ PowerTorsion l (G X) n :=
  (mapAdd (l ^ n) (i X).symm.toAddMonoidHom).comp
    ((FullEtaleKummerTateLimit.levelEquiv X l k hu n).toAddMonoidHom.comp
      (FullEtaleCyclicHOneLimit.levelEquiv X l k n).toAddMonoidHom)

/-- The same actual cyclic Kummer comparison is a prime-adic linear isomorphism. -/
def cyclicUnitTateLinearEquiv : CyclicHOne X l ≃ₗ[ℤ_[l]] Tate l (G X) where
  toAddEquiv := cyclicUnitTateEquiv X l k hu
  map_smul' r x := by
    apply PowerTateModule.ext l (G X)
    intro n
    rw [evaluate_smul]
    let f := levelComparison X l k hu n
    change f (PadicInt.toZModPow n r • (x.val n)) =
      PadicInt.toZModPow n r • f (x.val n)
    exact (f.toZModLinearMap (l ^ n)).map_smul (PadicInt.toZModPow n r) (x.val n)

@[simp] theorem cyclicUnitTateLinearEquiv_apply (x : CyclicHOne X l) :
    cyclicUnitTateLinearEquiv X l k hu x = cyclicUnitTateEquiv X l k hu x := rfl

end

end ManuscriptAudit.FullEtaleCyclicUnitTateLinear

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleCyclicUnitTateLinear.cyclicUnitTateLinearEquiv_apply
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
