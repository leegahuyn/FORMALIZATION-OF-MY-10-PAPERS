import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerHOne
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveUnits
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients

/-! Native finite-coefficient Kummer H¹ of the actual proper Weierstrass closure. -/

namespace ManuscriptAudit.WeierstrassProjectiveKummer

open AlgebraicGeometry CategoryTheory
open WeierstrassProjectiveClosure KummerUnitsSheaf KummerCohomologyDegreeTwo

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K)

private abbrev X := projectiveScheme W
private abbrev J := (X W).smallEtaleTopology
private abbrev A := AddCommGrpCat.{0}

theorem globalUnitPower_surjective (d : ℕ) [NeZero (d : K)] :
    Function.Surjective (fun a : (Γ(X W, ⊤))ˣ => a ^ d) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  exact WeierstrassProjectiveUnits.unit_power_surjective W d (Nat.pos_of_ne_zero (NeZero.ne d))

/-- First cohomology with the actual constant roots-of-unity sheaf realizes
the subgroup killed by d in first projective unit cohomology. -/
def rootsHOneEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (J W) A).obj (KummerConstantCoefficients.coefficientGroup K d)) 1
      ≃+ killedBy (Sheaf.H (fullCoordinateUnitSheaf (X W)) 1) d :=
  FullEtaleKummerHOne.geometricRootsHOneEquiv (toBase W) d (globalUnitPower_surjective W d)

/-- In the constant cyclic presentation the actual projective Kummer group
is the same d-torsion subgroup after choosing a coefficient generator. -/
def cyclicHOneEquiv (d : ℕ) [NeZero (d : K)] :
    Sheaf.H ((constantSheaf (J W) A).obj (AddCommGrpCat.of (ZMod d))) 1
      ≃+ killedBy (Sheaf.H (fullCoordinateUnitSheaf (X W)) 1) d := by
  let e : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let s := (constantSheaf (J W) A).mapIso
    (e.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let h := ((Sheaf.functorH (J W) 1).mapIso s).addCommGroupIsoToAddEquiv
  exact h.symm.trans (rootsHOneEquiv W d)

end

end ManuscriptAudit.WeierstrassProjectiveKummer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveKummer.globalUnitPower_surjective,
      ``ManuscriptAudit.WeierstrassProjectiveKummer.rootsHOneEquiv,
      ``ManuscriptAudit.WeierstrassProjectiveKummer.cyclicHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
