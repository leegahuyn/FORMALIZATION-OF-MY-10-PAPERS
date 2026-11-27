import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeFull
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyVanishingLeft

/-! Degreewise Kummer vanishing for actual cyclic constant coefficients over an algebraically closed field. -/

namespace ManuscriptAudit.KummerCohomologyVanishing

open AlgebraicGeometry CategoryTheory KummerUnitsSheaf

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

theorem cyclic_H_succ_subsingleton {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (k : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [NeZero (d : K)] (n : ℕ)
    (hPrev : Subsingleton (Sheaf.H (fullCoordinateUnitSheaf X) n))
    (hNext : Subsingleton (Sheaf.H (fullCoordinateUnitSheaf X) (n + 1))) :
    Subsingleton (Sheaf.H ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) (n + 1)) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let S := KummerRelativeFull.sequence X d
  have hS : S.ShortExact := KummerRelativeFull.sequence_shortExact k d (Nat.pos_of_ne_zero (NeZero.ne d))
  let e := KummerRelativeFull.unitsIso (X := X) d
  let H (v : ℕ) := ((Sheaf.functorH X.smallEtaleTopology v).mapIso e).addCommGroupIsoToAddEquiv
  have hRight : Subsingleton (Sheaf.H S.X₃ n) :=
    ⟨fun x y => (H n).symm.injective (hPrev.elim _ _)⟩
  have hMid : Subsingleton (Sheaf.H S.X₂ (n + 1)) :=
    ⟨fun x y => (H (n + 1)).symm.injective (hNext.elim _ _)⟩
  have hLeft := SheafCohomologyVanishingLeft.H_succ_subsingleton S hS n hRight hMid
  let eRoots : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let eCoefficients := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).mapIso
    (eRoots.toAddCommGrpIso :
      KummerConstantCoefficients.coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let eFirst := eCoefficients.symm ≪≫ KummerRelativeFull.firstIso (d := d) k
  let eH := ((Sheaf.functorH X.smallEtaleTopology (n + 1)).mapIso eFirst).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => eH.injective (hLeft.elim _ _)⟩

end
end ManuscriptAudit.KummerCohomologyVanishing

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.KummerCohomologyVanishing.cyclic_H_succ_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
