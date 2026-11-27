import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLaurentBinary
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured
import PrimalitySheafVerification.ManuscriptAudit.CuspSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology

/-! The arithmetic cusp and its puncture have binary H¹ of sizes two and four. -/

namespace ManuscriptAudit.ArithmeticCuspBinary

open AlgebraicGeometry CategoryTheory
open CuspAffineEtale CuspPunctured

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K] [Finite K]

private abbrev C := AddCommGrpCat.of (ZMod 2)
private abbrev puncture := Spec (CommRingCat.of (Localization.Away (cuspSquare K)))

def cuspHOneEquiv (p : ℕ) [Fact p.Prime] [CharP K p] (h₂ : (2 : K) ≠ 0) :
    ZMod 2 ≃+ Sheaf.H ((constantSheaf (Cusp K).smallEtaleTopology AddCommGrpCat.{0}).obj C) 1 :=
  (ArithmeticKummerSquareClasses.affineLineBinaryHOneEquiv K h₂).trans
    (CuspSmallEtaleCohomology.normalizationCohomologyEquiv K p C 1).symm

def punctureHOneEquiv (h₂ : (2 : K) ≠ 0) :
    (ZMod 2 × ZMod 2) ≃+
      Sheaf.H ((constantSheaf (puncture K).smallEtaleTopology AddCommGrpCat.{0}).obj C) 1 := by
  let e := (paper2_cusp_punctured_coordinate_equiv K).toRingEquiv.toCommRingCatIso
  exact (ArithmeticLaurentBinary.laurentBinaryHOneEquiv K h₂).trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv (Scheme.Spec.mapIso e.op) C 1)

theorem cusp_and_puncture_HOne_card (p : ℕ) [Fact p.Prime] [CharP K p] (h₂ : (2 : K) ≠ 0) :
    Nat.card (Sheaf.H ((constantSheaf (Cusp K).smallEtaleTopology AddCommGrpCat.{0}).obj C) 1) = 2 ∧
    Nat.card (Sheaf.H ((constantSheaf (puncture K).smallEtaleTopology AddCommGrpCat.{0}).obj C) 1) = 4 := by
  constructor
  · rw [← Nat.card_congr (cuspHOneEquiv K p h₂).toEquiv, Nat.card_zmod]
  · rw [← Nat.card_congr (punctureHOneEquiv K h₂).toEquiv, Nat.card_prod, Nat.card_zmod]

end
end ManuscriptAudit.ArithmeticCuspBinary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticCuspBinary.cuspHOneEquiv,
      ``ManuscriptAudit.ArithmeticCuspBinary.punctureHOneEquiv,
      ``ManuscriptAudit.ArithmeticCuspBinary.cusp_and_puncture_HOne_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
