import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafCohomologyDimensionShift

/-! Naturality of the native H¹-to-H² connecting homomorphism. -/

namespace ManuscriptAudit.SheafCohomologyDimensionShift

open CategoryTheory CategoryTheory.Abelian

universe u v w w'

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

private abbrev Z :=
  (constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))

/-- The actual connecting homomorphism from H¹ of the quotient to H²
of the first sheaf. -/
def connectingDegreeTwo {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact) :
    Sheaf.H S.X₃ 1 →+ Sheaf.H S.X₁ 2 :=
  hS.extClass.postcomp (Z (J := J)) (show 1 + 1 = 2 by rfl)

theorem connectingDegreeTwo_surjective {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) [Injective S.X₂] :
    Function.Surjective (connectingDegreeTwo hS) :=
  (hOneQuotientEquivHTwo S hS).surjective

/-- The native long-exact-sequence connecting homomorphism is natural. -/
theorem connectingDegreeTwo_natural {S T : ShortComplex (Sheaf J AddCommGrpCat.{w})}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (b : Sheaf.H S.X₃ 1) :
    Sheaf.H.map f.τ₁ 2 (connectingDegreeTwo hS b) =
      connectingDegreeTwo hT (Sheaf.H.map f.τ₃ 1 b) := by
  have hn := ShortComplex.ShortExact.extClass_naturality hS hT f
  change (b.comp hS.extClass (show 1 + 1 = 2 by rfl)).comp (Ext.mk₀ f.τ₁) (add_zero 2) =
    (b.comp (Ext.mk₀ f.τ₃) (add_zero 1)).comp hT.extClass (show 1 + 1 = 2 by rfl)
  rw [Ext.comp_assoc_of_third_deg_zero, hn, Ext.comp_assoc_of_second_deg_zero]

end

end ManuscriptAudit.SheafCohomologyDimensionShift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafCohomologyDimensionShift.connectingDegreeTwo_surjective,
      ``ManuscriptAudit.SheafCohomologyDimensionShift.connectingDegreeTwo_natural] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
