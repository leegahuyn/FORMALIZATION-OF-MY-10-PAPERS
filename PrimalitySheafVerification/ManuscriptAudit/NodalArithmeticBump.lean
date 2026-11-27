import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLaurentHOne
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLineHOne
import PrimalitySheafVerification.ManuscriptAudit.BinaryConstantCohomology
import PrimalitySheafVerification.ManuscriptAudit.NodalArithmeticProjectiveHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusCohomology

/-! The proper nodal curve and its smooth locus have two ordinary arithmetic
mod-two classes over F₅, even though the curve is nonsmooth. -/

namespace ManuscriptAudit.NodalArithmeticBump

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase)
open NodalArithmeticProjectiveHOne (properHOne)
open NodalSmoothLocusOverlap (smoothScheme)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev M := ZMod 2
private abbrev C := AddCommGrpCat.{0}
private abbrev J := (projectiveNode K).smallEtaleTopology
private abbrev J' := (smoothScheme K).smallEtaleTopology

abbrev smoothHOne :=
  Sheaf.H ((constantSheaf (J' K) C).obj (AddCommGrpCat.of M)) 1

def properModule : Module M (properHOne K) :=
  BinaryConstantCohomology.coefficientModule (J K) 1

def smoothModule : Module M (smoothHOne K) :=
  BinaryConstantCohomology.coefficientModule (J' K) 1

set_option maxRecDepth 7000 in
/-- Exact dimensions of the actual projective and smooth H¹ over a field
with the indicated binary square classes. -/
theorem finranks_eq_two (h2 : (2 : K) ≠ 0)
    (hLine : M ≃+ NodalNormalizationHOneComparison.normalizationHOne K)
    (hSmooth : (M × M) ≃+ smoothHOne K)
    (u : Kˣ) (hu : ¬ ∃ v : Kˣ, v ^ (2 : ℕ) = u) :
    letI := properModule K
    letI := smoothModule K
    Module.finrank M (properHOne K) = 2 ∧ Module.finrank M (smoothHOne K) = 2 := by
  obtain ⟨hP, hCard⟩ := NodalArithmeticProjectiveHOne.finite_card_eq_four K h2 hLine u hu
  letI : Finite (properHOne K) := hP
  letI : Finite (smoothHOne K) := Finite.of_injective hSmooth.symm hSmooth.symm.injective
  letI := properModule K
  letI := smoothModule K
  have hProd : Nat.card (M × M) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card] <;> rfl
  have hSmoothCard : Nat.card (smoothHOne K) = 4 :=
    (Nat.card_congr hSmooth.symm.toEquiv).trans hProd
  exact ⟨BinaryConstantCohomology.finrank_eq_two_of_card_four (J K) 1 hCard,
    BinaryConstantCohomology.finrank_eq_two_of_card_four (J' K) 1 hSmoothCard⟩

private abbrev K₅ := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def twoUnit : K₅ˣ := Units.mk0 2 (by decide)

private theorem twoUnit_nonsquare : ¬ ∃ v : K₅ˣ, v ^ (2 : ℕ) = twoUnit := by
  rintro ⟨v, hv⟩
  have hn : ∀ a : K₅, a ^ (2 : ℕ) ≠ (2 : K₅) := by decide
  exact hn (v : K₅) (congrArg Units.val hv)

private def smoothHOneF5Equiv : (M × M) ≃+ smoothHOne K₅ :=
  ArithmeticLaurentHOne.laurentCyclicHOneEquiv.trans
    (SmallEtaleEquivalenceCohomology.schemeIsoCohomologyEquiv
      (NodalSmoothLocusGm.smoothLocusIsoGm K₅ (by decide)).symm (AddCommGrpCat.of M) 1)

/-- The ordinary arithmetic bump vanishes on this actual nonsmooth
projective curve over F₅ with constant Z/2 coefficients. -/
theorem f5_zero_bump_and_not_smooth :
    letI := properModule K₅
    letI := smoothModule K₅
    ((Module.finrank M (properHOne K₅) : ℤ) - Module.finrank M (smoothHOne K₅) = 0) ∧
      ¬ AlgebraicGeometry.Smooth (projectiveNodeToBase K₅) := by
  letI := properModule K₅
  letI := smoothModule K₅
  obtain ⟨hp, hs⟩ := finranks_eq_two K₅ (by decide)
    ArithmeticLineHOne.affineLineCyclicHOneEquiv smoothHOneF5Equiv twoUnit twoUnit_nonsquare
  exact ⟨by rw [hp, hs, sub_self], NodalSmoothCharts.projectiveNode_not_smooth K₅⟩

end
end ManuscriptAudit.NodalArithmeticBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalArithmeticBump.finranks_eq_two,
      ``ManuscriptAudit.NodalArithmeticBump.f5_zero_bump_and_not_smooth] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
