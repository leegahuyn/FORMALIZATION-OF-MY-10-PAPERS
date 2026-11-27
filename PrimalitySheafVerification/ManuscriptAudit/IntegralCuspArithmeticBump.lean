import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineCuspSmoothLocus
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticCuspBump
import PrimalitySheafVerification.ManuscriptAudit.BinaryConstantCohomology
import PrimalitySheafVerification.ManuscriptAudit.IntegralCuspNodalAffine
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoSmallEtaleCohomology
import PrimalitySheafVerification.ManuscriptAudit.SmoothLocusUnderIso

/-! The signed arithmetic counterexample on the actual residue fiber of
the flat integral cusp model, with its genuine relative smooth locus. -/

namespace ManuscriptAudit.IntegralCuspArithmeticBump

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralCuspNodalAffine (coefficientPoint cuspToInt cuspFiberIso cuspFiberIso_over)
open SmallEtaleEquivalenceCohomology (schemeIsoCohomologyEquiv)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 7000

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

/-- The actual cusp scheme fiber over its coefficient field. -/
abbrev fiber := pullback (coefficientPoint K) cuspToInt

def fiberToBase : fiber K ⟶ Spec (CommRingCat.of K) :=
  pullback.fst _ _

/-- The actual relative smooth scheme of the integral family's residue fiber. -/
def fiberSmoothIso :
    (fiberToBase K).smoothLocus.toScheme ≅ AffineCuspSmoothLocus.punctured K :=
  SmoothLocusUnderIso.iso (cuspFiberIso K) (fiberToBase K)
    (AffineCuspSmoothLocus.cuspToBase K) (cuspFiberIso_over K) ≪≫
    AffineCuspSmoothLocus.smoothLocusIso K

private abbrev K₅ := ZMod 5
private abbrev M := ZMod 2
private abbrev C := AddCommGrpCat.{0}
private abbrev coeff := AddCommGrpCat.of M
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private abbrev X₅ := fiber K₅
private abbrev U₅ := (fiberToBase K₅).smoothLocus.toScheme

abbrev fiberHOne := Sheaf.H ((constantSheaf X₅.smallEtaleTopology C).obj coeff) 1
abbrev smoothHOne := Sheaf.H ((constantSheaf U₅.smallEtaleTopology C).obj coeff) 1

def fiberModule : Module M fiberHOne :=
  BinaryConstantCohomology.coefficientModule X₅.smallEtaleTopology 1

def smoothModule : Module M smoothHOne :=
  BinaryConstantCohomology.coefficientModule U₅.smallEtaleTopology 1

/-- The actual mod-two degree-one dimensions over F₅ are one and two. -/
theorem f5_finranks :
    letI := fiberModule
    letI := smoothModule
    Module.finrank M fiberHOne = 1 ∧ Module.finrank M smoothHOne = 2 := by
  letI := fiberModule
  letI := smoothModule
  let e : M ≃+ fiberHOne := ArithmeticCuspBump.cuspCyclicHOneEquiv.trans
    (schemeIsoCohomologyEquiv (cuspFiberIso K₅) coeff 1).symm
  let f : (M × M) ≃+ smoothHOne := ArithmeticLaurentHOne.puncturedCuspCyclicHOneEquiv.trans
    (schemeIsoCohomologyEquiv (fiberSmoothIso K₅) coeff 1).symm
  let eL : M ≃ₗ[M] fiberHOne := { e with map_smul' := ZMod.map_smul e }
  letI : Finite smoothHOne := Finite.of_injective f.symm f.symm.injective
  have hProd : Nat.card (M × M) = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card] <;> rfl
  have hSmooth : Nat.card smoothHOne = 4 := (Nat.card_congr f.symm.toEquiv).trans hProd
  exact ⟨eL.finrank_eq.symm.trans (CommSemiring.finrank_self _),
    BinaryConstantCohomology.finrank_eq_two_of_card_four U₅.smallEtaleTopology 1 hSmooth⟩

/-- The literal signed arithmetic difference on this flat finite-type
Spec ℤ family's actual p=5 fiber equals −1. -/
theorem f5_signed_bump :
    letI := fiberModule
    letI := smoothModule
    (Module.finrank M fiberHOne : ℤ) - Module.finrank M smoothHOne = -1 := by
  letI := fiberModule
  letI := smoothModule
  obtain ⟨hp, hs⟩ := f5_finranks
  rw [hp, hs] <;> decide

end
end ManuscriptAudit.IntegralCuspArithmeticBump

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.IntegralCuspArithmeticBump.fiberSmoothIso,
      ``ManuscriptAudit.IntegralCuspArithmeticBump.f5_finranks,
      ``ManuscriptAudit.IntegralCuspArithmeticBump.f5_signed_bump] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
