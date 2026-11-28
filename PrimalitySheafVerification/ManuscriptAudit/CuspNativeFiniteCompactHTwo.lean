import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoPositiveCharacteristic
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteCompactHTwoEquiv

/-! The actual finite-residue generator computes both native
compact-support cusp groups, including the manuscript's prime level. -/

namespace ManuscriptAudit.CuspNativeFiniteCompactHTwo

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)
open CuspNativeCompactSmoothHOne (smoothOpen punctured_range properOrigin_closed)
open SmallEtaleGeometricBaseChange (cuspOrigin cuspOrigin_closedImmersion cuspPuncturedOpen)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleConstantRestriction (constant)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (extensionByZero)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
  (p ℓ : ℕ) [hp : Fact p.Prime] [hchar : CharP K p] [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev U := affineCusp K
private abbrev V := (cuspPuncturedOpen K).toScheme
private abbrev j := affineOpen K
private abbrev v := (cuspPuncturedOpen K).ι
private abbrev b := cuspOrigin K

local instance zmodTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance zmodDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

local instance residueOrder (n : ℕ) : NeZero (ℓ ^ n) :=
  ⟨pow_ne_zero _ (Fact.out : Nat.Prime ℓ).ne_zero⟩

private abbrev F (n : ℕ) := ZMod (ℓ ^ n)

private def affineToAmbient (n : ℕ) :
    Sheaf.H ((extensionByZero (j K) A).obj (functions (F ℓ n) (U K))) 2 ≃+
      Sheaf.H (functions (F ℓ n) (X K)) 2 := by
  letI := infinityPoint_isClosedImmersion K
  exact ProetaleFiniteCompactHTwoEquiv.singleEquiv K (F ℓ n) (j K) (infinityPoint K) (by
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl])

include p hp hchar in
/-- The actual finite Laurent generator is a bijective homomorphism. -/
def properEquiv (n : ℕ) :
    F ℓ n ≃+ Sheaf.H (functions (F ℓ n) (X K)) 2 :=
  AddEquiv.ofBijective (CuspNativeAdicHTwoReduction.residueInclusion K ℓ n)
    ⟨CuspNativeAdicHTwoReduction.residueInclusion_injective K ℓ n,
      CuspNativeAdicHTwoPositiveCharacteristic.residueInclusion_surjective K p ℓ n⟩

include p hp hchar in
/-- Actual native finite compact-support degree two of the affine cusp. -/
def affineCompactEquiv (n : ℕ) :
    F ℓ n ≃+ Sheaf.H ((extensionByZero (j K) A).obj (constant (U K) (F ℓ n))) 2 :=
  (properEquiv K p ℓ n).trans ((affineToAmbient K ℓ n).symm.trans
    (cohomologyIso (X := X K) ((extensionByZero (j K) A).mapIso
      (ProetaleDiscreteConstant.constantIso (U K) (F ℓ n))).symm 2))

include p hp hchar in
/-- Actual native finite compact-support degree two of the punctured cusp. -/
def smoothCompactEquiv (n : ℕ) :
    F ℓ n ≃+ Sheaf.H ((extensionByZero (smoothOpen K) A).obj (constant (V K) (F ℓ n))) 2 := by
  letI := cuspOrigin_closedImmersion K
  letI := properOrigin_closed K
  let e := ProetaleFiniteCompactHTwoEquiv.nestedEquiv K (F ℓ n) (v K) (j K) (b K)
    (punctured_range K)
  exact (properEquiv K p ℓ n).trans ((affineToAmbient K ℓ n).symm.trans
    (e.symm.trans (cohomologyIso (X := X K) ((extensionByZero (smoothOpen K) A).mapIso
      (ProetaleDiscreteConstant.constantIso (V K) (F ℓ n))).symm 2)))

include p hp hchar in
/-- The prime-level compact affine group appearing in the manuscript. -/
def affinePrimeCompactEquiv :
    ZMod ℓ ≃+ Sheaf.H ((extensionByZero (j K) A).obj (constant (U K) (ZMod ℓ))) 2 := by
  simpa only [F, pow_one] using affineCompactEquiv K p ℓ 1

include p hp hchar in
/-- The prime-level compact smooth group appearing in the manuscript. -/
def smoothPrimeCompactEquiv :
    ZMod ℓ ≃+ Sheaf.H ((extensionByZero (smoothOpen K) A).obj (constant (V K) (ZMod ℓ))) 2 := by
  simpa only [F, pow_one] using smoothCompactEquiv K p ℓ 1

end
end ManuscriptAudit.CuspNativeFiniteCompactHTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeFiniteCompactHTwo.properEquiv,
      ``ManuscriptAudit.CuspNativeFiniteCompactHTwo.affinePrimeCompactEquiv,
      ``ManuscriptAudit.CuspNativeFiniteCompactHTwo.smoothPrimeCompactEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
