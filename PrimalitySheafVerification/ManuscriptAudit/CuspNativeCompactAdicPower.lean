import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicPowerSequence
import PrimalitySheafVerification.ManuscriptAudit.ProetaleOpenClosedHZero
import PrimalitySheafVerification.ManuscriptAudit.NativeSingularCurveCompactHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspProperBoundary

/-! Finite compact vanishing imposes precise prime-power torsion constraints
on the genuine integral native extension-by-zero groups of the affine cusp. -/

namespace ManuscriptAudit.CuspNativeCompactAdicPower

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open ProetaleAdicPowerSequence (compactSequence multiply compactSequence_shortExact)
open ProetaleCohomologyIso (cohomologyIso)
open OpenProetaleExtension (extensionByZero)
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ)

private abbrev A := AddCommGrpCat.{1}
private abbrev U := affineCusp K
private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev E := extensionByZero (j K) A
private abbrev S := compactSequence ℓ r (j K)
private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology (X K)) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private theorem residue_HZero_subsingleton : Subsingleton (Sheaf.H (S K ℓ r).X₃ 0) := by
  letI := CuspProperBoundary.projectiveCusp_preconnected K
  letI := infinityPoint_isClosedImmersion K
  have h : Set.range (j K) = (Set.range (infinityPoint K))ᶜ := by
    rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl]
  exact ProetaleOpenClosedHZero.compactFunctionsHZero_subsingleton K (infinityPoint K)
    (ZMod (ℓ ^ r)) (j K) h

variable [NeZero (ℓ : K)]

private theorem residue_HOne_subsingleton : Subsingleton (Sheaf.H (S K ℓ r).X₃ 1) := by
  letI : NeZero ((ℓ ^ r : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero r (NeZero.ne (ℓ : K))⟩
  letI := NativeSingularCurveCompactHOne.cusp_affine_subsingleton K (ℓ ^ r)
  let e := (E K).mapIso (ProetaleDiscreteConstant.nativeResidueIso (U K) ℓ r)
  exact (cohomologyIso (X := X K) e.symm 1).injective.subsingleton

set_option maxHeartbeats 1800000 in
private theorem injective_of_previous_residue_subsingleton (n : ℕ)
    (hResidue : Subsingleton (Sheaf.H (S K ℓ r).X₃ n)) :
    Function.Injective (Sheaf.H.map (S K ℓ r).f (n + 1)) := by
  let hS := compactSequence_shortExact ℓ r (j K)
  intro a b hab
  apply sub_eq_zero.mp
  have hz : Sheaf.H.map (S K ℓ r).f (n + 1) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := Ext.covariant_sequence_exact₁ (integers K) hS (a - b) hz
    (rfl : n + 1 = n + 1)
  have hc0 : c = 0 := hResidue.elim _ _
  rw [hc0, Ext.zero_comp] at hc
  exact hc.symm

/-- On genuine integral compact degree one, multiplication by every
power of the adic prime is bijective for the affine cusp. -/
theorem affine_HOne_multiplication_bijective :
    Function.Bijective (Sheaf.H.map ((E K).map (multiply (U K) ℓ r)) 1) := by
  let hS := compactSequence_shortExact ℓ r (j K)
  refine ⟨injective_of_previous_residue_subsingleton K ℓ r 0 (residue_HZero_subsingleton K ℓ r), ?_⟩
  intro x
  have hx : Sheaf.H.map (S K ℓ r).g 1 x = 0 :=
    (residue_HOne_subsingleton K ℓ r).elim _ _
  exact Ext.covariant_sequence_exact₂ (integers K) hS x hx

/-- Genuine integral compact degree two of the affine cusp
has injective multiplication by every power of the adic prime. -/
theorem affine_HTwo_multiplication_injective :
    Function.Injective (Sheaf.H.map ((E K).map (multiply (U K) ℓ r)) 2) :=
  injective_of_previous_residue_subsingleton K ℓ r 1 (residue_HOne_subsingleton K ℓ r)

end

end ManuscriptAudit.CuspNativeCompactAdicPower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompactAdicPower.affine_HOne_multiplication_bijective,
      ``ManuscriptAudit.CuspNativeCompactAdicPower.affine_HTwo_multiplication_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
