import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Finiteness.Basic
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportAbsoluteHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportEuler

/-!
# The actual compact-support Euler difference for every common truncation

For coefficients prime to the field characteristic, the checked
absolute degree-zero and degree-one calculations give the finite
dimensions required by the relative Euler identity. The higher
groups are identified in each degree by the actual localization.
-/

namespace ManuscriptAudit.CuspCompactSupportAbsoluteEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open CuspProperCompactification CuspCompactSupportSequence
open OpenEtaleExtension SmallEtaleGeometricBaseChange
open scoped BigOperators

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
attribute [local instance] CuspCompactSupportEuler.cuspModule CuspCompactSupportEuler.punctureModule

variable (K : Type) [Field K] [kClosed : IsAlgClosed K]
variable (p : ℕ) [pPrime : Fact p.Prime] [pChar : CharP K p]
variable (ℓ : ℕ) [Fact ℓ.Prime] [coeffNZ : NeZero (ℓ : K)]

private abbrev G := AddCommGrpCat.{0}
private abbrev M : G := AddCommGrpCat.of (ULift.{0} (ZMod ℓ))
private abbrev m : G := AddCommGrpCat.of (ZMod ℓ)

private def coefficientIso : M ℓ ≅ m ℓ :=
  (show ULift.{0} (ZMod ℓ) ≃+ ZMod ℓ from
    { toFun := ULift.down, invFun := ULift.up, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }).toAddCommGrpIso

private def extensionCohomologyEquiv {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) :
    Sheaf.H ((extensionByZero j G).obj ((constantSheaf U.smallEtaleTopology G).obj (M ℓ))) n ≃+
      Sheaf.H ((extensionByZero j G).obj ((constantSheaf U.smallEtaleTopology G).obj (m ℓ))) n :=
  ((Sheaf.functorH X.smallEtaleTopology n).mapIso
    ((extensionByZero j G).mapIso
      ((constantSheaf U.smallEtaleTopology G).mapIso (coefficientIso ℓ)))).addCommGroupIsoToAddEquiv

private def cuspCoefficients (n : ℕ) : cuspHc K (M ℓ) n ≃+ cuspHc K (m ℓ) n :=
  extensionCohomologyEquiv ℓ (affineOpen K) n

private def punctureCoefficients (n : ℕ) :
    punctureHc K (M ℓ) n ≃+ punctureHc K (m ℓ) n :=
  extensionCohomologyEquiv ℓ ((cuspPuncturedOpen K).ι ≫ affineOpen K) n

/-- Euler sum through degree N+1, expressed as the first two degrees and the tail. -/
def truncatedEuler (d : ℕ → ℕ) (N : ℕ) : ℤ :=
  (d 0 : ℤ) - d 1 + ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * d (n + 2)

include kClosed p pPrime pChar coeffNZ

/-- For these actual groups the difference is one in every common truncation. -/
theorem actualTruncatedEulerDifference (N : ℕ) :
    truncatedEuler (fun n => Module.finrank (ZMod ℓ) (cuspHc K (M ℓ) n)) N -
      truncatedEuler (fun n => Module.finrank (ZMod ℓ) (punctureHc K (M ℓ) n)) N = 1 := by
  obtain ⟨hP₀, hC₀⟩ := compactSupportHZero_subsingleton K (M ℓ)
  letI : Finite (punctureHc K (M ℓ) 0) :=
    Finite.of_injective (fun _ : punctureHc K (M ℓ) 0 => PUnit.unit) (fun x y _ => hP₀.allEq x y)
  letI : Finite (cuspHc K (M ℓ) 0) :=
    Finite.of_injective (fun _ : cuspHc K (M ℓ) 0 => PUnit.unit) (fun x y _ => hC₀.allEq x y)
  let eC := cuspCoefficients K ℓ 1
  have hC₁ := CuspCompactSupportAbsoluteHOne.cuspHcOne_subsingleton K p ℓ
  letI : Finite (cuspHc K (M ℓ) 1) :=
    Finite.of_injective (fun _ : cuspHc K (M ℓ) 1 => PUnit.unit)
      (fun x y _ => eC.injective (hC₁.allEq (eC x) (eC y)))
  let eP := (punctureCoefficients K ℓ 1).trans
    (CuspCompactSupportAbsoluteHOne.punctureHcOneEquiv K p ℓ)
  letI : Finite (punctureHc K (M ℓ) 1) := Finite.of_injective eP eP.injective
  exact CuspCompactSupportEuler.truncatedEulerDifference K ℓ N

end

end ManuscriptAudit.CuspCompactSupportAbsoluteEuler

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.CuspCompactSupportAbsoluteEuler.actualTruncatedEulerDifference
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
