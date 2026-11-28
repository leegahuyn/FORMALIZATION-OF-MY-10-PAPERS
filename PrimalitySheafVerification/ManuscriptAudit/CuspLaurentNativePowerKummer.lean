import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspRelativePowerMap
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineUnitPullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleLaurentCyclicHOne

/-! The actual relative cusp overlap power acts on the native Laurent
Kummer group by multiplication by its exponent. -/

namespace ManuscriptAudit.CuspLaurentNativePowerKummer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspRelativePowerMap (overlapMap)
open CuspRelativePowerCoordinates (laurentPower laurentPower_T)
open ProetaleAffineLineCyclicHOne (unitsHZeroEquiv)
open ProetaleAffineUnitPullback (unitsMap_spec)
open ProetaleUnitSheaf (unitSheaf)
open ProetaleKummerSchemePullback (unitsMap kernelMap kernelBoundary_natural)
open ProetaleKummerKernelTransition (kernelBoundary)
open ProetaleKummerPower (power)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleKummerBoundaryNative (unitBoundary)
open ProetaleLaurentCyclicHOne (exponentUnit cyclicToRootsHOne cyclicToRootsHOne_intCast)
open ProetaleCohomologyIso (cohomologyIso)
open LaurentUnitProductCoordinates (unitCoordinates unitCoordinates_apply)
open KummerUnitsSheaf (ringUnits)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev R := LaurentPolynomial K
private abbrev W := Spec (CommRingCat.of (R K))
private abbrev k : W K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (R K)))

private theorem exponent_coordinate (i : ℤ) :
    unitsHZeroEquiv (R K) (exponentUnit K i) = unitCoordinates K (0, i) := by
  change unitsHZeroEquiv (R K) ((unitsHZeroEquiv (R K)).symm (unitCoordinates K (0, i))) = _
  exact (unitsHZeroEquiv (R K)).apply_symm_apply _

private theorem coordinate_value (i : ℤ) :
    ((unitCoordinates K (0, i)).toMul : R K) = LaurentPolynomial.T i := by
  rw [unitCoordinates_apply]
  change LaurentPolynomial.C (1 : K) * LaurentPolynomial.T i = _
  rw [map_one, one_mul]

/-- Pullback of the actual Laurent unit with exponent i has exponent mi. -/
theorem units_exponent (m : ℕ) (i : ℤ) :
    unitsMap (overlapMap K m) 0 (exponentUnit K i) = exponentUnit K (i * (m : ℤ)) := by
  let a := CommRingCat.ofHom (laurentPower K m).toRingHom
  apply (unitsHZeroEquiv (R K)).injective
  change unitsHZeroEquiv (R K) (unitsMap (Spec.map a) 0 (exponentUnit K i)) = _
  rw [unitsMap_spec, exponent_coordinate, exponent_coordinate]
  apply Additive.ext
  apply Units.ext
  change laurentPower K m ((unitCoordinates K (0, i)).toMul : R K) =
    ((unitCoordinates K (0, i * (m : ℤ))).toMul : R K)
  rw [coordinate_value, coordinate_value, laurentPower_T]

variable (d : ℕ) [NeZero (d : K)]

local instance residueOrder : NeZero d := NeZero.of_neZero_natCast K

/-- The same formula holds for the actual Kummer boundary of the unit. -/
theorem boundary_exponent (m : ℕ) (i : ℤ) :
    kernelMap (overlapMap K m) d 1 (kernelBoundary (k K) d (exponentUnit K i)) =
      kernelBoundary (k K) d (exponentUnit K (i * (m : ℤ))) := by
  rw [kernelBoundary_natural (overlapMap K m) (k K) (k K) d, units_exponent]

/-- The native categorical Kummer kernel is the cyclic exponent quotient. -/
def kernelCyclicEquiv : ZMod d ≃+ Sheaf.H (kernel (power (W K) d)) 1 :=
  (cyclicToRootsHOne K d).trans (cohomologyIso (constantKernelIso (k K) d) 1)

private theorem kernelCyclic_intCast (i : ℤ) :
    kernelCyclicEquiv K d (i : ZMod d) = kernelBoundary (k K) d (exponentUnit K i) := by
  change cohomologyIso (constantKernelIso (k K) d) 1 (cyclicToRootsHOne K d (i : ZMod d)) = _
  rw [cyclicToRootsHOne_intCast]
  change cohomologyIso (constantKernelIso (k K) d) 1
    ((cohomologyIso (constantKernelIso (k K) d) 1).symm
      (kernelBoundary (k K) d (exponentUnit K i))) = _
  exact (cohomologyIso (constantKernelIso (k K) d) 1).apply_symm_apply _

set_option maxHeartbeats 5200000 in
/-- The actual relative power map multiplies the native Kummer degree-one class by m. -/
theorem kernelMap_scalar (m : ℕ) (a : ZMod d) :
    kernelMap (overlapMap K m) d 1 (kernelCyclicEquiv K d a) =
      m • kernelCyclicEquiv K d a := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
  have h : ((i * (m : ℤ) : ℤ) : ZMod d) = m • (i : ZMod d) := by
    rw [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul, mul_comm]
  rw [← map_nsmul (kernelCyclicEquiv K d), ← h, kernelCyclic_intCast, kernelCyclic_intCast,
    boundary_exponent]

end
end ManuscriptAudit.CuspLaurentNativePowerKummer

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspLaurentNativePowerKummer.units_exponent,
      ``ManuscriptAudit.CuspLaurentNativePowerKummer.boundary_exponent,
      ``ManuscriptAudit.CuspLaurentNativePowerKummer.kernelMap_scalar] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
