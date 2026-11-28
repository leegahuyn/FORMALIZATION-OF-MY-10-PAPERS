import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.BaseChange
import PrimalitySheafVerification.ManuscriptAudit.FlatSurjectionLocalization

/-! A flat closed affine restriction lifts across an ambient quotient as
an actual localization square. -/

namespace ManuscriptAudit.FlatSurjectionLocalizationLift

open CategoryTheory
open FlatSurjectionLocalization

noncomputable section
universe u

variable (R D E : Type u) [CommRing R] [CommRing D] [CommRing E]
variable [Algebra R D] [Algebra D E]

def denominators : Submonoid R :=
  (oneFiber D E).comap (algebraMap R D).toMonoidHom

abbrev Ambient := Localization (denominators R D E)

private theorem maps_to_unit (x : denominators R D E) :
    IsUnit (((algebraMap D E).comp (algebraMap R D)) (x : R)) := by
  have h : ((algebraMap D E).comp (algebraMap R D)) (x : R) = 1 := x.2
  rw [h]
  exact isUnit_one

/-- The actual lift of the visible closed-fiber localization. -/
def lift : Ambient R D E →+* E :=
  IsLocalization.lift (M := denominators R D E) (maps_to_unit R D E)

theorem lift_comp :
    (lift R D E).comp (algebraMap R (Ambient R D E)) =
      (algebraMap D E).comp (algebraMap R D) :=
  IsLocalization.lift_comp (M := denominators R D E) (maps_to_unit R D E)

/-- Base-changing the ambient localization gives back the literal original
flat quotient and the specified quotient map, not an auxiliary model. -/
theorem isPushout [Module.Flat D E]
    (hD : Function.Surjective (algebraMap R D))
    (hE : Function.Surjective (algebraMap D E)) :
    IsPushout (CommRingCat.ofHom (algebraMap R D))
      (CommRingCat.ofHom (algebraMap R (Ambient R D E)))
      (CommRingCat.ofHom (algebraMap D E))
      (CommRingCat.ofHom (lift R D E)) := by
  let M := denominators R D E
  have hmon : M.map (algebraMap R D) = oneFiber D E := by
    exact Submonoid.map_comap_eq_self_of_surjective hD
  letI : IsLocalization (M.map (algebraMap R D)) E := by
    rw [hmon]
    exact FlatSurjectionLocalization.isLocalization hE
  exact CommRingCat.isPushout_of_isLocalization (algebraMap R D) (lift R D E)
    (lift_comp R D E) M

end
end ManuscriptAudit.FlatSurjectionLocalizationLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FlatSurjectionLocalizationLift.isPushout
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
