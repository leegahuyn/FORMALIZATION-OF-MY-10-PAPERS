import Lean.Util.CollectAxioms
import Mathlib.GroupTheory.QuotientGroup.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-! The actual small étale Kummer H¹ of a PID is naturally the quotient
of its unit group by dth powers, including over nonclosed coefficient fields. -/

namespace ManuscriptAudit.KummerPIDUnitQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open KummerAffineCohomology KummerConstantCoefficients SmallEtaleCohomologyComparison

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] KummerCohomologySequence.affineSiteHasExt fullSiteHasExt

private def powerHom (R : Type) [CommRing R] (d : ℕ) : Additive Rˣ →+ Additive Rˣ where
  toFun u := d • u
  map_zero' := nsmul_zero d
  map_add' a b := by exact nsmul_add _ _ _

/-- The subgroup of actual coordinate units that are dth powers. -/
def powerSubgroup (R : Type) [CommRing R] (d : ℕ) : AddSubgroup (Additive Rˣ) :=
  (powerHom R d).range

/-- Subgroup membership is equivalent to exhibiting an actual unit root. -/
theorem mem_powerSubgroup {R : Type} [CommRing R] (d : ℕ) (x : Additive Rˣ) :
    x ∈ powerSubgroup R d ↔ ∃ u : Rˣ, u ^ d = x.toMul := by
  rw [powerSubgroup, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨u, h⟩
    exact ⟨u.toMul, congrArg Additive.toMul h⟩
  · rintro ⟨u, h⟩
    exact ⟨Additive.ofMul u, congrArg Additive.ofMul h⟩

variable (K R : Type) [Field K] [CommRing R] [Algebra K R]
variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Genuine degree-one full étale cohomology with constant coefficient
roots, computed on the spectrum of a PID by the coordinate-unit quotient. -/
def rootsHOneEquiv (d : ℕ) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d] :
    (Additive Rˣ ⧸ powerSubgroup R d) ≃+
      Sheaf.H ((constantSheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{0}).obj
        (coefficientGroup K d)) 1 := by
  let A := CommRingCat.of R
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hK : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
  have hR : IsUnit (d : R) := by
    simpa only [map_natCast] using hK.map (algebraMap K R)
  let b := unitBoundary (K := K) A d hd hR
  have hb : Function.Surjective b :=
    unitBoundary_surjective_of_unitHOne (K := K) A d hd hR
      (AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid R)
  have hker : powerSubgroup R d = b.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, mem_powerSubgroup]
    exact (unitBoundary_eq_zero_iff (K := K) A d hd hR x).symm
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    ((QuotientAddGroup.quotientKerEquivOfSurjective b hb).trans
      (cohomologyEquiv A (coefficientGroup K d) 1))

end
end ManuscriptAudit.KummerPIDUnitQuotient

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerPIDUnitQuotient.mem_powerSubgroup,
      ``ManuscriptAudit.KummerPIDUnitQuotient.rootsHOneEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
