import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Ideal
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineReducedFibres

/-! The principal closed fibres remain reduced in every actual local
chart of a weakly étale affine scheme over the affine line. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineLocalReducedFibres

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B]
  [Algebra (Polynomial K) B] [WeaklyEtale (structureMap (Polynomial K) B)]

theorem reduced_atPrime (p : Polynomial K) (hp : Prime p) (q : Ideal B) [q.IsPrime] :
    IsReduced (Localization.AtPrime q ⧸ Ideal.span
      ({algebraMap B (Localization.AtPrime q) (algebraMap (Polynomial K) B p)} :
        Set (Localization.AtPrime q))) := by
  let s := algebraMap (Polynomial K) B p
  let J := Ideal.span ({s} : Set B)
  let D := Localization.AtPrime q
  letI : IsReduced (B ⧸ J) := WeaklyEtaleAffineLineReducedFibres.reduced_prime_fibre K B p hp
  have e : J.map (algebraMap B D) = Ideal.span ({algebraMap B D s} : Set D) := by
    simp only [J, Ideal.map_span, Set.image_singleton]
  rw [← e]
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (B ⧸ J) q.primeCompl) _ inferInstance

end
end ManuscriptAudit.WeaklyEtaleAffineLineLocalReducedFibres

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineLocalReducedFibres.reduced_atPrime
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
