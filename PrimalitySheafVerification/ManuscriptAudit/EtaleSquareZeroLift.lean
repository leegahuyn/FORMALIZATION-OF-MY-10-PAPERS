import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.Basic

/-!
# Lifting étale isomorphisms across square-zero ideals

An isomorphism of square-zero reductions between two formally étale
algebras lifts to an isomorphism of the algebras. This gives the
comparison on the common quotient in conductor patching.
-/

namespace ManuscriptAudit.EtaleSquareZeroLift

noncomputable section

variable (R E F : Type*) [CommRing R] [CommRing E] [CommRing F]
variable [Algebra R E] [Algebra R F]
variable [Algebra.FormallyEtale R E] [Algebra.FormallyEtale R F]
variable (I : Ideal E) (J : Ideal F) (hI : I ^ 2 = ⊥) (hJ : J ^ 2 = ⊥)
variable (e : (E ⧸ I) ≃ₐ[R] F ⧸ J)

private def liftForward : E →ₐ[R] F :=
  Classical.choose ((Algebra.FormallyEtale.comp_bijective R E J hJ).surjective
    (e.toAlgHom.comp (Ideal.Quotient.mkₐ R I)))

private theorem liftForward_spec :
    (Ideal.Quotient.mkₐ R J).comp (liftForward R E F I J hJ e) =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R I) :=
  Classical.choose_spec ((Algebra.FormallyEtale.comp_bijective R E J hJ).surjective
    (e.toAlgHom.comp (Ideal.Quotient.mkₐ R I)))

/-- The unique lifts of the isomorphism and its inverse are mutual inverses. -/
def liftReductionIso : E ≃ₐ[R] F := by
  let f := liftForward R E F I J hJ e
  let g := liftForward R F E J I hI e.symm
  have hf := liftForward_spec R E F I J hJ e
  have hg := liftForward_spec R F E J I hI e.symm
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply (Algebra.FormallyEtale.comp_bijective R F J hJ).injective
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk J (f (g x)) = Ideal.Quotient.mk J x
    calc
      _ = e (Ideal.Quotient.mk I (g x)) := DFunLike.congr_fun hf (g x)
      _ = e (e.symm (Ideal.Quotient.mk J x)) := congrArg e (DFunLike.congr_fun hg x)
      _ = _ := e.apply_symm_apply _
  · apply (Algebra.FormallyEtale.comp_bijective R E I hI).injective
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk I (g (f x)) = Ideal.Quotient.mk I x
    calc
      _ = e.symm (Ideal.Quotient.mk J (f x)) := DFunLike.congr_fun hg (f x)
      _ = e.symm (e (Ideal.Quotient.mk I x)) := congrArg e.symm (DFunLike.congr_fun hf x)
      _ = _ := e.symm_apply_apply _

/-- The lifted isomorphism reduces to the given one. -/
theorem liftReductionIso_spec :
    (Ideal.Quotient.mkₐ R J).comp (liftReductionIso R E F I J hI hJ e).toAlgHom =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ R I) :=
  liftForward_spec R E F I J hJ e

/-- Any algebra map inducing the given reduction is the lifted isomorphism. -/
theorem liftReductionIso_unique (f : E →ₐ[R] F)
    (hf : (Ideal.Quotient.mkₐ R J).comp f = e.toAlgHom.comp (Ideal.Quotient.mkₐ R I)) :
    f = (liftReductionIso R E F I J hI hJ e).toAlgHom :=
  (Algebra.FormallyEtale.comp_bijective R E J hJ).injective
    (hf.trans (liftReductionIso_spec R E F I J hI hJ e).symm)

end

end ManuscriptAudit.EtaleSquareZeroLift

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleSquareZeroLift.liftReductionIso,
      ``ManuscriptAudit.EtaleSquareZeroLift.liftReductionIso_spec,
      ``ManuscriptAudit.EtaleSquareZeroLift.liftReductionIso_unique] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
