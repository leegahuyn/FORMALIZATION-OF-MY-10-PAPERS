import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Quotient
import PrimalitySheafVerification.ManuscriptAudit.EtaleSquareZeroLift

/-!
# Étale base change over a split square-zero extension

For a compatible tower (B \to D \to k) with a section (k \to D)
and square-zero kernel, base change of an étale (B)-algebra (E)
to (D) is canonically obtained from (k \otimes_B E) by scalar
extension along the section.
-/

namespace ManuscriptAudit.EtaleSplitSquareZero

open scoped TensorProduct

noncomputable section

variable (D k : Type*) [CommRing D] [CommRing k] [Algebra D k]

/-- The augmentation ideal of the extension. -/
abbrev augmentationIdeal : Ideal D := RingHom.ker (algebraMap D k)

variable [Algebra k D] [IsScalarTower k D k]

private theorem augmentation_surjective : Function.Surjective (algebraMap D k) := by
  intro a
  refine ⟨algebraMap k D a, ?_⟩
  rw [← IsScalarTower.algebraMap_apply k D k, Algebra.algebraMap_self_apply]

private def augmentationEquiv : (D ⧸ augmentationIdeal D k) ≃ₐ[D] k :=
  AlgEquiv.ofRingEquiv
    (f := (algebraMap D k).quotientKerEquivOfSurjective (augmentation_surjective D k))
    (fun d => RingHom.quotientKerEquivOfSurjective_apply_mk (augmentation_surjective D k) d)

variable (V : Type*) [CommRing V] [Algebra D V]

/-- The square-zero ideal extended to a (D)-algebra. -/
abbrev extendedIdeal : Ideal V :=
  (augmentationIdeal D k).map (algebraMap D V)

private theorem extendedIdeal_sq (h : augmentationIdeal D k ^ 2 = ⊥) :
    extendedIdeal D k V ^ 2 = ⊥ := by
  change (Ideal.map (algebraMap D V) (augmentationIdeal D k)) ^ 2 = ⊥
  rw [← Ideal.map_pow, h, Ideal.map_bot]

set_option backward.isDefEq.respectTransparency false in
private def quotientEquiv :
    (V ⧸ extendedIdeal D k V) ≃ₐ[D] (k ⊗[D] V) :=
  (AlgEquiv.restrictScalars D
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor V (augmentationIdeal D k))).trans
      (Algebra.TensorProduct.congr (augmentationEquiv D k) (AlgEquiv.refl : V ≃ₐ[D] V))

variable (B E : Type*) [CommRing B] [CommRing E]
variable [Algebra B D] [Algebra B k] [IsScalarTower B D k] [Algebra B E]

private abbrev T := D ⊗[B] E
private abbrev S := k ⊗[B] E
private abbrev U := D ⊗[k] (S k B E)

set_option backward.isDefEq.respectTransparency false in
/-- Reducing the base change along (B \to D) yields ordinary base change along (B \to k). -/
def directReduction :
    ((T D B E) ⧸ extendedIdeal D k (T D B E)) ≃ₐ[D] (S k B E) :=
  (quotientEquiv D k (T D B E)).trans (Algebra.TensorProduct.cancelBaseChange B D D k E)

set_option backward.isDefEq.respectTransparency false in
/-- Reducing the scalar extension along (k \to D) recovers the original (k)-algebra. -/
def sectionReduction :
    ((U D k B E) ⧸ extendedIdeal D k (U D k B E)) ≃ₐ[D] (S k B E) :=
  (quotientEquiv D k (U D k B E)).trans
    ((Algebra.TensorProduct.cancelBaseChange k D D k (S k B E)).trans
      ((Algebra.TensorProduct.lid k (S k B E)).restrictScalars D))

variable [Algebra.Etale B E]

set_option backward.isDefEq.respectTransparency false in
/-- The two (D)-algebras are identified by lifting their common reduction. -/
def comparison (h : augmentationIdeal D k ^ 2 = ⊥) :
    (D ⊗[B] E) ≃ₐ[D] D ⊗[k] (k ⊗[B] E) :=
  EtaleSquareZeroLift.liftReductionIso D (T D B E) (U D k B E)
    (extendedIdeal D k (T D B E)) (extendedIdeal D k (U D k B E))
    (extendedIdeal_sq D k (T D B E) h) (extendedIdeal_sq D k (U D k B E) h)
    ((directReduction D k B E).trans (sectionReduction D k B E).symm)

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison induces the identity on the common scalar extension to (k). -/
theorem comparison_reduction (h : augmentationIdeal D k ^ 2 = ⊥) (x : D ⊗[B] E) :
    sectionReduction D k B E
        (Ideal.Quotient.mk (extendedIdeal D k (U D k B E)) (comparison D k B E h x)) =
      directReduction D k B E
        (Ideal.Quotient.mk (extendedIdeal D k (T D B E)) x) := by
  let I := extendedIdeal D k (T D B E)
  let J := extendedIdeal D k (U D k B E)
  let f := directReduction D k B E
  let g := sectionReduction D k B E
  have hcomp : (Ideal.Quotient.mkₐ D J).comp (comparison D k B E h).toAlgHom =
      (f.trans g.symm).toAlgHom.comp (Ideal.Quotient.mkₐ D I) :=
    EtaleSquareZeroLift.liftReductionIso_spec D (T D B E) (U D k B E) I J
      (extendedIdeal_sq D k (T D B E) h) (extendedIdeal_sq D k (U D k B E) h)
      (f.trans g.symm)
  have hx : Ideal.Quotient.mk J (comparison D k B E h x) =
      g.symm (f (Ideal.Quotient.mk I x)) :=
    DFunLike.congr_fun hcomp x
  calc
    _ = g (g.symm (f (Ideal.Quotient.mk I x))) := congrArg g hx
    _ = _ := g.apply_symm_apply _

end

end ManuscriptAudit.EtaleSplitSquareZero

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleSplitSquareZero.directReduction,
      ``ManuscriptAudit.EtaleSplitSquareZero.sectionReduction,
      ``ManuscriptAudit.EtaleSplitSquareZero.comparison,
      ``ManuscriptAudit.EtaleSplitSquareZero.comparison_reduction] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
