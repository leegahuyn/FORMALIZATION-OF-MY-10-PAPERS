import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineWeaklyEtaleCommonCountableCover

/-! An actual common affine refinement for countably many weakly étale surjections. -/

namespace ManuscriptAudit.AffineSchemeWeaklyEtaleRefinement

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev ring (Y : Scheme.{0}) := Scheme.Γ.obj (op Y)

private theorem specMap_appTop_weaklyEtale {U Y : Scheme.{0}} [IsAffine U] [IsAffine Y]
    (f : U ⟶ Y) [WeaklyEtale f] : WeaklyEtale (Spec.map f.appTop) := by
  have h :
      Spec.map f.appTop = U.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [h]
  infer_instance

private theorem specMap_appTop_surjective {U Y : Scheme.{0}} [IsAffine U] [IsAffine Y]
    (f : U ⟶ Y) [Surjective f] : Surjective (Spec.map f.appTop) := by
  have h :
      Spec.map f.appTop = U.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Category.assoc, ← Scheme.isoSpec_inv_naturality, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [h]
  infer_instance

private def rings {Y : Scheme.{0}} {U : ℕ → Scheme.{0}} (f : ∀ n, U n ⟶ Y)
    (n : ℕ) : CommAlgCat.{0} (ring Y) :=
  letI : Algebra (ring Y) (ring (U n)) := (f n).appTop.hom.toAlgebra
  CommAlgCat.of (ring Y) (ring (U n))

private theorem rings_structure {Y : Scheme.{0}} {U : ℕ → Scheme.{0}}
    (f : ∀ n, U n ⟶ Y) (n : ℕ) :
    ProetaleAffineTensor.structureMap (ring Y) (rings f n) = Spec.map (f n).appTop := by
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  rfl

theorem exists_refinement {Y : Scheme.{0}} [IsAffine Y] (U : ℕ → Scheme.{0})
    (f : ∀ n, U n ⟶ Y)
    (hA : ∀ n, IsAffine (U n)) (hW : ∀ n, WeaklyEtale (f n)) (hS : ∀ n, Surjective (f n)) :
    ∃ (W : Scheme.{0}) (g : W ⟶ Y) (k : ∀ n, W ⟶ U n),
      IsAffine W ∧ WeaklyEtale g ∧ Surjective g ∧ ∀ n, k n ≫ f n = g := by
  let B := rings f
  have hWeak (n : ℕ) : WeaklyEtale (ProetaleAffineTensor.structureMap (ring Y) (B n)) := by
    letI := hA n
    letI := hW n
    rw [show ProetaleAffineTensor.structureMap (ring Y) (B n) =
      Spec.map (f n).appTop from rings_structure f n]
    exact specMap_appTop_weaklyEtale (f n)
  have hFaithful (n : ℕ) : Module.FaithfullyFlat (ring Y) (B n) := by
    letI := hA n
    letI := hW n
    letI := hS n
    exact RingHom.faithfullyFlat_algebraMap_iff.mp
      ((Flat.flat_and_surjective_SpecMap_iff (f n).appTop).mp
        ⟨(specMap_appTop_weaklyEtale (f n)).flat, specMap_appTop_surjective (f n)⟩)
  let c := AffineEtaleCommonCountableCover.coverMap B
  letI : WeaklyEtale c := AffineWeaklyEtaleCommonCountableCover.cover_weaklyEtale B hFaithful hWeak
  letI : Surjective c := AffineEtaleCommonCountableCover.cover_surjective B hFaithful
  let k (n : ℕ) := by
    letI := hA n
    exact AffineEtaleCommonCountableCover.factorMap B n ≫ (U n).isoSpec.inv
  refine ⟨_, c ≫ Y.isoSpec.inv, k, inferInstance, inferInstance, inferInstance, ?_⟩
  intro n
  letI := hA n
  change (AffineEtaleCommonCountableCover.factorMap B n ≫ (U n).isoSpec.inv) ≫ f n =
    c ≫ Y.isoSpec.inv
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, ← Category.assoc,
    ← rings_structure f n, AffineEtaleCommonCountableCover.factor_comp]

end
end ManuscriptAudit.AffineSchemeWeaklyEtaleRefinement

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineSchemeWeaklyEtaleRefinement.exists_refinement
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
