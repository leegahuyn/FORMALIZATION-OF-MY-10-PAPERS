import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCommonCountableCover
import PrimalitySheafVerification.ManuscriptAudit.FinitePrincipalClosedSectionLift
import PrimalitySheafVerification.ManuscriptAudit.PadicContinuousLiftFromResidues

/-! A continuous adic section on the closed fiber of an affine chart
extends after one genuine surjective affine weakly étale refinement. -/

namespace ManuscriptAudit.AffineAdicClosedSectionLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Z X U V : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual map of closed fibers induced by a refinement of the first chart. -/
def fiberMap (g : U ⟶ X) (a : V ⟶ U) :
    pullback (a ≫ g) i ⟶ pullback g i :=
  pullback.lift (pullback.fst (a ≫ g) i ≫ a) (pullback.snd (a ≫ g) i) (by
    rw [Category.assoc, pullback.condition])

@[reassoc]
theorem fiberMap_fst (g : U ⟶ X) (a : V ⟶ U) :
    fiberMap i g a ≫ pullback.fst g i = pullback.fst (a ≫ g) i ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem fiberMap_snd (g : U ⟶ X) (a : V ⟶ U) :
    fiberMap i g a ≫ pullback.snd g i = pullback.snd (a ≫ g) i :=
  pullback.lift_snd _ _ _

variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance residueDiscrete (n : ℕ) : DiscreteTopology (ZMod n) := ⟨rfl⟩

private def finiteValue {R : CommRingCat.{0}} (g : Spec R ⟶ X)
    (s : C(↥(pullback g i : Scheme.{0}), ℤ_[ℓ])) (n : ℕ) :
    C(↥(pullback g i : Scheme.{0}), ZMod (ℓ ^ n)) :=
  ⟨fun x ↦ PadicInt.toZModPow n (s x), (PadicResidueHomeomorphism.reduction_continuous ℓ n).comp s.continuous⟩

set_option maxHeartbeats 3000000 in
theorem exists_affine_lift {R : CommRingCat.{0}} (g : Spec R ⟶ X)
    (s : C(↥(pullback g i : Scheme.{0}), ℤ_[ℓ])) :
    ∃ (B : CommRingCat.{0}) (a : Spec B ⟶ Spec R), WeaklyEtale a ∧ Surjective a ∧
      ∃ f : C(Spec B, ℤ_[ℓ]), ∀ x : ↥(pullback (a ≫ g) i : Scheme.{0}),
        f (pullback.fst (a ≫ g) i x) = s (fiberMap i g a x) := by
  let p := pullback.fst g i
  have hp : Topology.IsClosedEmbedding (show ↥(pullback g i : Scheme.{0}) → PrimeSpectrum R from p) :=
    p.isClosedEmbedding
  have hLevels (n : ℕ) :=
    FinitePrincipalClosedSectionLift.exists_cover_lift (show ↥(pullback g i : Scheme.{0}) → PrimeSpectrum R from p)
      hp (finiteValue i ℓ g s n)
  choose B hFlat hEt hFn hF using hLevels
  let a := AffineEtaleCommonCountableCover.coverMap B
  let s' := s.comp ⟨fiberMap i g a, (fiberMap i g a).continuous⟩
  have hLift (n : ℕ) :
      ∃ t : C(Spec (CommRingCat.of (AffineEtaleTensorDirectLimit.Tower B)), ZMod (ℓ ^ n)),
        ∀ x : ↥(pullback (a ≫ g) i : Scheme.{0}), t (pullback.fst (a ≫ g) i x) = PadicInt.toZModPow n (s' x) := by
    let q := AffineEtaleCommonCountableCover.factorMap B n
    refine ⟨(hFn n).comp ⟨q, q.continuous⟩, fun x ↦ ?_⟩
    change hFn n (q (pullback.fst (a ≫ g) i x)) = finiteValue i ℓ g s n (fiberMap i g a x)
    apply hF n
    change (q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (B n)))) (pullback.fst (a ≫ g) i x) =
      (fiberMap i g a ≫ pullback.fst g i) x
    rw [show q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (B n))) = a from
      AffineEtaleCommonCountableCover.factor_comp B n, fiberMap_fst]
    rfl
  obtain ⟨f, hf⟩ := PadicContinuousLiftFromResidues.exists_continuous_lift ℓ
    (pullback.fst (a ≫ g) i) s' hLift
  exact ⟨CommRingCat.of (AffineEtaleTensorDirectLimit.Tower B), a,
    AffineEtaleCommonCountableCover.cover_weaklyEtale B hFlat hEt,
    AffineEtaleCommonCountableCover.cover_surjective B hFlat, f, hf⟩

end

end ManuscriptAudit.AffineAdicClosedSectionLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineAdicClosedSectionLift.exists_affine_lift
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
