import Lean.Util.CollectAxioms
import Mathlib.RingTheory.TensorProduct.Basic
import PrimalitySheafVerification.ManuscriptAudit.MilnorCoordinatePatch

/-!
# Normalization base change of a coordinate patch

The first coordinate of the patch extends to a linear map over the
normalization. This map commutes with the change of coordinates that
takes a liftable transition matrix to the identity.
-/

namespace ManuscriptAudit.MilnorNormalizationMap

open Matrix MilnorCoordinatePatch
open scoped TensorProduct

universe u v

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable {n : Type v} [Fintype n]
variable (q : B →ₐ[A] D) (s : C →ₐ[A] D)

/-- The first-coordinate projection before extending scalars. -/
def firstProjection (U : Matrix n n D) : patch q s U →ₗ[A] (n → B) :=
  (LinearMap.fst A (n → B) (n → C)).comp (patch q s U).subtype

/-- The canonical map after extending scalars to the normalization. -/
def normalizationMap (U : Matrix n n D) : B ⊗[A] patch q s U →ₗ[B] (n → B) :=
  (firstProjection q s U).liftBaseChange B

@[simp]
theorem normalizationMap_tmul (U : Matrix n n D) (b : B) (x : patch q s U) :
    normalizationMap q s U (b ⊗ₜ[A] x) = b • x.val.1 :=
  rfl

variable [DecidableEq n]

/-- The coordinate change over the normalization acts by the inverse lifted matrix. -/
def inverseLiftOnCoordinates (V : GL n B) : (n → B) ≃ₗ[B] (n → B) :=
  Matrix.toLin'OfInv V.val_inv V.inv_val

@[simp]
theorem inverseLiftOnCoordinates_apply (V : GL n B) (x : n → B) :
    inverseLiftOnCoordinates V x = V.inv *ᵥ x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Extension of the first-coordinate projection commutes with the lifted coordinate change. -/
theorem normalizationMap_equivOfLift (U : GL n D) (V : GL n B)
    (hV : GeneralLinearGroup.map q.toRingHom V = U) :
    (normalizationMap q s (1 : Matrix n n D)).comp
      ((equivOfLift q s U V hV).baseChange A B _ _).toLinearMap =
      (inverseLiftOnCoordinates V).toLinearMap.comp (normalizationMap q s U.val) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  change b • (equivOfLift q s U V hV x).val.1 =
    inverseLiftOnCoordinates V (b • x.val.1)
  have h := congrArg Prod.fst (equivOfLift_apply_coe q s U V hV x)
  change (equivOfLift q s U V hV x).val.1 = V.inv *ᵥ x.val.1 at h
  rw [h, map_smul, inverseLiftOnCoordinates_apply]

/-- Bijectivity for identity gluing implies bijectivity for a liftable transition matrix. -/
theorem normalizationMap_bijective_of_lift (U : GL n D) (V : GL n B)
    (hV : GeneralLinearGroup.map q.toRingHom V = U)
    (hIdentity : Function.Bijective (normalizationMap q s (1 : Matrix n n D))) :
    Function.Bijective (normalizationMap q s U.val) := by
  let e := (equivOfLift q s U V hV).baseChange A B _ _
  let g := inverseLiftOnCoordinates V
  have h : (normalizationMap q s (1 : Matrix n n D)) ∘ e =
      g ∘ normalizationMap q s U.val :=
    funext fun x => DFunLike.congr_fun (normalizationMap_equivOfLift q s U V hV) x
  have hcomp : Function.Bijective (g ∘ normalizationMap q s U.val) := by
    rw [← h]
    exact hIdentity.comp e.bijective
  constructor
  · intro x y hxy
    exact hcomp.injective (congrArg g hxy)
  · intro y
    obtain ⟨x, hx⟩ := hcomp.surjective (g y)
    exact ⟨x, g.injective hx⟩

end ManuscriptAudit.MilnorNormalizationMap

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MilnorNormalizationMap.normalizationMap_tmul,
      ``ManuscriptAudit.MilnorNormalizationMap.normalizationMap_equivOfLift,
      ``ManuscriptAudit.MilnorNormalizationMap.normalizationMap_bijective_of_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
