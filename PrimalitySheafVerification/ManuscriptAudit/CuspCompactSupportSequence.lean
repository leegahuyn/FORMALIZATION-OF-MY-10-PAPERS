import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspOpenOriginSequence
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero

/-!
# Compact-support localization in the proper cusp compactification

Use the checked projective closure of the actual affine cusp.
The relative compactly supported groups below are computed by extension
by zero along the displayed open immersions into this proper scheme.
The short exact sequence compares the cusp, its puncture, and its origin.
-/

namespace ManuscriptAudit.CuspCompactSupportSequence

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification SmallEtaleGeometricBaseChange

universe u

noncomputable section

variable (K : Type u) [Field K] [IsSepClosed K]

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private theorem originToBase :
    (cuspOrigin K ≫ affineOpen K) ≫ projectiveCuspToBase K =
      𝟙 (Spec (CommRingCat.of K)) := by
  have hRing : CommRingCat.ofHom (algebraMap K (CuspPunctured.CuspSubalgebra K)) ≫
      CuspConductorSquare.origin K = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Polynomial.constantCoeff : Polynomial K →+* K) (Polynomial.C a) = a
    simp
  rw [Category.assoc, affineOpen_toBase, cuspOrigin, ← Spec.map_comp, hRing, Spec.map_id]

/-- The extension-by-zero localization sequence on the actual proper closure. -/
def compactSupportSequence (M : AddCommGrpCat.{u}) :
    ShortComplex (Sheaf (projectiveCusp K).smallEtaleTopology AddCommGrpCat.{u}) :=
  letI := affineOpen_isOpenImmersion K
  cuspOpenOriginSequence K (affineOpen K) (projectiveCuspToBase K) (originToBase K) M

/-- Both open extensions in the compact-support comparison lie in a proper ambient scheme. -/
theorem compactSupportSequence_shortExact (M : AddCommGrpCat.{u}) :
    IsProper (projectiveCuspToBase K) ∧ (compactSupportSequence K M).ShortExact := by
  letI := affineOpen_isOpenImmersion K
  exact ⟨projectiveCusp_isProper K,
    cuspOpenOriginSequence_shortExact K (affineOpen K) (projectiveCuspToBase K) (originToBase K) M⟩

/-- Compactly supported groups of the puncture using this compactification. -/
abbrev punctureHc (M : AddCommGrpCat.{u}) (n : ℕ) :=
  Sheaf.H (compactSupportSequence K M).X₁ n

/-- Compactly supported groups of the affine cusp using this compactification. -/
abbrev cuspHc (M : AddCommGrpCat.{u}) (n : ℕ) :=
  Sheaf.H (compactSupportSequence K M).X₂ n

end

end ManuscriptAudit.CuspCompactSupportSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspCompactSupportSequence.compactSupportSequence_shortExact
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
