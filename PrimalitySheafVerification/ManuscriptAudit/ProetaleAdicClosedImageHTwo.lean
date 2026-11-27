import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedImageCokernel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDirectImageHOne

/-! The actual closed direct image from an algebraically closed point
has zero native H² for integral adic coefficients. -/

namespace ManuscriptAudit.ProetaleAdicClosedImageHTwo

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleBaseChange (directImage)
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open ProetaleInverseImage (adjunction)
open ProetaleAdicClosedImageCokernel (map_cokernel_epi)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
variable (i : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion i]
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev Z := Spec (CommRingCat.of K)
private abbrev F := functions ℤ_[ℓ] (Z (K := K))
private abbrev G := directImage i A
private abbrev C (T : Scheme.{0}) := Sheaf (Scheme.ProEt.topology T) A
private abbrev integers (T : Scheme.{0}) :=
  (constantSheaf (Scheme.ProEt.topology T) A).obj (AddCommGrpCat.of (ULift.{1} ℤ))

local instance (T : Scheme.{0}) : EnoughInjectives (C T) :=
  IsGrothendieckAbelian.enoughInjectives.{1} (C := C T)

set_option maxHeartbeats 2300000 in
/-- Actual compact adic coefficients at the closed point are acyclic in
degree two after their native closed direct image. -/
theorem HTwo_subsingleton : Subsingleton (Sheaf.H (functionsOver ℤ_[ℓ] i) 2) := by
  let I := Injective.under (F (K := K) ℓ)
  let m : F (K := K) ℓ ⟶ I := Injective.ι _
  let q := cokernel.π m
  let S := ShortComplex.mk m q (cokernel.condition m)
  letI : (G i).IsRightAdjoint := (adjunction i).isRightAdjoint
  letI : (G i).Additive := (G i).additive_of_preserves_binary_products
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel m)
  have hSe : (S.map (G i)).Exact := hS.map_of_mono_of_preservesKernel (G i)
    (inferInstanceAs (Mono m)) (inferInstanceAs (PreservesLimit (parallelPair q 0) (G i)))
  have hShort : (S.map (G i)).ShortExact :=
    ShortComplex.ShortExact.mk' hSe
      (inferInstanceAs (Mono ((G i).map m))) (map_cokernel_epi i ℓ m)
  letI : Injective ((G i).obj I) := Injective.injective_of_adjoint (adjunction i) I
  letI : Subsingleton (Sheaf.H ((G i).obj I) 2) :=
    Ext.subsingleton_of_injective (integers X) ((G i).obj I) 1
  letI : Subsingleton (Sheaf.H (cokernel m) 1) :=
    ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton K (cokernel m) 0
  letI : Subsingleton (Sheaf.H ((G i).obj (cokernel m)) 1) :=
    ProetaleDirectImageHOne.directImage_HOne_subsingleton i (cokernel m)
  apply subsingleton_of_forall_eq 0
  intro x
  let W := S.map (G i)
  have hx : x.comp (Ext.mk₀ W.f) (add_zero 2) = 0 := Subsingleton.elim _ _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (integers X) hShort x hx
    (show 1 + 1 = 2 by rfl)
  have hy₀ : y = 0 := Subsingleton.elim _ _
  rw [hy₀, Ext.zero_comp] at hy
  exact hy.symm

end
end ManuscriptAudit.ProetaleAdicClosedImageHTwo

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleAdicClosedImageHTwo.HTwo_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
