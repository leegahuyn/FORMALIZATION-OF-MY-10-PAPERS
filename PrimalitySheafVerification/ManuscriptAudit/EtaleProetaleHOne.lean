import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleInverseImage
import PrimalitySheafVerification.ManuscriptAudit.ExtOneAdjunctionNaturality

/-! The native degree-one comparison from the cohomology of the actual
étale direct image to pro-étale cohomology is injective. -/

namespace ManuscriptAudit.EtaleProetaleHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open EtaleProetaleInverseImage

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{u})

private abbrev A := AddCommGrpCat.{u + 1}

private abbrev C := Sheaf X.smallEtaleTopology A.{u}

private abbrev D := Sheaf (Scheme.ProEt.topology X) A.{u}

private theorem etaleGrothendieck : IsGrothendieckAbelian.{u + 1} (C X) := by
  letI : EssentiallySmall.{u + 1} X.Etale :=
    EssentiallySmall.mk' (AsSmall.equiv : X.Etale ≌ AsSmall.{0} X.Etale)
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology A.{u}

attribute [local instance] etaleGrothendieck

local instance etaleExt : HasExt.{u + 1} (C X) := IsGrothendieckAbelian.hasExt (C X)

local instance etaleInjectives : EnoughInjectives (C X) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1} (C := C X)

local instance inverseImage_additive : (inverseImage X).Additive :=
  Functor.additive_of_preserves_binary_products (inverseImage X)

private abbrev etaleZ := (constantSheaf X.smallEtaleTopology A.{u}).obj
  (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private abbrev proEtaleZ := (constantSheaf (Scheme.ProEt.topology X) A.{u}).obj
  (AddCommGrpCat.of (ULift.{u + 1} ℤ))

private def constantIso : (inverseImage X).obj (etaleZ X) ≅ proEtaleZ X :=
  (constantInverseImageIso X).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The native degree-one map induced by étale inverse image and the counit. -/
def comparison (F : D X) : Sheaf.H ((directImage X).obj F) 1 →+ Sheaf.H F 1 :=
  ((Ext.mk₀ (constantIso X).inv).precomp F (zero_add 1)).comp
    (ExtOneAdjunction.map (adjunction X) (etaleZ X) F)

/-- Actual direct-image degree-one cohomology embeds into pro-étale degree-one cohomology. -/
theorem comparison_injective (F : D X) : Function.Injective (comparison X F) := by
  have h : Function.LeftInverse
      ((Ext.mk₀ (constantIso X).hom).precomp F (zero_add 1))
      ((Ext.mk₀ (constantIso X).inv).precomp F (zero_add 1)) := by
    intro e
    change (Ext.mk₀ (constantIso X).hom).comp
      ((Ext.mk₀ (constantIso X).inv).comp e (zero_add 1)) (zero_add 1) = e
    rw [Ext.mk₀_comp_mk₀_assoc, (constantIso X).hom_inv_id, Ext.mk₀_id_comp]
  intro a b hab
  apply ExtOneAdjunction.map_injective (adjunction X) (etaleZ X) F
  apply h.injective
  exact hab

/-- The degree-one site comparison is natural in the coefficient sheaf. -/
theorem comparison_naturality {F G : D X} (f : F ⟶ G)
    (x : Sheaf.H ((directImage X).obj F) 1) :
    comparison X G (Sheaf.H.map ((directImage X).map f) 1 x) =
      Sheaf.H.map f 1 (comparison X F x) := by
  change (Ext.mk₀ (constantIso X).inv).comp
      (ExtOneAdjunction.map (adjunction X) (etaleZ X) G
        (x.comp (Ext.mk₀ ((directImage X).map f)) (add_zero 1))) (zero_add 1) =
    ((Ext.mk₀ (constantIso X).inv).comp
      (ExtOneAdjunction.map (adjunction X) (etaleZ X) F x) (zero_add 1)).comp
        (Ext.mk₀ f) (add_zero 1)
  rw [ExtOneAdjunctionNaturality.map_postcomp, Ext.comp_assoc_of_third_deg_zero]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The specialization to the actual coefficient sheaf defining native adic cohomology. -/
def adicComparison :
    Sheaf.H ((directImage X).obj
      ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ))) 1 →+
      X.EllAdicCohomology ℓ 1 :=
  comparison X _

theorem adicComparison_injective : Function.Injective (adicComparison X ℓ) :=
  comparison_injective X _

end
end ManuscriptAudit.EtaleProetaleHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleHOne.comparison_injective,
      ``ManuscriptAudit.EtaleProetaleHOne.adicComparison_injective,
      ``ManuscriptAudit.EtaleProetaleHOne.comparison_naturality] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
