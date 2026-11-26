import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverHOne

/-!
# The nodal trace sequence on the native full small étale site

The affine basis restriction is fully faithful. Taking preimages of
the actual affine diagonal and trace retains the intended full
continuous-function sheaves and their values on affine objects.
-/

namespace ManuscriptAudit.NodalSwapCoverFullTrace

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalConductor NodalSwapCover NodalSwapCoverSheafTrace
open AffineEtaleTensorPresentation

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev A : Type := ↥(coordinates K)
private abbrev E : Type := Cover K
private abbrev R := CommRingCat.of (A K)
private abbrev X := Spec (R K)
private abbrev Y := Spec (CommRingCat.of (E K))
private abbrev cover := affineMap (A K) (E K)
private abbrev J := (X K).smallEtaleTopology
private abbrev cyclic := AddCommGrpCat.of (ZMod 2)

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

abbrev fullBaseFunctions : Sheaf (J K) AddCommGrpCat.{0} :=
  EtaleContinuousMapSheaf.continuousMapSheaf (X K) cyclic

abbrev fullCoverFunctions : Sheaf (J K) AddCommGrpCat.{0} :=
  (SmallEtaleBaseChange.directImage (cover K) AddCommGrpCat.{0}).obj
    (EtaleContinuousMapSheaf.continuousMapSheaf (Y K) cyclic)

abbrev constantIso :
    (constantSheaf (J K) AddCommGrpCat.{0}).obj cyclic ≅ fullBaseFunctions K :=
  EtaleContinuousMapSheaf.constantSheafContinuousMapIso (X K) cyclic

private abbrev restrict :=
  (Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}).inverse

local instance restrictAdditive : (restrict K).Additive :=
  (restrict K).additive_of_preserves_binary_products

abbrev chart (U : (X K).AffineEtale) : (X K).Etale :=
  (Scheme.AffineEtale.Spec (X K)).obj U

def fullDiagonal : fullBaseFunctions K ⟶ fullCoverFunctions K :=
  (restrict K).preimage (diagonal K cyclic)

variable (h2 : (2 : K) ≠ 0)

def fullTrace : fullCoverFunctions K ⟶ fullBaseFunctions K :=
  (restrict K).preimage (trace K cyclic h2)

private theorem restrict_diagonal :
    (restrict K).map (fullDiagonal K) = diagonal K cyclic :=
  (restrict K).map_preimage _

private theorem restrict_trace :
    (restrict K).map (fullTrace K h2) = trace K cyclic h2 :=
  (restrict K).map_preimage _

private theorem full_zero : fullDiagonal K ≫ fullTrace K h2 = 0 := by
  apply (restrict K).map_injective
  rw [Functor.map_comp, Functor.map_zero, restrict_diagonal, restrict_trace]
  exact (NodalSwapCoverHOne.shortComplex K h2).zero

def shortComplex : ShortComplex (Sheaf (J K) AddCommGrpCat.{0}) :=
  ShortComplex.mk (fullDiagonal K) (fullTrace K h2) (full_zero K h2)

private def restrictIso :
    (shortComplex K h2).map (restrict K) ≅ NodalSwapCoverHOne.shortComplex K h2 :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using (restrict_diagonal K).symm)
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using (restrict_trace K h2).symm)

set_option maxHeartbeats 1400000 in
theorem shortComplex_shortExact : (shortComplex K h2).ShortExact := by
  have h := (ShortComplex.shortExact_iff_of_iso (restrictIso K h2)).mpr
    (NodalSwapCoverHOne.shortComplex_shortExact K h2)
  apply ShortComplex.ShortExact.mk'
  · exact (ShortComplex.exact_map_iff_of_faithful (shortComplex K h2) (restrict K)).mp h.exact
  · exact (restrict K).mono_of_mono_map h.mono_f
  · exact (restrict K).epi_of_epi_map h.epi_g

set_option maxHeartbeats 1400000 in
theorem fullTrace_app (U : (X K).AffineEtale)
    (s : (fullCoverFunctions K).obj.obj (op (chart K U))) :
    (fullTrace K h2).hom.app (op (chart K U)) s =
      (trace K cyclic h2).hom.app (op U) s :=
  ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : coverFunctions K cyclic ⟶ baseFunctions K cyclic => f.hom)
      (restrict_trace K h2)) (op U)) s

private abbrev term := KummerAffineCohomology.affineTerminal (R K)

def oneAt (U : (X K).Etale) : (fullBaseFunctions K).obj.obj (op U) :=
  ContinuousMap.const U.left (1 : ZMod 2)

theorem oneAt_restrict {U V : (X K).Etale} (f : U ⟶ V) :
    (fullBaseFunctions K).obj.map f.op (oneAt K V) = oneAt K U := by
  apply ContinuousMap.ext
  intro p
  rfl

abbrev terminalOne : (fullBaseFunctions K).obj.obj (op (chart K (term K))) :=
  oneAt K (chart K (term K))

theorem terminal_one_unlifted :
    ¬ ∃ s : (fullCoverFunctions K).obj.obj (op (chart K (term K))),
      (fullTrace K h2).hom.app (op (chart K (term K))) s = terminalOne K := by
  rintro ⟨s, hs⟩
  exact (NodalSwapCoverHOne.terminal_one_unlifted K h2)
    ⟨s, (fullTrace_app K h2 (term K) s).symm.trans hs⟩

attribute [local instance] objectAlgebra

set_option maxHeartbeats 1400000 in
theorem fullTrace_app_surjective_of_section (U : (X K).AffineEtale)
    (g : E K →ₐ[A K] objectRing (A K) U) :
    Function.Surjective ((fullTrace K h2).hom.app (op (chart K U))) := by
  intro t
  obtain ⟨s, hs⟩ := trace_app_surjective_of_affine_trace_surjective K cyclic h2 U
    (NodalSwapCoverLocalTrace.affineTrace_surjective_of_section K (objectRing (A K) U) cyclic h2 g) t
  exact ⟨s, (fullTrace_app K h2 U s).trans hs⟩


theorem one_has_lift_of_section (U : (X K).AffineEtale)
    (g : E K →ₐ[A K] objectRing (A K) U) :
    ∃ s : (fullCoverFunctions K).obj.obj (op (chart K U)),
      (fullTrace K h2).hom.app (op (chart K U)) s = oneAt K (chart K U) :=
  fullTrace_app_surjective_of_section K h2 U g (oneAt K (chart K U))

end

end ManuscriptAudit.NodalSwapCoverFullTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.NodalSwapCoverFullTrace.shortComplex_shortExact,
      ``ManuscriptAudit.NodalSwapCoverFullTrace.fullTrace_app,
      ``ManuscriptAudit.NodalSwapCoverFullTrace.terminal_one_unlifted,
      ``ManuscriptAudit.NodalSwapCoverFullTrace.fullTrace_app_surjective_of_section,
      ``ManuscriptAudit.NodalSwapCoverFullTrace.oneAt_restrict,
      ``ManuscriptAudit.NodalSwapCoverFullTrace.one_has_lift_of_section] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
