import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenSectionLoss

/-!
# The sheafified free abelian envelope fails to preserve the terminal object

Paper 4, physical p. 107, Definition 3.12 applies the free abelian
group objectwise and then sheafifies. Lemma 3.13 asserts finite-limit
preservation. The actual terminal set sheaf has an envelope with at
least two homomorphisms into the abelian skyscraper at (2).
-/

namespace ManuscriptAudit.SheafFreeAbelianLimits

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1000000

private abbrev G := AddCommGrpCat.{0}

private def punitTerminal : IsTerminal (PUnit : Type) :=
  IsTerminal.ofUniqueHom (fun _ => TypeCat.ofHom (fun _ => PUnit.unit))
    (fun _ f => by
      apply ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _)

section Site

variable {C : Type} [SmallCategory C] (J : GrothendieckTopology C)

/-- The actual terminal set sheaf. -/
def terminalSetSheaf : Sheaf J (Type) :=
  Sheaf.terminal J punitTerminal

def terminalSetSheaf_isTerminal : IsTerminal (terminalSetSheaf J) :=
  Sheaf.isTerminalTerminal J punitTerminal

variable [HasWeakSheafify J G]

/-- The functor in the manuscript, with free abelian groups taken before
using abelian sheafification. -/
def freeAbelianEnvelope : Sheaf J (Type) ⥤ Sheaf J G :=
  Sheaf.composeAndSheafify J AddCommGrpCat.free

/-- The left-adjoint assertion in Lemma 3.13 holds for the actual functors. -/
def envelopeAdjunction :
    freeAbelianEnvelope J ⊣ sheafCompose J (forget G) :=
  Sheaf.adjunction J AddCommGrpCat.adj

/-- Maps from the envelope of the terminal set sheaf are global sections. -/
def envelopeTerminalHomEquiv {T : C} (hT : IsTerminal T) (F : Sheaf J G) :
    ((freeAbelianEnvelope J).obj (terminalSetSheaf J) ⟶ F) ≃
      F.obj.obj (op T) := by
  change ((presheafToSheaf J G).obj ((terminalSetSheaf J).obj ⋙ AddCommGrpCat.free) ⟶ F) ≃ _
  refine ((sheafificationAdjunction J G).homEquiv _ F).trans ?_
  refine ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv _ F.obj).trans ?_
  change (((CategoryTheory.Functor.const Cᵒᵖ).obj (PUnit : Type)) ⟶
    F.obj ⋙ forget G) ≃ _
  refine ((constantPresheafAdj (Type) hT).homEquiv (PUnit : Type) (F.obj ⋙ forget G)).trans ?_
  exact TypeCat.homEquiv.trans (Equiv.funUnique (PUnit : Type) _)

theorem envelopeTerminal_not_terminal {T : C} (hT : IsTerminal T) (F : Sheaf J G)
    (hF : Nontrivial (F.obj.obj (op T))) :
    ¬ Nonempty (IsTerminal ((freeAbelianEnvelope J).obj (terminalSetSheaf J))) := by
  letI := hF
  rintro ⟨h⟩
  let e := envelopeTerminalHomEquiv J hT F
  obtain ⟨s, t, hst⟩ := exists_pair_ne (F.obj.obj (op T))
  exact hst (e.symm.injective (h.isZero.eq_of_src (e.symm s) (e.symm t)))

theorem envelope_not_preservesFiniteLimits {T : C} (hT : IsTerminal T)
    (F : Sheaf J G) (hF : Nontrivial (F.obj.obj (op T))) :
    ¬ PreservesFiniteLimits (freeAbelianEnvelope J) := by
  intro h
  letI := h
  apply envelopeTerminal_not_terminal J hT F hF
  exact ⟨IsTerminal.isTerminalObj (freeAbelianEnvelope J) (terminalSetSheaf J)
    (terminalSetSheaf_isTerminal J)⟩

end Site

private abbrev SpecZ := TopCat.of (PrimeSpectrum ℤ)
private abbrev zariskiZ := Opens.grothendieckTopology (PrimeSpectrum ℤ)

private def topIsTerminal : IsTerminal (⊤ : Opens SpecZ) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

private theorem skyscraperTop_nontrivial :
    Nontrivial (PrincipalOpenSectionLoss.skyscraperAtTwo.obj.obj (op (⊤ : Opens SpecZ))) := by
  rw [PrincipalOpenSectionLoss.skyscraperAtTwo_globalSections]
  change Nontrivial (ZMod 2)
  letI : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  infer_instance

/-- The statement fails on the standard open-set site of Spec ℤ. -/
theorem paper4_freeAbelianEnvelope_zariski_not_preservesFiniteLimits :
    ¬ PreservesFiniteLimits (freeAbelianEnvelope zariskiZ) :=
  envelope_not_preservesFiniteLimits zariskiZ topIsTerminal
    PrincipalOpenSectionLoss.skyscraperAtTwo skyscraperTop_nontrivial

private abbrev basicOpens := Set.range (PrimeSpectrum.basicOpen (R := ℤ))

/-- The full subcategory of opens that are principal, with genuine inclusion arrows. -/
abbrev PrincipalOpen :=
  InducedCategory (Opens (PrimeSpectrum ℤ)) (Subtype.val : basicOpens → Opens (PrimeSpectrum ℤ))

abbrev principalInclusion : PrincipalOpen ⥤ Opens (PrimeSpectrum ℤ) :=
  inducedFunctor (Subtype.val : basicOpens → Opens (PrimeSpectrum ℤ))

/-- The usual topology inherited by the principal-open basis. -/
abbrev principalSite : GrothendieckTopology PrincipalOpen :=
  principalInclusion.inducedTopology zariskiZ

theorem principalInclusion_coverDense : principalInclusion.IsCoverDense zariskiZ := by
  have hRange :
      Set.range (Subtype.val : basicOpens → Opens (PrimeSpectrum ℤ)) = basicOpens := by
    ext U
    constructor
    · rintro ⟨V, rfl⟩
      exact V.property
    · intro hU
      exact ⟨⟨U, hU⟩, rfl⟩
  exact TopCat.Opens.coverDense_inducedFunctor (X := SpecZ)
    (B := (Subtype.val : basicOpens → Opens (PrimeSpectrum ℤ))) (by
      rw [hRange]
      exact PrimeSpectrum.isBasis_basic_opens)

private def principalTop : PrincipalOpen :=
  (⟨⊤, ⟨1, by simp⟩⟩ : basicOpens)

private def principalTop_isTerminal : IsTerminal principalTop := by
  refine IsTerminal.ofUniqueHom
    (fun U => InducedCategory.homMk (homOfLE (show principalInclusion.obj U ≤ ⊤ from le_top))) ?_
  intro U f
  apply principalInclusion.map_injective
  exact Subsingleton.elim _ _

private def basisSkyscraper : Sheaf principalSite G :=
  (principalInclusion.sheafPushforwardContinuous G principalSite zariskiZ).obj
    PrincipalOpenSectionLoss.skyscraperAtTwo

/-- The actual free envelope on the principal basis is left adjoint to
forgetting the abelian group structure. -/
def paper4_freeAbelianEnvelope_principalAdjunction :
    freeAbelianEnvelope principalSite ⊣ sheafCompose principalSite (forget G) :=
  envelopeAdjunction principalSite

/-- The same failure on the actual principal-open basis with its induced topology. -/
theorem paper4_freeAbelianEnvelope_principal_not_preservesFiniteLimits :
    ¬ PreservesFiniteLimits (freeAbelianEnvelope principalSite) := by
  apply envelope_not_preservesFiniteLimits principalSite principalTop_isTerminal basisSkyscraper
  change Nontrivial (PrincipalOpenSectionLoss.skyscraperAtTwo.obj.obj (op (⊤ : Opens SpecZ)))
  exact skyscraperTop_nontrivial

end

end ManuscriptAudit.SheafFreeAbelianLimits

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``ManuscriptAudit.SheafFreeAbelianLimits.terminalSetSheaf_isTerminal,
    ``ManuscriptAudit.SheafFreeAbelianLimits.envelopeAdjunction,
    ``ManuscriptAudit.SheafFreeAbelianLimits.envelopeTerminalHomEquiv,
    ``ManuscriptAudit.SheafFreeAbelianLimits.envelopeTerminal_not_terminal,
    ``ManuscriptAudit.SheafFreeAbelianLimits.paper4_freeAbelianEnvelope_zariski_not_preservesFiniteLimits,
    ``ManuscriptAudit.SheafFreeAbelianLimits.principalInclusion_coverDense,
    ``ManuscriptAudit.SheafFreeAbelianLimits.paper4_freeAbelianEnvelope_principalAdjunction,
    ``ManuscriptAudit.SheafFreeAbelianLimits.paper4_freeAbelianEnvelope_principal_not_preservesFiniteLimits] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
