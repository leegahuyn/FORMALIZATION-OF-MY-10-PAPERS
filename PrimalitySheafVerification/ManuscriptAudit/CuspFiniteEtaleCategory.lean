import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Smooth.Flat
import PrimalitySheafVerification.ManuscriptAudit.CuspNormalizationHom

/-!
# Cusp normalization on finite étale categories

The native scalar-extension functor is fully faithful. An algebra equivalence
recovering each normalization algebra from a finite étale cusp algebra then
makes this same functor an equivalence.
-/

namespace ManuscriptAudit.CuspFiniteEtaleCategory

open CategoryTheory CommAlgCat Polynomial
open scoped TensorProduct

noncomputable section

universe u

variable (K : Type u) [Field K]

private abbrev A := CuspPunctured.CuspSubalgebra K
private abbrev B := Polynomial K

abbrev normalizationBaseChange : FiniteEtale.{u} (A K) ⥤ FiniteEtale.{u} (B K) :=
  FiniteEtale.baseChange (A K) (B K)

set_option backward.isDefEq.respectTransparency false in
theorem normalizationBaseChange_map_bijective (X Y : FiniteEtale.{u} (A K)) :
    Function.Bijective ((normalizationBaseChange K).map : (X ⟶ Y) → _) := by
  letI : Algebra.Etale (A K) X.obj := X.property.right
  letI : Algebra.Etale (A K) Y.obj := Y.property.right
  have h := CuspNormalizationHom.baseChange_bijective K X.obj Y.obj
  constructor
  · intro f g hfg
    apply InducedCategory.hom_ext
    apply CommAlgCat.hom_ext
    exact h.injective (congrArg (fun z => z.hom.hom) hfg)
  · intro f
    obtain ⟨g, hg⟩ := h.surjective f.hom.hom
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom g), ?_⟩
    exact InducedCategory.hom_ext (CommAlgCat.hom_ext hg)

def normalizationBaseChangeFullyFaithful : (normalizationBaseChange K).FullyFaithful :=
  Classical.choice <|
    (Functor.FullyFaithful.nonempty_iff_map_bijective (normalizationBaseChange K)).mpr
      (normalizationBaseChange_map_bijective K)

/-- Objectwise recovery of finite étale normalization algebras by base change. -/
def HasFiniteEtaleDescent : Prop :=
  ∀ E : FiniteEtale.{u} (B K), ∃ T : FiniteEtale.{u} (A K),
    Nonempty ((B K ⊗[A K] T.obj) ≃ₐ[B K] E.obj)

set_option backward.isDefEq.respectTransparency false in
theorem normalizationBaseChange_essSurj (h : HasFiniteEtaleDescent K) :
    (normalizationBaseChange K).EssSurj where
  mem_essImage E := by
    obtain ⟨T, ⟨e⟩⟩ := h E
    exact ⟨T, ⟨FiniteEtale.isoMk e⟩⟩

theorem normalizationBaseChange_isEquivalence (h : HasFiniteEtaleDescent K) :
    (normalizationBaseChange K).IsEquivalence where
  faithful := (normalizationBaseChangeFullyFaithful K).faithful
  full := (normalizationBaseChangeFullyFaithful K).full
  essSurj := normalizationBaseChange_essSurj K h

/-- An equivalence with actual normalization base change as its forward functor. -/
def finiteEtaleEquivalence (h : HasFiniteEtaleDescent K) :
    FiniteEtale.{u} (A K) ≌ FiniteEtale.{u} (B K) :=
  letI := normalizationBaseChange_isEquivalence K h
  (normalizationBaseChange K).asEquivalence

end

end ManuscriptAudit.CuspFiniteEtaleCategory

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspFiniteEtaleCategory.normalizationBaseChange_map_bijective,
      ``ManuscriptAudit.CuspFiniteEtaleCategory.normalizationBaseChangeFullyFaithful,
      ``ManuscriptAudit.CuspFiniteEtaleCategory.normalizationBaseChange_essSurj,
      ``ManuscriptAudit.CuspFiniteEtaleCategory.normalizationBaseChange_isEquivalence,
      ``ManuscriptAudit.CuspFiniteEtaleCategory.finiteEtaleEquivalence] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
