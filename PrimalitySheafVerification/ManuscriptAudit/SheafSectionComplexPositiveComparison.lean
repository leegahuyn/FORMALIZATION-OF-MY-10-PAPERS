import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafPositiveResolutionNaturality
import PrimalitySheafVerification.ManuscriptAudit.SheafSectionResolutionComplex

/-! Natural positive cohomology comparison for the integer-indexed global-section complex. -/

namespace ManuscriptAudit.SheafSectionComplexPositiveComparison

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SheafSectionResolutionComplex (sections resolution resolutionMap sectionComplex sectionComplexMap)
open SheafPositiveResolutionCohomology (sectionsShort positiveEquiv)
open SheafPositiveResolutionNaturality (shortMap positiveEquiv_natural)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{0}
private abbrev c := ComplexShape.up ℤ

variable [HasSheafify J A] [EnoughInjectives (Sheaf J A)] [HasExt.{0} (Sheaf J A)]
variable {T : C} (hT : IsTerminal T)
variable {F G : Sheaf J A}

private abbrev adjacent (n : ℕ) := shortComplexFunctor' A c (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)

private def termIso (F : Sheaf J A) (m : ℕ) :
    (sectionComplex J T F).X (m : ℤ) ≅ (sections J T).obj ((resolution J F).cocomplex.X m) :=
  (sections J T).mapIso ((resolution J F).cochainComplexXIso (m : ℤ) m rfl)

private theorem termIso_d (F : Sheaf J A) (a b : ℕ) :
    (termIso J (T := T) F a).hom ≫ (sections J T).map ((resolution J F).cocomplex.d a b) =
      (sectionComplex J T F).d (a : ℤ) (b : ℤ) ≫ (termIso J (T := T) F b).hom := by
  let R := resolution J F
  change (sections J T).map (R.cochainComplexXIso _ a rfl).hom ≫
    (sections J T).map (R.cocomplex.d a b) =
    (sections J T).map (R.cochainComplex.d (a : ℤ) (b : ℤ)) ≫
      (sections J T).map (R.cochainComplexXIso _ b rfl).hom
  rw [← Functor.map_comp, ← Functor.map_comp, R.cochainComplex_d _ _ a b rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual adjacent terms of the integer-indexed model are those of the evaluated resolution. -/
def shortIso (F : Sheaf J A) (n : ℕ) :
    (adjacent n).obj (sectionComplex J T F) ≅ sectionsShort J (resolution J F) n (T := T) :=
  ShortComplex.isoMk (termIso J F n) (termIso J F (n + 1)) (termIso J F (n + 2))
    (termIso_d J F n (n + 1)) (termIso_d J F (n + 1) (n + 2))

private theorem termIso_natural (f : F ⟶ G) (m : ℕ) :
    (sectionComplexMap J T f).f (m : ℤ) ≫ (termIso J G m (T := T)).hom =
      (termIso J F m (T := T)).hom ≫ (sections J T).map ((resolutionMap J f).hom.f m) := by
  let R := resolution J F
  let P := resolution J G
  let φ := resolutionMap J f
  change (sections J T).map (φ.hom'.f (m : ℤ)) ≫ (sections J T).map (P.cochainComplexXIso _ m rfl).hom =
    (sections J T).map (R.cochainComplexXIso _ m rfl).hom ≫ (sections J T).map (φ.hom.f m)
  rw [← Functor.map_comp, ← Functor.map_comp, φ.hom'_f (m : ℤ) m rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem shortIso_natural (f : F ⟶ G) (n : ℕ) :
    (adjacent n).map (sectionComplexMap J T f) ≫ (shortIso J (T := T) G n).hom =
      (shortIso J (T := T) F n).hom ≫ shortMap J (resolutionMap J f) n (T := T) := by
  ext : 1
  · exact termIso_natural J f n
  · exact termIso_natural J f (n + 1)
  · exact termIso_natural J f (n + 2)

private def canonicalShortIso (n : ℕ) :
    shortComplexFunctor A c (((n + 1 : ℕ) : ℤ)) ≅ adjacent n :=
  natIsoSc' A c (n : ℤ) ((n + 1 : ℕ) : ℤ) ((n + 2 : ℕ) : ℤ)
    (by rw [CochainComplex.prev]; omega) (by rw [CochainComplex.next]; omega)

private def combinedIso (F : Sheaf J A) (n : ℕ) :
    (sectionComplex J T F).sc (((n + 1 : ℕ) : ℤ)) ≅ sectionsShort J (resolution J F) n (T := T) :=
  (canonicalShortIso n).app (sectionComplex J T F) ≪≫ shortIso J F n

private theorem combinedIso_natural (f : F ⟶ G) (n : ℕ) :
    (shortComplexFunctor A c (((n + 1 : ℕ) : ℤ))).map (sectionComplexMap J T f) ≫
      (combinedIso J (T := T) G n).hom =
    (combinedIso J (T := T) F n).hom ≫ shortMap J (resolutionMap J f) n (T := T) := by
  let t := sectionComplexMap J T f
  let e := canonicalShortIso n
  have h :
      (shortComplexFunctor A c (((n + 1 : ℕ) : ℤ))).map t ≫ (e.app (sectionComplex J T G)).hom =
        (e.app (sectionComplex J T F)).hom ≫ (adjacent n).map t :=
    e.hom.naturality t
  change (shortComplexFunctor A c (((n + 1 : ℕ) : ℤ))).map t ≫
      ((e.app (sectionComplex J T G)).hom ≫ (shortIso J G n).hom) =
    ((e.app (sectionComplex J T F)).hom ≫ (shortIso J F n).hom) ≫
      shortMap J (resolutionMap J f) n (T := T)
  rw [← Category.assoc, h, Category.assoc, shortIso_natural J f n, ← Category.assoc]

/-- The chosen actual section complex computes native sheaf cohomology in every positive degree. -/
def cohomologyEquiv (F : Sheaf J A) (n : ℕ) :
    (sectionComplex J T F).homology (((n + 1 : ℕ) : ℤ)) ≃+ Sheaf.H F (n + 1) :=
  (ShortComplex.homologyMapIso (combinedIso J (T := T) F n)).addCommGroupIsoToAddEquiv.trans
    (positiveEquiv J hT (resolution J F) n)

/-- The actual chain map of the lifted coefficient arrow induces the native cohomology map. -/
theorem cohomologyEquiv_natural (f : F ⟶ G) (n : ℕ)
    (x : (sectionComplex J T F).homology (((n + 1 : ℕ) : ℤ))) :
    cohomologyEquiv J hT G n (homologyMap (sectionComplexMap J T f) (↑(n + 1) : ℤ) x) =
      Sheaf.H.map f (n + 1) (cohomologyEquiv J hT F n x) := by
  let a := (combinedIso J (T := T) F n).hom
  let b := (combinedIso J (T := T) G n).hom
  have h := congrArg (fun u ↦ ShortComplex.homologyMap u) (combinedIso_natural J f n (T := T))
  simp only [ShortComplex.homologyMap_comp] at h
  have hx :
      ShortComplex.homologyMap b (homologyMap (sectionComplexMap J T f) (↑(n + 1) : ℤ) x) =
        ShortComplex.homologyMap (shortMap J (resolutionMap J f) n (T := T))
          (ShortComplex.homologyMap a x) :=
    CategoryTheory.congr_fun h x
  change positiveEquiv J hT (resolution J G) n
      (ShortComplex.homologyMap b (homologyMap (sectionComplexMap J T f) (↑(n + 1) : ℤ) x)) =
    Sheaf.H.map f (n + 1) (positiveEquiv J hT (resolution J F) n (ShortComplex.homologyMap a x))
  rw [hx]
  exact positiveEquiv_natural J hT (resolutionMap J f) n (ShortComplex.homologyMap a x)

end
end ManuscriptAudit.SheafSectionComplexPositiveComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SheafSectionComplexPositiveComparison.shortIso,
      ``ManuscriptAudit.SheafSectionComplexPositiveComparison.cohomologyEquiv,
      ``ManuscriptAudit.SheafSectionComplexPositiveComparison.cohomologyEquiv_natural] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
