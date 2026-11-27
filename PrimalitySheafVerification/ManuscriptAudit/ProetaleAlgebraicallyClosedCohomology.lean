import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.EpiMono
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFieldTerminalCovers

/-! Pro-étale cohomology over an algebraically closed field vanishes in
every positive degree because the terminal object has split covers. -/

namespace ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite
open ProetaleFieldTerminalCovers (base terminalObject terminalObject_isTerminal covering_eq_top)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K : Type u) [Field K] [IsAlgClosed K]

private abbrev A := AddCommGrpCat.{u + 1}

private abbrev D := Sheaf (Scheme.ProEt.topology (base K)) A.{u}

/-- Epimorphisms of actual pro-étale abelian sheaves of an algebraically
closed field are surjective on global sections. -/
theorem globalSections_surjective {F G : D K} (f : F ⟶ G) [Epi f] :
    Function.Surjective (f.hom.app (op (terminalObject K))) := by
  let J := Scheme.ProEt.topology (base K)
  let T := terminalObject K
  letI : Presheaf.IsLocallySurjective J f.hom :=
    (Sheaf.isLocallySurjective_iff_epi' f).mpr inferInstance
  intro z
  let R : Sieve T := Presheaf.imageSieve f.hom z
  have hR : R ∈ J T := Presheaf.imageSieve_mem J f.hom z
  have hId : R (𝟙 T) := (Sieve.id_mem_iff_eq_top R).mpr (covering_eq_top K R hR)
  obtain ⟨x, hx⟩ := hId
  exact ⟨x, by simpa using hx⟩

private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology (base K)) A.{u}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- The actual constant integer sheaf on this pro-étale site is projective. -/
instance constantIntegers_projective : Projective (integers K) where
  factors {F G} g f hf := by
    letI : Epi f := hf
    let T := terminalObject_isTerminal K
    let z : Sheaf.H G 0 := Ext.mk₀ g
    obtain ⟨x, hx⟩ := globalSections_surjective K f ((Sheaf.H.equiv₀ G T) z)
    let z' := (Sheaf.H.equiv₀ F T).symm x
    obtain ⟨g', hg'⟩ := (Ext.mk₀_bijective (integers K) F).surjective z'
    refine ⟨g', (Ext.mk₀_bijective (integers K) G).injective ?_⟩
    rw [← Ext.mk₀_comp_mk₀]
    change Sheaf.H.map f 0 (Ext.mk₀ g') = z
    rw [hg']
    apply (Sheaf.H.equiv₀ G T).injective
    rw [← Sheaf.H.equiv₀_naturality]
    change f.hom.app _ ((Sheaf.H.equiv₀ F T) ((Sheaf.H.equiv₀ F T).symm x)) = _
    rwa [AddEquiv.apply_symm_apply]

/-- Native positive-degree pro-étale cohomology vanishes for every
abelian sheaf over an algebraically closed field. -/
theorem H_succ_subsingleton (F : D K) (n : ℕ) : Subsingleton (Sheaf.H F (n + 1)) :=
  Ext.subsingleton_of_projective (integers K) F n

/-- The actual Mathlib ℓ-adic cohomology over an algebraically closed
field vanishes in all positive degrees. -/
theorem adic_H_succ_subsingleton (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Subsingleton ((base K).EllAdicCohomology ℓ (n + 1)) :=
  H_succ_subsingleton K _ n

end
end ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology.globalSections_surjective,
      ``ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology.constantIntegers_projective,
      ``ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton,
      ``ManuscriptAudit.ProetaleAlgebraicallyClosedCohomology.adic_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
