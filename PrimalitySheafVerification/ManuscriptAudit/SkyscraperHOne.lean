import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Topology.Sheaves.Flasque
import PrimalitySheafVerification.ManuscriptAudit.ClosedSupportDetection

/-!
# First cohomology of a point skyscraper

Paper 6, physical p. 202, asserts a contribution to first cohomology from
each of its point skyscrapers. An individual skyscraper has zero first
Zariski sheaf cohomology. The proof uses native flasqueness and the long
exact Ext sequence of an injective embedding.
-/

namespace ManuscriptAudit.SkyscraperHOne

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev G := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

private def topIsTerminal (X : TopCat.{0}) : IsTerminal (⊤ : Opens X) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

/-- A flasque abelian sheaf has trivial native cohomology in degree one. -/
theorem flasque_H1_subsingleton {X : TopCat.{0}} (F : AbelianSheaf X)
    [TopCat.Sheaf.IsFlasque F] : Subsingleton (F.H 1) := by
  let S := ShortComplex.cokernelSequence (Injective.ι F)
  haveI : Injective S.X₂ := by
    change Injective (Injective.under F)
    infer_instance
  haveI : TopCat.Sheaf.IsFlasque S.X₁ := by
    change TopCat.Sheaf.IsFlasque F
    infer_instance
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) ?_ inferInstance
    change Mono (Injective.ι F)
    infer_instance
  have hepi : Epi (S.g.hom.app (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) hS
  have hSurj : Function.Surjective (Sheaf.H.map S.g 0) := by
    intro y
    obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi
      (Sheaf.H.equiv₀ S.X₃ (topIsTerminal X) y)
    refine ⟨(Sheaf.H.equiv₀ S.X₂ (topIsTerminal X)).symm t, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  apply subsingleton_of_forall_eq 0
  intro x
  let Z := (constantSheaf (Opens.grothendieckTopology X) G).obj
    (AddCommGrpCat.of (ULift ℤ))
  change Ext Z S.X₁ 1 at x
  have hx : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
    Ext.eq_zero_of_injective _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (show 0 + 1 = 1 by rfl)
  obtain ⟨z, hz⟩ := hSurj y
  change z.comp (Ext.mk₀ S.g) (add_zero 0) = y at hz
  change x = 0
  rw [← hy, ← hz, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
    Ext.comp_zero]

/-- A point skyscraper has no nonzero class in native degree-one sheaf cohomology. -/
theorem skyscraper_H1_subsingleton {X : TopCat.{0}} (p : X)
    [(U : Opens X) → Decidable (p ∈ U)] (A : G) :
    Subsingleton ((skyscraperSheaf p A).H 1) := by
  letI := TopCat.isFlasque_skyscraperSheaf_of_hasZeroObject p A
  exact flasque_H1_subsingleton _

end

end ManuscriptAudit.SkyscraperHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SkyscraperHOne.flasque_H1_subsingleton,
      ``ManuscriptAudit.SkyscraperHOne.skyscraper_H1_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
