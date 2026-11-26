import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import PrimalitySheafVerification.ManuscriptAudit.FiniteSkyscraperSumHOne

/-!
# Higher Zariski cohomology of a point skyscraper

Taking the skyscraper of an abelian group preserves kernels and
epimorphisms. The stalk functor preserves monomorphisms, so its right
adjoint preserves injectives. An injective embedding of the coefficient
group therefore supplies a native Ext dimension shift.
-/

namespace ManuscriptAudit.ZariskiSkyscraperHigherCohomology

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.SkyscraperHOne
open ManuscriptAudit.FiniteSkyscraperSumHOne
open scoped ZeroObject

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev AGrp := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

section

variable {X : TopCat.{0}} (p : X) [(U : Opens X) → Decidable (p ∈ U)]

private abbrev skFunctor : AGrp ⥤ AbelianSheaf X := skyscraperSheafFunctor p

private theorem map_app_epi {M N : AGrp} (f : M ⟶ N) [Epi f] (U : (Opens X)ᵒᵖ) :
    Epi (((skFunctor p).map f).hom.app U) := by
  by_cases hp : p ∈ unop U
  · let eM : (skyscraperPresheaf p M).obj U ≅ M := eqToIso (by simp [skyscraperPresheaf_obj, hp])
    let eN : (skyscraperPresheaf p N).obj U ≅ N := eqToIso (by simp [skyscraperPresheaf_obj, hp])
    change Epi ((SkyscraperPresheafFunctor.map' p f).app U)
    rw [SkyscraperPresheafFunctor.map'_app, dif_pos hp]
    change Epi (eM.hom ≫ f ≫ eN.inv)
    infer_instance
  · have hZ : IsZero ((skyscraperSheaf p N).obj.obj U) :=
      (isTerminalSkyscraperSheafObjObjOfNotMem (A := N) hp).isZero
    exact ⟨fun _ g h _ => hZ.eq_of_src g h⟩

private theorem sk_preservesEpimorphisms : (skFunctor p).PreservesEpimorphisms where
  preserves {M N} f hf := by
    letI : Epi f := hf
    let F := TopCat.Sheaf.forget AGrp X
    let g := (skFunctor p).map f
    letI : Epi (F.map g) := (NatTrans.epi_iff_epi_app _).mpr (map_app_epi p f)
    constructor
    intro K a b h
    apply F.map_injective
    apply (cancel_epi (F.map g)).mp
    rw [← F.map_comp, ← F.map_comp, h]

end

private theorem H_succ_subsingleton_of_surjective {X : TopCat.{0}}
    (S : ShortComplex (AbelianSheaf X)) (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ) (hSurj : Function.Surjective (Sheaf.H.map S.g n)) :
    Subsingleton (S.X₁.H (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let Z := (constantSheaf (Opens.grothendieckTopology X) AGrp).obj
    (AddCommGrpCat.of (ULift ℤ))
  change Ext Z S.X₁ (n + 1) at x
  have hx : x.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (show n + 1 = n + 1 by rfl)
  obtain ⟨z, hz⟩ := hSurj y
  change z.comp (Ext.mk₀ S.g) (add_zero n) = y at hz
  change x = 0
  rw [← hy, ← hz, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
    Ext.comp_zero]

section

variable {X : TopCat.{0}} (p : X) [(U : Opens X) → Decidable (p ∈ U)]

private theorem skyscraper_succ_of_epi_HMap (M : AGrp) (n : ℕ)
    (h : ∀ {A B : AGrp} (f : A ⟶ B) [Epi f],
      Function.Surjective (Sheaf.H.map ((skFunctor p).map f) n)) :
    Subsingleton ((skyscraperSheaf p M).H (n + 1)) := by
  let K := skFunctor p
  let adj := stalkSkyscraperSheafAdjunction (C := AGrp) p
  letI : K.IsRightAdjoint := adj.isRightAdjoint
  letI : K.Additive := K.additive_of_preserves_binary_products
  letI : K.PreservesEpimorphisms := sk_preservesEpimorphisms p
  letI : ∀ {A B : AGrp} (f : A ⟶ B), PreservesLimit (parallelPair f 0) K :=
    fun _ => inferInstance
  letI : K.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels K
  letI : K.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let S₀ := ShortComplex.cokernelSequence (Injective.ι M)
  letI : Mono S₀.f := inferInstanceAs (Mono (Injective.ι M))
  letI : Epi S₀.g := inferInstanceAs (Epi (cokernel.π (Injective.ι M)))
  have h₀ : S₀.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (Injective.ι M))
      (inferInstanceAs (Mono S₀.f)) (inferInstanceAs (Epi S₀.g))
  let S := S₀.map K
  have hS : S.ShortExact := h₀.map K
  letI : Injective S.X₂ := by
    change Injective (K.obj (Injective.under M))
    infer_instance
  exact H_succ_subsingleton_of_surjective S hS n (h S₀.g)

/-- Every positive degree of native Zariski sheaf cohomology vanishes for a point skyscraper. -/
theorem skyscraper_H_succ_subsingleton (M : AGrp) (n : ℕ) :
    Subsingleton ((skyscraperSheaf p M).H (n + 1)) := by
  induction n generalizing M with
  | zero => exact skyscraper_H1_subsingleton p M
  | succ n ih =>
    apply skyscraper_succ_of_epi_HMap p M (n + 1)
    intro A B f _ y
    letI := ih B
    exact ⟨0, Subsingleton.elim _ _⟩

end

/-- The positive-degree result for the native skyscraper with a classical membership test. -/
theorem pointSummand_H_succ_subsingleton {X : TopCat.{0}} (p : X) (M : AGrp) (n : ℕ) :
    Subsingleton ((pointSummand p M).H (n + 1)) := by
  classical
  exact skyscraper_H_succ_subsingleton p M n

end

end ManuscriptAudit.ZariskiSkyscraperHigherCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ZariskiSkyscraperHigherCohomology.skyscraper_H_succ_subsingleton,
      ``ManuscriptAudit.ZariskiSkyscraperHigherCohomology.pointSummand_H_succ_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
