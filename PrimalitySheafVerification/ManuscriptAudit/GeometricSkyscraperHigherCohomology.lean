import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero

/-!
# Higher étale cohomology of a geometric skyscraper

The stalk functor is exact, so its right adjoint preserves injectives.
The skyscraper also preserves epimorphisms and kernels. Apply it to an
injective embedding of the coefficient group and use the native Ext long
exact sequence to shift degrees. At degree zero the product map at the
terminal object is surjective.
-/

namespace ManuscriptAudit.GeometricSkyscraperCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

noncomputable section

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

variable {X : Scheme.{u}} (Φ : X.smallEtaleTopology.Point.{u})

private theorem H_succ_subsingleton_of_surjective
    (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (hS : S.ShortExact)
    [Injective S.X₂] (n : ℕ) (hSurj : Function.Surjective (Sheaf.H.map S.g n)) :
    Subsingleton (Sheaf.H S.X₁ (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  change Ext Z S.X₁ (n + 1) at x
  have hx : x.comp (Ext.mk₀ S.f) (add_zero (n + 1)) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hS x hx (show n + 1 = n + 1 by rfl)
  obtain ⟨z, hz⟩ := hSurj y
  change z.comp (Ext.mk₀ S.g) (add_zero n) = y at hz
  change x = 0
  rw [← hy, ← hz, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
    Ext.comp_zero]

private theorem geometricSkyscraperHZeroMap_surjective
    {M N : AddCommGrpCat.{u}} (f : M ⟶ N) [Epi f] :
    Function.Surjective (Sheaf.H.map (Φ.skyscraperSheafFunctor.map f) 0) := by
  let T := ⊤_ X.Etale
  let p := Φ.skyscraperSheafFunctor.map f
  let hT : IsTerminal T := terminalIsTerminal
  let hEpi := geometricSkyscraper_map_app_epi Φ f (op T)
  intro y
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hEpi
    (Sheaf.H.equiv₀ (Φ.skyscraperSheaf N) hT y)
  refine ⟨(Sheaf.H.equiv₀ (Φ.skyscraperSheaf M) hT).symm t, ?_⟩
  rw [Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]

private theorem geometricSkyscraper_succ_of_epi_HMap
    (M : AddCommGrpCat.{u}) (n : ℕ)
    (h : ∀ {A B : AddCommGrpCat.{u}} (f : A ⟶ B) [Epi f],
      Function.Surjective (Sheaf.H.map (Φ.skyscraperSheafFunctor.map f) n)) :
    Subsingleton (Sheaf.H (Φ.skyscraperSheaf M) (n + 1)) := by
  let G := Φ.skyscraperSheafFunctor (A := AddCommGrpCat.{u})
  letI : G.Additive := G.additive_of_preserves_binary_products
  letI : G.PreservesEpimorphisms := geometricSkyscraper_preservesEpimorphisms Φ
  letI : ∀ {A B : AddCommGrpCat.{u}} (f : A ⟶ B),
      PreservesLimit (parallelPair f 0) G := fun _ => inferInstance
  letI : G.PreservesHomology := preservesHomology_of_preservesEpis_and_kernels G
  letI : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms Φ.skyscraperSheafAdjunction
  let S₀ := ShortComplex.cokernelSequence (Injective.ι M)
  have h₀ : S₀.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) inferInstance inferInstance
  letI : Mono S₀.f := h₀.mono_f
  letI : Epi S₀.g := h₀.epi_g
  let S := S₀.map G
  have hS : S.ShortExact := h₀.map G
  letI : Injective S.X₂ := by
    change Injective (G.obj (Injective.under M))
    infer_instance
  exact H_succ_subsingleton_of_surjective S hS n (h S₀.g)

/-- All positive degrees of actual étale cohomology vanish for a geometric skyscraper. -/
theorem geometricSkyscraperH_succ_subsingleton (M : AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H (Φ.skyscraperSheaf M) (n + 1)) := by
  induction n generalizing M with
  | zero => exact geometricSkyscraper_succ_of_epi_HMap Φ M 0
      (fun f => geometricSkyscraperHZeroMap_surjective Φ f)
  | succ n ih =>
    apply geometricSkyscraper_succ_of_epi_HMap Φ M (n + 1)
    intro A B f _ y
    letI := ih B
    exact ⟨0, Subsingleton.elim _ _⟩

end

end ManuscriptAudit.GeometricSkyscraperCohomology

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GeometricSkyscraperCohomology.geometricSkyscraperH_succ_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
