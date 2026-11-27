import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleHOneUniverseComparison
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeConductorHOne
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveCyclicHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne

/-! The actual small étale to native pro-étale degree-one comparison
is bijective with finite residue coefficients on the proper models. -/

namespace ManuscriptAudit.EtaleProetaleFiniteHOneComparison

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNode)
open CuspProperCompactification (projectiveCusp)
open EtaleProetaleResidueComparison (residueDirectImageIso)
open ProetaleResidueSheaves (residueSheaf)
open ProetaleAdicHOneDetection (finiteCoefficient)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

section Comparison

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)

abbrev etaleCoefficient :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod (ℓ ^ n)))

/-- The actual site comparison on H¹ of the finite residue sheaf. -/
def comparison :
    Sheaf.H (etaleCoefficient X ℓ n) 1 →+ Sheaf.H (finiteCoefficient X ℓ n) 1 :=
  (EtaleProetaleHOneUniverseComparison.comparison X (residueSheaf X ℓ n)).comp
    (Sheaf.H.map (residueDirectImageIso X ℓ n).inv 1)

theorem comparison_injective : Function.Injective (comparison X ℓ n) := by
  let e := residueDirectImageIso X ℓ n
  have hi : Function.LeftInverse (Sheaf.H.map e.hom 1) (Sheaf.H.map e.inv 1) := by
    intro x
    rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  exact (EtaleProetaleHOneUniverseComparison.comparison_injective X (residueSheaf X ℓ n)).comp
    hi.injective

/-- An injective actual comparison between two copies of a finite group is surjective. -/
theorem comparison_surjective_of_finiteType (T : Type) [Finite T]
    (e : Sheaf.H (etaleCoefficient X ℓ n) 1 ≃ T)
    (f : Sheaf.H (finiteCoefficient X ℓ n) 1 ≃ T) :
    Function.Surjective (comparison X ℓ n) := by
  let g : T → T := f ∘ comparison X ℓ n ∘ e.symm
  have hg : Function.Injective g := f.injective.comp
    ((comparison_injective X ℓ n).comp e.symm.injective)
  intro a
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hg (f a)
  exact ⟨e.symm t, f.injective ht⟩

end Comparison

section Models

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

theorem node_surjective (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Function.Surjective (comparison (projectiveNode K) ℓ n) := by
  letI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (show ℓ ≠ 0 from (Fact.out : Nat.Prime ℓ).ne_zero)⟩
  letI : NeZero ((ℓ ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩
  exact comparison_surjective_of_finiteType (projectiveNode K) ℓ n (ZMod (ℓ ^ n))
    (NodalProjectiveCyclicHOne.projectiveHOneEquiv K (ℓ ^ n) h2).toEquiv
    (NodalNativeConductorHOne.residueHOneEquiv K h2 ℓ n).toEquiv

/-- The actual degree-one site comparison on every finite residue of the proper split node. -/
def nodeEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Sheaf.H (etaleCoefficient (projectiveNode K) ℓ n) 1 ≃+
      Sheaf.H (finiteCoefficient (projectiveNode K) ℓ n) 1 :=
  AddEquiv.ofBijective (comparison (projectiveNode K) ℓ n)
    ⟨comparison_injective (projectiveNode K) ℓ n, node_surjective K ℓ h2 n⟩

/-- The same actual comparison on each finite residue of the proper cusp. -/
def cuspEquiv (n : ℕ) :
    Sheaf.H (etaleCoefficient (projectiveCusp K) ℓ n) 1 ≃+
      Sheaf.H (finiteCoefficient (projectiveCusp K) ℓ n) 1 :=
  AddEquiv.ofBijective (comparison (projectiveCusp K) ℓ n)
    ⟨comparison_injective (projectiveCusp K) ℓ n, fun _ ↦
      ⟨0, (CuspNativeProetaleProperHOne.residue_HOne_subsingleton K ℓ n).elim _ _⟩⟩

end Models

end
end ManuscriptAudit.EtaleProetaleFiniteHOneComparison

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleFiniteHOneComparison.comparison_injective,
      ``ManuscriptAudit.EtaleProetaleFiniteHOneComparison.comparison_surjective_of_finiteType,
      ``ManuscriptAudit.EtaleProetaleFiniteHOneComparison.nodeEquiv,
      ``ManuscriptAudit.EtaleProetaleFiniteHOneComparison.cuspEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
