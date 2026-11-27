import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicNativeExactSequence

/-! The actual residue difference is surjective on degree-zero
cohomology, so native degree-one adic cohomology injects into the
degree-one cohomology of the actual residue product. -/

namespace ManuscriptAudit.ProetaleAdicProductHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleAdicNativeExactSequence (sequence shortExact)
open ProetaleAdicProductKernel (difference)
open ProetaleCoefficientUniverseLift (lift epi_map_app_of_epi_app)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev Q := sequence X ℓ

/-- The native residue difference is surjective on global degree-zero cohomology. -/
theorem HZero_difference_surjective : Function.Surjective (Sheaf.H.map (Q X ℓ).g 0) := by
  let T := Scheme.ProEt.mk (𝟙 X)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X
  have he₀ : Epi ((difference X ℓ).hom.app (op T)) :=
    ProetaleAdicProductEpi.evaluation_difference_epi X ℓ T
  have he₁ : Epi ((Q X ℓ).g.hom.app (op T)) :=
    epi_map_app_of_epi_app X (difference X ℓ) (op T) he₀
  intro y
  obtain ⟨z, hz⟩ := (AddCommGrpCat.epi_iff_surjective _).mp he₁
    ((Sheaf.H.equiv₀ (Q X ℓ).X₃ hT) y)
  refine ⟨(Sheaf.H.equiv₀ (Q X ℓ).X₂ hT).symm z, ?_⟩
  apply (Sheaf.H.equiv₀ (Q X ℓ).X₃ hT).injective
  rw [← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply]
  exact hz

/-- The actual adic inclusion induces an injective cohomology map in degree one. -/
theorem HOne_inclusion_injective : Function.Injective (Sheaf.H.map (Q X ℓ).f 1) := by
  let S := Q X ℓ
  have hS : S.ShortExact := shortExact X ℓ
  intro a b hab
  apply sub_eq_zero.mp
  have hz : Sheaf.H.map S.f 1 (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (X := _) hS (a - b) hz
    (show 0 + 1 = 1 by rfl)
  obtain ⟨x, hx⟩ := HZero_difference_surjective X ℓ y
  rw [← hy, ← hx]
  change (x.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
  simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
    Ext.comp_zero]

end
end ManuscriptAudit.ProetaleAdicProductHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicProductHOne.HZero_difference_surjective,
      ``ManuscriptAudit.ProetaleAdicProductHOne.HOne_inclusion_injective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
