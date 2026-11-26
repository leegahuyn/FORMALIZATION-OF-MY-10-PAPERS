import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspFlatNormalization
import PrimalitySheafVerification.ManuscriptAudit.CuspReductionBaseChange

/-!
# Sections of unramified morphisms after flat cusp base change

For any flat algebra over the cusp, the normalization still has no new
sections of an affine formally unramified morphism. The two reductions
modulo the conductor have the original algebra as their equalizer.
-/

namespace ManuscriptAudit.CuspFlatUnramifiedSections

open CuspDelta CuspFlatNormalization CuspReductionBaseChange
open Polynomial TensorProduct

noncomputable section

variable (K : Type*) [Field K]

private abbrev A := CuspPunctured.CuspSubalgebra K
private abbrev B := Polynomial K
private abbrev D := cuspSquareQuotient K

private theorem reduction_difference_exact :
    Function.Exact (Algebra.linearMap (A K) (B K))
      ((reductionAlg K).toLinearMap - (constantReductionAlg K).toLinearMap) := by
  intro f
  change cuspSquareReduction K f - cuspSquareReduction K (C (f.coeff 0)) = 0 ↔
    ∃ a : A K, (a : B K) = f
  rw [sub_eq_zero, cusp_square_reduction_eq_constant_iff, and_iff_right rfl]
  exact ⟨fun h => ⟨⟨f, (cusp_mem_iff_coeff_one_zero K f).mpr h⟩, rfl⟩, by
    rintro ⟨a, rfl⟩
    exact (cusp_mem_iff_coeff_one_zero K _).mp a.property⟩

variable (T : Type*) [CommRing T] [Algebra (A K) T] [Module.Flat (A K) T]

private abbrev q := flatReductionAlg K T
private abbrev c := flatConstantReductionAlg K T
private abbrev normalization := T ⊗[A K] B K
private abbrev reduction := T ⊗[A K] D K
private abbrev inclusion := Algebra.ofId T (normalization K T)

private theorem inclusion_apply (t : T) :
    inclusion K T t = t ⊗ₜ[A K] (1 : B K) := by
  simp only [inclusion, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_self_apply]

private theorem flatReduction_toLinearMap :
    ((reductionAlg K).toLinearMap).lTensor T =
      ((q K T).restrictScalars (A K)).toLinearMap := by
  apply TensorProduct.ext'
  intro t f
  exact (flatReductionAlg_tmul K T t f).symm

private theorem flatConstantReduction_toLinearMap :
    ((constantReductionAlg K).toLinearMap).lTensor T =
      ((c K T).restrictScalars (A K)).toLinearMap := by
  apply TensorProduct.ext'
  intro t f
  exact (flatConstantReductionAlg_tmul K T t f).symm

/-- After flat base change, the equalizer of the two reductions is exactly
the image of the original cusp algebra. -/
theorem flat_reduction_equalizer (z : normalization K T) :
    (q K T z = c K T z) ↔ ∃ t : T, inclusion K T t = z := by
  have h := flat_exact_from_inclusion K T _ (reduction_difference_exact K)
  rw [LinearMap.lTensor_sub, flatReduction_toLinearMap, flatConstantReduction_toLinearMap] at h
  simpa only [LinearMap.sub_apply, sub_eq_zero, AlgHom.toLinearMap_apply,
    AlgHom.restrictScalars_apply, Set.mem_range, Algebra.TensorProduct.includeLeft_apply,
    inclusion_apply] using h z

private def inclusionToEqualizer :
    T →ₐ[T] AlgHom.equalizer (q K T) (c K T) :=
  (inclusion K T).codRestrict _ fun t =>
    (AlgHom.mem_equalizer _ _ _).mpr
      ((flat_reduction_equalizer K T (inclusion K T t)).mpr ⟨t, rfl⟩)

/-- The actual equalizer of the two base-changed reduction maps is the
original flat algebra, as an algebra over itself. -/
def flatBaseEquivEqualizer : T ≃ₐ[T] AlgHom.equalizer (q K T) (c K T) :=
  AlgEquiv.ofBijective (inclusionToEqualizer K T) ⟨by
    intro t u h
    apply includeBase_injective K T
    exact congrArg Subtype.val h, by
    intro z
    obtain ⟨t, ht⟩ := (flat_reduction_equalizer K T z.val).mp
      ((AlgHom.mem_equalizer _ _ _).mp z.property)
    exact ⟨t, Subtype.ext ht⟩⟩

section SectionEquivalence

variable {R U V S : Type*}
variable [CommSemiring R] [Semiring U] [Semiring V] [Semiring S]
variable [Algebra R U] [Algebra R V] [Algebra R S]
variable (f g : U →ₐ[R] V) (h : ∀ t : S →ₐ[R] U, f.comp t = g.comp t)

private def restrictSectionToEqualizer (t : S →ₐ[R] U) :
    S →ₐ[R] AlgHom.equalizer f g :=
  t.codRestrict _ fun x => (AlgHom.mem_equalizer f g _).2 (AlgHom.congr_fun (h t) x)

private def sectionsEquivOfCompEq (e : R ≃ₐ[R] AlgHom.equalizer f g) :
    (S →ₐ[R] R) ≃ (S →ₐ[R] U) where
  toFun t := (AlgHom.equalizer f g).val.comp (e.toAlgHom.comp t)
  invFun t := e.symm.toAlgHom.comp (restrictSectionToEqualizer f g h t)
  left_inv t := AlgHom.ext fun x => e.symm_apply_apply (t x)
  right_inv t := AlgHom.ext fun x =>
    congrArg Subtype.val (e.apply_symm_apply (restrictSectionToEqualizer f g h t x))

end SectionEquivalence

variable {P : Type*} [CommRing P] [Algebra T P] [Algebra.FormallyUnramified T P]

set_option backward.isDefEq.respectTransparency false in
/-- A formally unramified algebra has the same sections before and after
base change from a flat cusp algebra to its polynomial normalization. -/
def flatSectionsEquiv : (P →ₐ[T] T) ≃ (P →ₐ[T] normalization K T) :=
  sectionsEquivOfCompEq (R := T) (U := normalization K T) (V := reduction K T) (S := P)
    (q K T) (c K T) (flatReduction_comp_sections K T) (flatBaseEquivEqualizer K T)

set_option backward.isDefEq.respectTransparency false in
/-- The forward section map is evaluation followed by the original base inclusion. -/
theorem flatSectionsEquiv_apply (f : P →ₐ[T] T) (p : P) :
    flatSectionsEquiv K T f p = f p ⊗ₜ[A K] (1 : B K) := by
  change inclusion K T (f p) = _
  exact inclusion_apply K T _

end

end ManuscriptAudit.CuspFlatUnramifiedSections

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspFlatUnramifiedSections.flat_reduction_equalizer,
      ``ManuscriptAudit.CuspFlatUnramifiedSections.flatBaseEquivEqualizer,
      ``ManuscriptAudit.CuspFlatUnramifiedSections.flatSectionsEquiv,
      ``ManuscriptAudit.CuspFlatUnramifiedSections.flatSectionsEquiv_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
