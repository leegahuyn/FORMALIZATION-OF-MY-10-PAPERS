import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleProperHOne

/-! Actual degree two maps to the kernel of the difference in product cohomology. -/

namespace ManuscriptAudit.ProetaleAdicHTwoProductKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleAdicNativeExactSequence (sequence shortExact)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev Q := sequence X ℓ

private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

/-- Here the product is the literal countable product of the native residue sheaves. -/
theorem product_HOne_subsingleton
    (h : ∀ n, Subsingleton (Sheaf.H (finiteCoefficient X ℓ n) 1)) :
    Subsingleton (Sheaf.H (Q X ℓ).X₂ 1) := by
  let e : (Q X ℓ).X₂ ≅ ∏ᶜ (finiteCoefficient X ℓ) := PreservesProduct.iso (lift X) (residueSheaf X ℓ)
  have hE : Function.LeftInverse (Sheaf.H.map e.inv 1) (Sheaf.H.map e.hom 1) := by
    intro x
    rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  constructor
  intro x y
  apply hE.injective
  apply ExtOneProduct.projectionMap_injective (finiteCoefficient X ℓ) (integers X)
  funext n
  exact (h n).elim _ _

abbrev differenceKernel :=
  (Sheaf.H.map (Q X ℓ).g 2).ker

private def toDifferenceKernel :
    X.EllAdicCohomology ℓ 2 →+ differenceKernel X ℓ :=
  (Sheaf.H.map (Q X ℓ).f 2).codRestrict (differenceKernel X ℓ) (by
    intro a
    change (a.comp (Ext.mk₀ (Q X ℓ).f) (add_zero 2)).comp
      (Ext.mk₀ (Q X ℓ).g) (add_zero 2) = 0
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, (Q X ℓ).zero,
      Ext.mk₀_zero, Ext.comp_zero])

private theorem toDifferenceKernel_bijective
    (h : ∀ n, Subsingleton (Sheaf.H (finiteCoefficient X ℓ n) 1)) :
    Function.Bijective (toDifferenceKernel X ℓ) := by
  let Q' := Q X ℓ
  have hS : Q'.ShortExact := shortExact X ℓ
  constructor
  · intro a b hab
    apply sub_eq_zero.mp
    have hp : Sheaf.H.map Q'.f 2 a = Sheaf.H.map Q'.f 2 b := congrArg Subtype.val hab
    have hz : Sheaf.H.map Q'.f 2 (a-b) = 0 := by rw [map_sub, hp, sub_self]
    obtain ⟨v, hv⟩ := Ext.covariant_sequence_exact₁ (X := _) hS (a-b) hz
      (show 1+1=2 by rfl)
    have hv₀ : v = 0 := (product_HOne_subsingleton X ℓ h).elim v 0
    rw [hv₀, Ext.zero_comp] at hv
    exact hv.symm
  · intro z
    have hz : Sheaf.H.map Q'.g 2 z.val = 0 := z.property
    obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ (integers X) hS z.val hz
    exact ⟨a, Subtype.ext ha⟩

/-- Identification with the kernel in native product cohomology. No commutation
of degree-two cohomology with a countable product is required for this identification. -/
def secondEquiv
    (h : ∀ n, Subsingleton (Sheaf.H (finiteCoefficient X ℓ n) 1)) :
    X.EllAdicCohomology ℓ 2 ≃+ differenceKernel X ℓ :=
  AddEquiv.ofBijective (toDifferenceKernel X ℓ) (toDifferenceKernel_bijective X ℓ h)

theorem secondEquiv_val
    (h : ∀ n, Subsingleton (Sheaf.H (finiteCoefficient X ℓ n) 1))
    (a : X.EllAdicCohomology ℓ 2) :
    (secondEquiv X ℓ h a).val = Sheaf.H.map (Q X ℓ).f 2 a :=
  rfl

def properCuspSecondEquiv (K : Type) [Field K] [IsAlgClosed K]
    (l : ℕ) [Fact l.Prime] [NeZero (l : K)] :
    (CuspProperCompactification.projectiveCusp K).EllAdicCohomology l 2 ≃+
      differenceKernel (CuspProperCompactification.projectiveCusp K) l :=
  secondEquiv _ l (CuspNativeProetaleProperHOne.residue_HOne_subsingleton K l)

end
end ManuscriptAudit.ProetaleAdicHTwoProductKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicHTwoProductKernel.product_HOne_subsingleton,
      ``ManuscriptAudit.ProetaleAdicHTwoProductKernel.secondEquiv,
      ``ManuscriptAudit.ProetaleAdicHTwoProductKernel.secondEquiv_val,
      ``ManuscriptAudit.ProetaleAdicHTwoProductKernel.properCuspSecondEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
