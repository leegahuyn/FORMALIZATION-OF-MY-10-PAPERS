import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatCocycleCoboundary

/-! Changing an actual cocycle by a unit coboundary preserves its affine Picard class. -/

namespace ManuscriptAudit.FaithfullyFlatCocyclePicard

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine
open FaithfullyFlatTensorEqualizer

noncomputable section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (s t : (Double A B)ˣ) (v : Bˣ)

private def mulUnit : B →ₗ[A] B where
  toFun b := (v : B) * b
  map_add' b c := mul_add _ _ _
  map_smul' a b := by
    simp only [Algebra.smul_def, RingHom.id_apply]
    exact mul_left_comm _ _ _

private def changeUnitMap
    (h : second A B (v : B) * (s : Double A B) = (t : Double A B) * first A B (v : B)) :
    invariants A B s →ₗ[A] invariants A B t :=
  ((mulUnit A B v).comp (invariants A B s).subtype).codRestrict _ fun x => by
    apply (mem_invariants A B t _).2
    change second A B ((v : B) * x.val) = (t : Double A B) * first A B ((v : B) * x.val)
    rw [map_mul, map_mul, (mem_invariants A B s _).1 x.property, ← mul_assoc, h, mul_assoc]

/-- Multiplying by a change of trivialization is an actual linear equivalence
of the two descended affine line modules. -/
def changeUnitEquiv
    (h : second A B (v : B) * (s : Double A B) = (t : Double A B) * first A B (v : B)) :
    invariants A B s ≃ₗ[A] invariants A B t := by
  have hv₁ : first A B (v : B) * first A B (↑(v⁻¹) : B) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hv₂ : second A B (↑(v⁻¹) : B) * second A B (v : B) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hi : second A B (↑(v⁻¹) : B) * (t : Double A B) =
      (s : Double A B) * first A B (↑(v⁻¹) : B) := calc
    _ = second A B (↑(v⁻¹) : B) *
          ((t : Double A B) * first A B (v : B)) * first A B (↑(v⁻¹) : B) := by
        rw [mul_assoc (second A B (↑(v⁻¹) : B)), mul_assoc (t : Double A B), hv₁, mul_one]
    _ = second A B (↑(v⁻¹) : B) *
          (second A B (v : B) * (s : Double A B)) * first A B (↑(v⁻¹) : B) := by rw [← h]
    _ = _ := by rw [← mul_assoc (second A B (↑(v⁻¹) : B)) _ (s : Double A B), hv₂, one_mul]
  let f := changeUnitMap A B s t v h
  let g := changeUnitMap A B t s v⁻¹ hi
  refine { f with invFun := g, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply Subtype.ext
    change (↑(v⁻¹) : B) * ((v : B) * x.val) = x.val
    rw [← mul_assoc, Units.inv_mul, one_mul]
  · intro x
    apply Subtype.ext
    change (v : B) * ((↑(v⁻¹) : B) * x.val) = x.val
    rw [← mul_assoc, Units.mul_inv, one_mul]

variable [Module.FaithfullyFlat A B]

theorem picardClass_eq_of_unit_change (hs : IsCocycle A B s) (ht : IsCocycle A B t)
    (h : second A B (v : B) * (s : Double A B) = (t : Double A B) * first A B (v : B)) :
    picardClass A B s hs = picardClass A B t ht := by
  letI := invariants_invertible A B s hs
  letI := invariants_invertible A B t ht
  exact CommRing.Pic.mk_eq_mk_iff.mpr ⟨changeUnitEquiv A B s t v h⟩

theorem picardClass_eq_one_iff_coboundary (ht : IsCocycle A B t) :
    picardClass A B t ht = 1 ↔
      ∃ v : Bˣ, t = (Units.map (first A B).toMonoidHom v)⁻¹ *
        Units.map (second A B).toMonoidHom v := by
  refine ⟨exists_coboundary_of_picard_one A B t ht, ?_⟩
  rintro ⟨u, hu⟩
  have he : (t : Double A B) = first A B (↑(u⁻¹) : B) * second A B (u : B) := by
    have h := congrArg Units.val hu
    simpa only [← map_inv] using h
  have hChange : second A B (u : B) * ((1 : (Double A B)ˣ) : Double A B) =
      (t : Double A B) * first A B (u : B) := by
    rw [he, Units.val_one, mul_one, mul_right_comm, ← map_mul, Units.inv_mul, map_one, one_mul]
  letI := invariants_invertible A B t ht
  let e := changeUnitEquiv A B (1 : (Double A B)ˣ) t u hChange
  exact CommRing.Pic.mk_eq_one_iff.mpr ⟨e.symm.trans (baseEquiv A B).symm⟩

end

end ManuscriptAudit.FaithfullyFlatCocyclePicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FaithfullyFlatCocyclePicard.changeUnitEquiv,
      ``ManuscriptAudit.FaithfullyFlatCocyclePicard.picardClass_eq_of_unit_change,
      ``ManuscriptAudit.FaithfullyFlatCocyclePicard.picardClass_eq_one_iff_coboundary] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
