import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FlatTwistedBaseChangeKernel

/-! Compatibility of the actual twisted tensor descent line with extension
of scalars. The transition is pulled back through the canonical double-overlap map. -/

namespace ManuscriptAudit.FlatTwistedBaseChangeLine

open TensorProduct TwistedTensorEqualizer FlatTwistedDescentLine FlatTwistedBaseChangeKernel
open scoped TensorProduct

noncomputable section

universe u
variable (A B S : Type u) [CommRing A] [CommRing B] [CommRing S]
variable [Algebra A B] [Algebra A S]

abbrev Cover := S ⊗[A] B

/-- The actual double overlap after base change. -/
def overlapEquiv : Double S (Cover A B S) ≃ₐ[S] S ⊗[A] Double A B :=
  (Algebra.TensorProduct.cancelBaseChange A S S (Cover A B S) B).trans
    (Algebra.TensorProduct.assoc A A S S B B)

theorem overlapEquiv_tmul (s r : S) (b c : B) :
    overlapEquiv A B S ((s ⊗ₜ[A] b) ⊗ₜ[S] (r ⊗ₜ[A] c)) =
      (r * s) ⊗ₜ[A] (b ⊗ₜ[A] c) := by
  simp only [overlapEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
    TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.assoc_tmul]

/-- Pull a genuine transition on the double overlap to its new base. -/
def overlapMap : Double A B →ₐ[A] Double S (Cover A B S) :=
  ((overlapEquiv A B S).symm.restrictScalars A).toAlgHom.comp
    Algebra.TensorProduct.includeRight


theorem overlapMap_tmul (b c : B) :
    overlapMap A B S (b ⊗ₜ[A] c) =
      ((1 : S) ⊗ₜ[A] b) ⊗ₜ[S] ((1 : S) ⊗ₜ[A] c) := by
  apply (overlapEquiv A B S).injective
  change overlapEquiv A B S ((overlapEquiv A B S).symm
    ((1 : S) ⊗ₜ[A] (b ⊗ₜ[A] c))) = _
  rw [AlgEquiv.apply_symm_apply, overlapEquiv_tmul, one_mul]

/-- The first Čech projection has the literal base-change square. -/
theorem overlapMap_first (b : B) :
    overlapMap A B S (first A B b) =
      first S (Cover A B S) ((1 : S) ⊗ₜ[A] b) := by
  rw [first_apply, first_apply, overlapMap_tmul] <;> rfl

/-- The second Čech projection has the literal base-change square. -/
theorem overlapMap_second (b : B) :
    overlapMap A B S (second A B b) =
      second S (Cover A B S) ((1 : S) ⊗ₜ[A] b) := by
  rw [second_apply, second_apply, overlapMap_tmul] <;> rfl

def pulledUnit (t : (Double A B)ˣ) : (Double S (Cover A B S))ˣ :=
  Units.map (overlapMap A B S).toRingHom.toMonoidHom t

private theorem overlapEquiv_unit (t : (Double A B)ˣ) :
    overlapEquiv A B S (pulledUnit A B S t : Double S (Cover A B S)) =
      (1 : S) ⊗ₜ[A] (t : Double A B) :=
  (overlapEquiv A B S).apply_symm_apply _

/-- Applying the scalar-extended differential agrees with its actual
Čech formula on the base-changed double overlap. -/
theorem differential_baseChange (t : (Double A B)ˣ) (x : Cover A B S) :
    overlapEquiv A B S (differential S (Cover A B S) (pulledUnit A B S t) x) =
      (differential A B t).baseChange S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s b =>
    simp only [differential_apply, map_sub, map_mul, overlapEquiv_unit, first_apply, second_apply,
      Algebra.TensorProduct.one_def, overlapEquiv_tmul, one_mul, mul_one,
      LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub (R := A)]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [Module.Flat A S]

/-- Native cocycle invariant lines commute with flat extension of scalars. -/
def lineBaseChange (t : (Double A B)ˣ) :
    S ⊗[A] invariants A B t ≃ₗ[S] invariants S (Cover A B S) (pulledUnit A B S t) := by
  refine (invariantsBaseChange (S := S) t).trans (LinearEquiv.ofEq _ _ ?_)
  ext x
  change (differential A B t).baseChange S x = 0 ↔
    differential S (Cover A B S) (pulledUnit A B S t) x = 0
  rw [← differential_baseChange, ← map_zero (overlapEquiv A B S),
    (overlapEquiv A B S).injective.eq_iff]

end

end ManuscriptAudit.FlatTwistedBaseChangeLine

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FlatTwistedBaseChangeLine.overlapEquiv_tmul,
      ``ManuscriptAudit.FlatTwistedBaseChangeLine.overlapMap_first,
      ``ManuscriptAudit.FlatTwistedBaseChangeLine.overlapMap_second,
      ``ManuscriptAudit.FlatTwistedBaseChangeLine.differential_baseChange,
      ``ManuscriptAudit.FlatTwistedBaseChangeLine.lineBaseChange] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
