import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Covariant Ext across a support kernel, and commutation with the actual
contravariant connecting map of a second short exact sequence. -/

namespace ManuscriptAudit.ExtSupportExactness

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Ext into a zero object is zero, with no assumptions on the first variable. -/
theorem ext_subsingleton_of_isZero (P H : C) (h : IsZero H) (n : ℕ) :
    Subsingleton (Ext P H n) := by
  have hzero : ∀ x : Ext P H n, x = 0 := by
    intro x
    calc
      x = x.comp (Ext.mk₀ (𝟙 H)) (add_zero n) := (Ext.comp_mk₀_id x).symm
      _ = 0 := by rw [h.eq_of_tgt (𝟙 H) 0, Ext.mk₀_zero, Ext.comp_zero]
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

/-- If the third term has zero Ext in two successive degrees, the
support inclusion is an equivalence in the second degree. -/
def inclusionEquiv {S : ShortComplex C} (hS : S.ShortExact) (P : C) (n : ℕ)
    (h₀ : Subsingleton (Ext P S.X₃ n)) (h₁ : Subsingleton (Ext P S.X₃ (n + 1))) :
    Ext P S.X₁ (n + 1) ≃+ Ext P S.X₂ (n + 1) := by
  let f := (Ext.mk₀ S.f).postcomp P (add_zero (n + 1))
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    have hz : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁ P hS (x - y) hz (rfl : n + 1 = n + 1)
    rw [h₀.elim t 0, Ext.zero_comp] at ht
    exact ht.symm
  · intro y
    exact Ext.covariant_sequence_exact₂ P hS y (h₁.elim _ _)

theorem boundary_naturality {S : ShortComplex C} (hS : S.ShortExact)
    {F G : C} (f : F ⟶ G) (n : ℕ) (x : Ext S.X₁ F n) :
    ((hS.extClass).comp x (Nat.add_comm 1 n)).comp (Ext.mk₀ f) (add_zero (n + 1)) =
      (hS.extClass).comp (x.comp (Ext.mk₀ f) (add_zero n)) (Nat.add_comm 1 n) :=
  Ext.comp_assoc_of_third_deg_zero hS.extClass x (Ext.mk₀ f) (Nat.add_comm 1 n)

end
end ManuscriptAudit.ExtSupportExactness

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExtSupportExactness.ext_subsingleton_of_isZero,
      ``ManuscriptAudit.ExtSupportExactness.inclusionEquiv,
      ``ManuscriptAudit.ExtSupportExactness.boundary_naturality] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
