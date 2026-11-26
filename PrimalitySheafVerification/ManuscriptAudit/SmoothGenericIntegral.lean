import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Integral elements in a smooth generic fiber

For a smooth algebra over an integrally closed domain, any element
of the actual tensor-product generic fiber that is integral over the
algebra already comes from a unique element of that algebra. This is
the integral-closure comparison needed to lift generic-fiber
idempotents and pass to individual affine components.
-/

namespace ManuscriptAudit.SmoothGenericIntegral

open scoped TensorProduct

noncomputable section

variable (A B F : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [Algebra A B] [Algebra.Smooth A B]
  [Field F] [Algebra A F] [IsFractionRing A F]

/-- The canonical map to the tensor-product generic fiber is injective. -/
theorem genericAlgebraMap_injective :
    Function.Injective (algebraMap B (B ⊗[A] F)) := by
  have h : Function.Injective
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] F) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective A F)
  exact h

/-- An integral generic-fiber element comes from a unique actual section. -/
theorem existsUnique_section (z : B ⊗[A] F) (hz : IsIntegral B z) :
    ∃! b : B, algebraMap B (B ⊗[A] F) b = z := by
  let g := TensorProduct.toIntegralClosure A B F
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := A) (S := B) (B := F)).2 ⟨z, hz⟩
  have h (x : B ⊗[A] integralClosure A F) :
      ∃ b : B, algebraMap B (B ⊗[A] F) b = (g x : B ⊗[A] F) := by
    induction x with
    | zero => exact ⟨0, by simp⟩
    | tmul b c =>
      obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := F)).1 c.property
      refine ⟨a • b, ?_⟩
      have htmul : (g (b ⊗ₜ[A] c) : B ⊗[A] F) = b ⊗ₜ[A] (c : F) := by
        simp [g, TensorProduct.toIntegralClosure]
      rw [htmul, ← ha]
      change (a • b) ⊗ₜ[A] (1 : F) = b ⊗ₜ[A] algebraMap A F a
      rw [Algebra.algebraMap_eq_smul_one]
      exact TensorProduct.smul_tmul a b 1
    | add x y hx hy =>
      obtain ⟨b, hb⟩ := hx
      obtain ⟨c, hc⟩ := hy
      exact ⟨b + c, by simp only [map_add, Subalgebra.coe_add, hb, hc]⟩
  obtain ⟨b, hb⟩ := h y
  have hb' : algebraMap B (B ⊗[A] F) b = z :=
    hb.trans (congrArg Subtype.val hy)
  refine ⟨b, hb', ?_⟩
  intro c hc
  exact genericAlgebraMap_injective A B F (hc.trans hb'.symm)

/-- Idempotents in the generic fiber lift to unique idempotent sections. -/
theorem existsUnique_idempotent_section [Nontrivial B] (z : B ⊗[A] F) (hz : z * z = z) :
    ∃! b : B, b * b = b ∧ algebraMap B (B ⊗[A] F) b = z := by
  have hIntegral : IsIntegral B z := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by simp), ?_⟩
    simp [pow_two, hz]
  obtain ⟨b, hb, hUnique⟩ := existsUnique_section A B F z hIntegral
  have hIdem : b * b = b := genericAlgebraMap_injective A B F (by
    rw [map_mul, hb, hz])
  exact ⟨b, ⟨hIdem, hb⟩, fun c hc => hUnique c hc.2⟩

end

end ManuscriptAudit.SmoothGenericIntegral

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SmoothGenericIntegral.genericAlgebraMap_injective,
      ``ManuscriptAudit.SmoothGenericIntegral.existsUnique_section,
      ``ManuscriptAudit.SmoothGenericIntegral.existsUnique_idempotent_section] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
