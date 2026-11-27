import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AbelianCountableProductShortExact
import PrimalitySheafVerification.ManuscriptAudit.ExtOneProduct
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-! Detection on the actual degree-two Ext of a countable product. -/

namespace ManuscriptAudit.ExtTwoCountableProductDetection

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AbelianCountableProductShortExact

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable [HasLimitsOfShape (Discrete ℕ) C]

private def projectionMap (F : ℕ → C) (B : C) :
    Ext B (∏ᶜ F) 2 →+ ∀ n, Ext B (F n) 2 where
  toFun x n := x.comp (Ext.mk₀ (Pi.π F n)) (add_zero 2)
  map_zero' := by
    funext n
    simp
  map_add' x y := by
    funext n
    exact Ext.add_comp ..

/-- Exact countable products give joint detection in degree two by one dimension shift. -/
theorem projections_jointly_injective [EnoughInjectives C]
    (hProducts : ∀ (F G : ℕ → C) (f : ∀ n, F n ⟶ G n),
      (∀ n, Epi (f n)) → Epi (mapProduct f))
    (F : ℕ → C) (B : C) :
    Function.Injective (fun x : Ext B (∏ᶜ F) 2 =>
      fun n => x.comp (Ext.mk₀ (Pi.π F n)) (add_zero 2)) := by
  let I (n : ℕ) := Injective.under (F n)
  let i (n : ℕ) : F n ⟶ I n := Injective.ι (F n)
  let Q (n : ℕ) := cokernel (i n)
  let S (n : ℕ) : ShortComplex C :=
    ShortComplex.mk (i n) (cokernel.π (i n)) (cokernel.condition (i n))
  have hS (n : ℕ) : (S n).ShortExact :=
    ShortComplex.ShortExact.mk'
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (i n)))
      (inferInstanceAs (Mono (Injective.ι (F n))))
      (inferInstanceAs (Epi (cokernel.π (i n))))
  let T := product S
  have hT : T.ShortExact := product_shortExact S hS
    (hProducts I Q (fun n => cokernel.π (i n)) (fun n => (hS n).epi_g))
  letI : Injective (∏ᶜ I) := product_injective I (fun _ => inferInstance)
  change Function.Injective (projectionMap F B)
  intro x x' hx
  apply sub_eq_zero.mp
  have hx₀ : projectionMap F B (x-x') = 0 := by rw [map_sub, hx, sub_self]
  let z := x-x'
  have hz : z.comp (Ext.mk₀ T.f) (add_zero 2) = 0 :=
    Ext.eq_zero_of_injective (show Ext B (∏ᶜ I) 2 from z.comp (Ext.mk₀ T.f) (add_zero 2))
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (X := B) hT z hz (show 1+1=2 by rfl)
  have hy₀ : y = 0 := by
    apply ExtOneProduct.projectionMap_injective Q B
    funext n
    change y.comp (Ext.mk₀ (Pi.π Q n)) (add_zero 1) =
      (0 : Ext B (∏ᶜ Q) 1).comp (Ext.mk₀ (Pi.π Q n)) (add_zero 1)
    rw [Ext.zero_comp]
    let y' := y.comp (Ext.mk₀ (Pi.π Q n)) (add_zero 1)
    have hProj : z.comp (Ext.mk₀ (Pi.π F n)) (add_zero 2) = 0 := congrFun hx₀ n
    have hBoundary : y'.comp (hS n).extClass rfl = 0 := by
      have hNat := hT.extClass_naturality (hS n) (projection S n)
      have eq : (y.comp hT.extClass rfl).comp (Ext.mk₀ (Pi.π F n)) (add_zero 2) =
          y'.comp (hS n).extClass rfl := by
        rw [Ext.comp_assoc_of_third_deg_zero]
        change y.comp (hT.extClass.comp (Ext.mk₀ (projection S n).τ₁) (add_zero 1)) rfl =
          (y.comp (Ext.mk₀ (projection S n).τ₃) (add_zero 1)).comp (hS n).extClass rfl
        rw [hNat, ← Ext.comp_assoc_of_second_deg_zero]
      rw [← eq, hy]
      exact hProj
    have hExact := Ext.covariant_sequence_exact₃' B (hS n) 1 2 rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at hExact
    obtain ⟨w, hw⟩ := (hExact y').1 hBoundary
    have hW : w = 0 := Ext.eq_zero_of_injective (show Ext B (I n) 1 from w)
    rw [hW, Ext.zero_comp] at hw
    exact hw.symm
  rw [hy₀, Ext.zero_comp] at hy
  exact hy.symm

end
end ManuscriptAudit.ExtTwoCountableProductDetection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtTwoCountableProductDetection.projections_jointly_injective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
