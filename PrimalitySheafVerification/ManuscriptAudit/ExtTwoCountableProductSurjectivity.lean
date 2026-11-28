import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AbelianCountableProductShortExact
import PrimalitySheafVerification.ManuscriptAudit.ExtOneCountableProductSurjectivity

/-! One dimension shift realizes every tuple of genuine degree-two Ext classes
in the actual countable product under the same exactness hypothesis. -/

namespace ManuscriptAudit.ExtTwoCountableProductSurjectivity

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AbelianCountableProductShortExact

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
  [HasLimitsOfShape (Discrete ℕ) C]

theorem projections_jointly_surjective
    (hProducts : ∀ (F G : ℕ → C) (f : ∀ n, F n ⟶ G n),
      (∀ n, Epi (f n)) → Epi (mapProduct f))
    (F : ℕ → C) (B : C) :
    Function.Surjective (fun x : Ext B (∏ᶜ F) 2 =>
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
  have hProducts' (G H : ℕ → C) (f : ∀ n, G n ⟶ H n) (hf : ∀ n, Epi (f n)) :
      Epi (CategoryTheory.Limits.Pi.map (f := G) (g := H) f) := by
    have he : CategoryTheory.Limits.Pi.map (f := G) (g := H) f = mapProduct f := by
      apply Pi.hom_ext
      intro n
      rw [CategoryTheory.Limits.Pi.map_π, mapProduct_π]
    rw [he]
    exact hProducts G H f hf
  intro x
  have hLift (n : ℕ) : ∃ y : Ext B (Q n) 1, y.comp (hS n).extClass rfl = x n := by
    have hzero : (x n).comp (Ext.mk₀ (S n).f) (add_zero 2) = 0 :=
      Ext.eq_zero_of_injective (show Ext B (I n) 2 from
        (x n).comp (Ext.mk₀ (S n).f) (add_zero 2))
    exact Ext.covariant_sequence_exact₁ (X := B) (hS n) (x n) hzero (show 1+1=2 by rfl)
  choose y hy using hLift
  obtain ⟨a, ha⟩ := ExtOneCountableProductSurjectivity.projectionMap_surjective hProducts' Q B y
  refine ⟨a.comp hT.extClass rfl, ?_⟩
  funext n
  have haₙ : a.comp (Ext.mk₀ (Pi.π Q n)) (add_zero 1) = y n := congrFun ha n
  change (a.comp hT.extClass rfl).comp (Ext.mk₀ (Pi.π F n)) (add_zero 2) = x n
  rw [Ext.comp_assoc_of_third_deg_zero]
  change a.comp (hT.extClass.comp (Ext.mk₀ (projection S n).τ₁) (add_zero 1)) rfl = x n
  rw [hT.extClass_naturality (hS n) (projection S n), ← Ext.comp_assoc_of_second_deg_zero]
  change (a.comp (Ext.mk₀ (Pi.π Q n)) (add_zero 1)).comp (hS n).extClass rfl = x n
  rw [haₙ, hy]

end
end ManuscriptAudit.ExtTwoCountableProductSurjectivity

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtTwoCountableProductSurjectivity.projections_jointly_surjective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
