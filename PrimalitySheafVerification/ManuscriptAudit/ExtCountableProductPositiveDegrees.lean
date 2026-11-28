import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtTwoCountableProductSurjectivity
import PrimalitySheafVerification.ManuscriptAudit.ExtTwoCountableProductDetection

/-! Actual countable product coordinates in every positive Ext degree. -/

namespace ManuscriptAudit.ExtCountableProductPositiveDegrees
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AbelianCountableProductShortExact

universe u v w
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
  [HasLimitsOfShape (Discrete ℕ) C]

def projectionMap (F : ℕ → C) (B : C) (d : ℕ) :
    Ext B (∏ᶜ F) d →+ ∀ n, Ext B (F n) d where
  toFun x n := x.comp (Ext.mk₀ (Pi.π F n)) (add_zero d)
  map_zero' := by
    funext n
    simp
  map_add' x y := by
    funext n
    exact Ext.add_comp ..

theorem projections_jointly_bijective
    (hProducts : ∀ (F G : ℕ → C) (f : ∀ n, F n ⟶ G n),
      (∀ n, Epi (f n)) → Epi (mapProduct f))
    (F : ℕ → C) (B : C) (d : ℕ) :
    Function.Bijective (projectionMap F B (d + 1)) := by
  induction d generalizing F with
  | zero =>
      have hProducts' (G H : ℕ → C) (f : ∀ n, G n ⟶ H n) (hf : ∀ n, Epi (f n)) :
          Epi (Pi.map (f := G) (g := H) f) := by
        have h : Pi.map (f := G) (g := H) f = mapProduct f := by
          apply Pi.hom_ext
          intro n
          rw [Pi.map_π, mapProduct_π]
        rw [h]
        exact hProducts G H f hf
      exact (ExtOneCountableProductSurjectivity.projectionEquiv hProducts' F B).bijective
  | succ d ih =>
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
      have hNatur (a : Ext B (∏ᶜ Q) (d+1)) (n : ℕ) :
          (projectionMap F B (d+2) (a.comp hT.extClass rfl)) n =
            ((projectionMap Q B (d+1) a) n).comp (hS n).extClass rfl := by
        change (a.comp hT.extClass rfl).comp (Ext.mk₀ (Pi.π F n)) (add_zero (d+2)) =
          (a.comp (Ext.mk₀ (Pi.π Q n)) (add_zero (d+1))).comp (hS n).extClass rfl
        rw [Ext.comp_assoc_of_third_deg_zero]
        change a.comp (hT.extClass.comp (Ext.mk₀ (projection S n).τ₁) (add_zero 1)) rfl =
          (a.comp (Ext.mk₀ (projection S n).τ₃) (add_zero (d+1))).comp (hS n).extClass rfl
        rw [hT.extClass_naturality (hS n) (projection S n), ← Ext.comp_assoc_of_second_deg_zero]
      constructor
      · intro x x' hx
        apply sub_eq_zero.mp
        let z := x-x'
        have hz : projectionMap F B (d+2) z = 0 := by
          change projectionMap F B (d+2) (x-x') = 0
          rw [map_sub, hx, sub_self]
        have hzI : z.comp (Ext.mk₀ T.f) (add_zero (d+2)) = 0 :=
          Ext.eq_zero_of_injective (show Ext B (∏ᶜ I) (d+2) from
            z.comp (Ext.mk₀ T.f) (add_zero (d+2)))
        obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ (X := B) hT z hzI
          (show d+1+1 = d+2 by rfl)
        have ha₀ : a = 0 := by
          apply (ih Q).1
          rw [map_zero]
          funext n
          let y := (projectionMap Q B (d+1) a) n
          have hy : y.comp (hS n).extClass (show d+1+1 = d+2 by rfl) = 0 := by
            calc
              _ = (projectionMap F B (d+2) (a.comp hT.extClass rfl)) n := (hNatur a n).symm
              _ = (projectionMap F B (d+2) z) n := by rw [ha]
              _ = _ := congrFun hz n
          obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ B (hS n) y
            (show d+1+1 = d+2 by rfl) hy
          have hw₀ : w = 0 := Ext.eq_zero_of_injective (show Ext B (I n) (d+1) from w)
          rw [hw₀, Ext.zero_comp] at hw
          exact hw.symm
        rw [ha₀, Ext.zero_comp] at ha
        exact ha.symm
      · intro x
        have hLift (n : ℕ) : ∃ y : Ext B (Q n) (d+1), y.comp (hS n).extClass rfl = x n := by
          have hZ : (x n).comp (Ext.mk₀ (S n).f) (add_zero (d+2)) = 0 :=
            Ext.eq_zero_of_injective (show Ext B (I n) (d+2) from
              (x n).comp (Ext.mk₀ (S n).f) (add_zero (d+2)))
          exact Ext.covariant_sequence_exact₁ (X := B) (hS n) (x n) hZ
            (show d+1+1 = d+2 by rfl)
        choose y hy using hLift
        obtain ⟨a, ha⟩ := (ih Q).2 y
        refine ⟨a.comp hT.extClass rfl, ?_⟩
        funext n
        rw [hNatur, congrFun ha n, hy n]

end
end ManuscriptAudit.ExtCountableProductPositiveDegrees

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtCountableProductPositiveDegrees.projections_jointly_bijective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
