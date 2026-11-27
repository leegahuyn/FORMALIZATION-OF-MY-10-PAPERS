import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ExtOneProduct
import PrimalitySheafVerification.ManuscriptAudit.ExtOneSimultaneousPullback

/-! With exact countable products, every family of genuine degree-one
extension classes comes from a single extension by the product. -/

namespace ManuscriptAudit.ExtOneCountableProductSurjectivity

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [EnoughInjectives C]
  [HasLimitsOfShape (Discrete ℕ) C]

/-- A simultaneous genuine extension realizes every tuple of component classes. -/
theorem projectionMap_surjective
    (hProducts : ∀ (F G : ℕ → C) (f : ∀ n, F n ⟶ G n),
      (∀ n, Epi (f n)) → Epi (CategoryTheory.Limits.Pi.map (f := F) (g := G) f))
    (B : ℕ → C) (A : C) : Function.Surjective (ExtOneProduct.projectionMap B A) := by
  intro x
  choose E i p zero hS hx using fun n => ExtOneAdjunction.exists_extension (x n)
  let S (n : ℕ) : ShortComplex C := ShortComplex.mk (i n) (p n) (zero n)
  let G : ℕ → C := fun _ => A
  let a (n : ℕ) : A ⟶ (S n).X₃ := 𝟙 A
  letI : Epi (CategoryTheory.Limits.Pi.map (f := E) (g := G) p) :=
    hProducts E G p (fun n => (hS n).epi_g)
  letI : Epi (ExtOneSimultaneousPullback.projection S a) := by
    change Epi (pullback.fst (Pi.lift a) (CategoryTheory.Limits.Pi.map (f := E) (g := G) p))
    infer_instance
  refine ⟨(ExtOneSimultaneousPullback.sequence_shortExact S a hS).extClass, ?_⟩
  funext n
  change (ExtOneSimultaneousPullback.sequence_shortExact S a hS).extClass.comp
    (Ext.mk₀ (Pi.π B n)) (add_zero 1) = x n
  calc
    _ = (Ext.mk₀ (a n)).comp (hS n).extClass (zero_add 1) :=
      ExtOneSimultaneousPullback.extension_project S a hS n
    _ = (hS n).extClass := by simp [a]
    _ = _ := hx n

/-- Degree-one Ext commutes with the actual countable product under exactness. -/
def projectionEquiv
    (hProducts : ∀ (F G : ℕ → C) (f : ∀ n, F n ⟶ G n),
      (∀ n, Epi (f n)) → Epi (CategoryTheory.Limits.Pi.map (f := F) (g := G) f))
    (B : ℕ → C) (A : C) : Ext A (∏ᶜ B) 1 ≃+ ∀ n, Ext A (B n) 1 :=
  AddEquiv.ofBijective (ExtOneProduct.projectionMap B A)
    ⟨ExtOneProduct.projectionMap_injective B A, projectionMap_surjective hProducts B A⟩

end
end ManuscriptAudit.ExtOneCountableProductSurjectivity

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ExtOneCountableProductSurjectivity.projectionMap_surjective,
      ``ManuscriptAudit.ExtOneCountableProductSurjectivity.projectionEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
