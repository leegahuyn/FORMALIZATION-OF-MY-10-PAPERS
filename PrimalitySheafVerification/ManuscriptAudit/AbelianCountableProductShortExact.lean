import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! Countable product sequences and the product of injective objects. -/

namespace ManuscriptAudit.AbelianCountableProductShortExact

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C]
variable [HasLimitsOfShape (Discrete ℕ) C]

def mapProduct {F G : ℕ → C} (f : ∀ n, F n ⟶ G n) :
    (∏ᶜ F) ⟶ ∏ᶜ G :=
  Pi.lift (fun n => Pi.π F n ≫ f n)

@[reassoc]
theorem mapProduct_π {F G : ℕ → C} (f : ∀ n, F n ⟶ G n) (n : ℕ) :
    mapProduct f ≫ Pi.π G n = Pi.π F n ≫ f n := by
  unfold mapProduct
  rw [Pi.lift_π]

variable [Abelian C] (S : ℕ → ShortComplex C)

abbrev leftTerms (n : ℕ) := (S n).X₁
abbrev middleTerms (n : ℕ) := (S n).X₂
abbrev rightTerms (n : ℕ) := (S n).X₃

def product : ShortComplex C :=
  ShortComplex.mk (mapProduct (fun n => (S n).f)) (mapProduct (fun n => (S n).g)) (by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, mapProduct_π, ← Category.assoc, mapProduct_π, Category.assoc,
      (S n).zero, comp_zero, zero_comp])

def projection (n : ℕ) : product S ⟶ S n where
  τ₁ := Pi.π (leftTerms S) n
  τ₂ := Pi.π (middleTerms S) n
  τ₃ := Pi.π (rightTerms S) n
  comm₁₂ := by
    change Pi.π (leftTerms S) n ≫ (S n).f =
      mapProduct (fun i => (S i).f) ≫ Pi.π (middleTerms S) n
    exact (mapProduct_π (F := leftTerms S) (G := middleTerms S) (fun i => (S i).f) n).symm
  comm₂₃ := by
    change Pi.π (middleTerms S) n ≫ (S n).g =
      mapProduct (fun i => (S i).g) ≫ Pi.π (rightTerms S) n
    exact (mapProduct_π (F := middleTerms S) (G := rightTerms S) (fun i => (S i).g) n).symm

theorem product_mono (h : ∀ n, (S n).ShortExact) : Mono (product S).f := by
  constructor
  intro W a b hab
  apply Pi.hom_ext
  intro n
  letI : Mono (S n).f := (h n).mono_f
  apply (cancel_mono ((S n).f)).mp
  change (a ≫ (projection S n).τ₁) ≫ (S n).f =
    (b ≫ (projection S n).τ₁) ≫ (S n).f
  calc
    _ = (a ≫ (product S).f) ≫ (projection S n).τ₂ :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun q => a ≫ q) (projection S n).comm₁₂).trans (Category.assoc _ _ _).symm)
    _ = (b ≫ (product S).f) ≫ (projection S n).τ₂ :=
      congrArg (fun q => q ≫ (projection S n).τ₂) hab
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (fun q => b ≫ q) (projection S n).comm₁₂.symm).trans (Category.assoc _ _ _).symm)

theorem product_shortExact (h : ∀ n, (S n).ShortExact) (hEpi : Epi (product S).g) :
    (product S).ShortExact := by
  letI : Mono (product S).f := product_mono S h
  have hK : IsLimit (KernelFork.ofι (product S).f (product S).zero) := by
    refine KernelFork.IsLimit.ofι' _ _ (fun {W} a ha => ?_)
    have hComp (n : ℕ) : (a ≫ Pi.π (middleTerms S) n) ≫ (S n).g = 0 := by
      change (a ≫ (projection S n).τ₂) ≫ (S n).g = 0
      calc
        _ = (a ≫ (product S).g) ≫ (projection S n).τ₃ :=
          (Category.assoc _ _ _).trans
            ((congrArg (fun q => a ≫ q) (projection S n).comm₂₃).trans (Category.assoc _ _ _).symm)
        _ = 0 := by rw [ha, zero_comp]
    let l (n : ℕ) := (h n).fIsKernel.lift (KernelFork.ofι _ (hComp n))
    have hl (n : ℕ) : l n ≫ (S n).f = a ≫ Pi.π (middleTerms S) n :=
      (h n).fIsKernel.fac (KernelFork.ofι _ (hComp n)) WalkingParallelPair.zero
    refine ⟨Pi.lift l, ?_⟩
    apply Pi.hom_ext
    intro n
    change (Pi.lift l ≫ mapProduct (fun i => (S i).f)) ≫ Pi.π (middleTerms S) n =
      a ≫ Pi.π (middleTerms S) n
    rw [Category.assoc, mapProduct_π, ← Category.assoc, Pi.lift_π, hl]
  exact ShortComplex.ShortExact.mk' ((product S).exact_of_f_is_kernel hK)
    (product_mono S h) hEpi

theorem product_injective (I : ℕ → C) (h : ∀ n, Injective (I n)) :
    Injective (∏ᶜ I) := by
  constructor
  intro X Y a f hf
  let lift (n : ℕ) : Y ⟶ I n := by
    letI := h n
    exact Injective.factorThru (a ≫ Pi.π I n) f
  refine ⟨Pi.lift lift, ?_⟩
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, Pi.lift_π]
  letI := h n
  exact Injective.comp_factorThru (a ≫ Pi.π I n) f

end
end ManuscriptAudit.AbelianCountableProductShortExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AbelianCountableProductShortExact.product_shortExact,
      ``ManuscriptAudit.AbelianCountableProductShortExact.product_injective] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
