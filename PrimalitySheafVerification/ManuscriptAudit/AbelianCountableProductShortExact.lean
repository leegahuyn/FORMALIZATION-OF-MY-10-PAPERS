import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! Countable product sequences and the product of injective objects. -/

namespace ManuscriptAudit.AbelianCountableProductShortExact

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [HasLimitsOfShape (Discrete ℕ) C]

variable (S : ℕ → ShortComplex C)

abbrev leftTerms (n : ℕ) := (S n).X₁
abbrev middleTerms (n : ℕ) := (S n).X₂
abbrev rightTerms (n : ℕ) := (S n).X₃

def product : ShortComplex C :=
  ShortComplex.mk (Pi.map (fun n => (S n).f)) (Pi.map (fun n => (S n).g)) (by
    apply Pi.hom_ext
    intro n
    rw [Category.assoc, Pi.map_π, ← Category.assoc, Pi.map_π, Category.assoc,
      (S n).zero, comp_zero, zero_comp])

def projection (n : ℕ) : product S ⟶ S n where
  τ₁ := Pi.π (leftTerms S) n
  τ₂ := Pi.π (middleTerms S) n
  τ₃ := Pi.π (rightTerms S) n
  comm₁₂ := by
    change Pi.π (leftTerms S) n ≫ (S n).f =
      Pi.map (fun i => (S i).f) ≫ Pi.π (middleTerms S) n
    exact (Pi.map_π _ _).symm
  comm₂₃ := by
    change Pi.π (middleTerms S) n ≫ (S n).g =
      Pi.map (fun i => (S i).g) ≫ Pi.π (rightTerms S) n
    exact (Pi.map_π _ _).symm

theorem product_mono (h : ∀ n, (S n).ShortExact) : Mono (product S).f := by
  constructor
  intro W a b hab
  apply Pi.hom_ext
  intro n
  letI : Mono (S n).f := (h n).mono_f
  apply (cancel_mono ((S n).f)).mp
  have ht := congrArg (fun t => t ≫ Pi.π (middleTerms S) n) hab
  change (a ≫ Pi.map (fun i => (S i).f)) ≫ Pi.π (middleTerms S) n =
    (b ≫ Pi.map (fun i => (S i).f)) ≫ Pi.π (middleTerms S) n at ht
  simpa only [Category.assoc, Pi.map_π] using ht

theorem product_shortExact (h : ∀ n, (S n).ShortExact) (hEpi : Epi (product S).g) :
    (product S).ShortExact := by
  letI : Mono (product S).f := product_mono S h
  have hK : IsLimit (KernelFork.ofι (product S).f (product S).zero) := by
    refine KernelFork.IsLimit.ofι' _ _ (fun {W} a ha => ?_)
    have hComp (n : ℕ) : (a ≫ Pi.π (middleTerms S) n) ≫ (S n).g = 0 := by
      have he := congrArg (fun t => t ≫ Pi.π (rightTerms S) n) ha
      change (a ≫ Pi.map (fun i => (S i).g)) ≫ Pi.π (rightTerms S) n = _ at he
      simpa only [Category.assoc, Pi.map_π, zero_comp] using he
    let l (n : ℕ) := (h n).fIsKernel.lift (KernelFork.ofι _ (hComp n))
    have hl (n : ℕ) : l n ≫ (S n).f = a ≫ Pi.π (middleTerms S) n :=
      (h n).fIsKernel.fac (KernelFork.ofι _ (hComp n)) WalkingParallelPair.zero
    refine ⟨Pi.lift l, ?_⟩
    apply Pi.hom_ext
    intro n
    change (Pi.lift l ≫ Pi.map (fun i => (S i).f)) ≫ Pi.π (middleTerms S) n =
      a ≫ Pi.π (middleTerms S) n
    rw [Category.assoc, Pi.map_π, ← Category.assoc, Pi.lift_π, hl]
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
