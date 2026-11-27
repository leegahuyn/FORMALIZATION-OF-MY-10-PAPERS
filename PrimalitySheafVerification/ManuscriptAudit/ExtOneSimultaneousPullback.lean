import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! Simultaneously pull a countable family of extensions back along
maps from one object. The resulting extension exists whenever that
actual pullback projection is epi. -/

namespace ManuscriptAudit.ExtOneSimultaneousPullback

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (S : ℕ → ShortComplex C)
  [HasProduct (fun n ↦ (S n).X₁)] [HasProduct (fun n ↦ (S n).X₂)] [HasProduct (fun n ↦ (S n).X₃)]
variable {A : C} (a : ∀ n, A ⟶ (S n).X₃)

private abbrev X₁ (n : ℕ) := (S n).X₁
private abbrev X₂ (n : ℕ) := (S n).X₂
private abbrev X₃ (n : ℕ) := (S n).X₃
private abbrev f : (∏ᶜ (X₁ S)) ⟶ ∏ᶜ (X₂ S) :=
  CategoryTheory.Limits.Pi.map (f := X₁ S) (g := X₂ S) (fun n ↦ (S n).f)
private abbrev g : (∏ᶜ (X₂ S)) ⟶ ∏ᶜ (X₃ S) :=
  CategoryTheory.Limits.Pi.map (f := X₂ S) (g := X₃ S) (fun n ↦ (S n).g)
private abbrev b := Pi.lift a

/-- The genuine pullback of the product of right arrows along the given tuple. -/
abbrev object := pullback (b S a) (g S)

abbrev projection : object S a ⟶ A := pullback.fst (b S a) (g S)

abbrev toProduct : object S a ⟶ ∏ᶜ (X₂ S) := pullback.snd (b S a) (g S)

private theorem product_comp_zero : f S ≫ g S = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.map_π, Pi.map_π_assoc, ShortComplex.zero, comp_zero, zero_comp]

private def inclusion : (∏ᶜ (X₁ S)) ⟶ object S a :=
  pullback.lift 0 (f S) (by rw [zero_comp, product_comp_zero])

private theorem inclusion_fst : inclusion S a ≫ projection S a = 0 :=
  pullback.lift_fst _ _ _

private theorem inclusion_snd : inclusion S a ≫ toProduct S a = f S :=
  pullback.lift_snd _ _ _

/-- The product of the kernels and the actual simultaneous pullback projection. -/
def sequence : ShortComplex C := ShortComplex.mk (inclusion S a) (projection S a) (inclusion_fst S a)

variable (hS : ∀ n, (S n).ShortExact)

include hS in
private theorem productFirst_mono : Mono (f S) := by
  constructor
  intro T x y h
  apply Pi.hom_ext
  intro n
  letI := (hS n).mono_f
  apply (cancel_mono (S n).f).mp
  simpa only [Category.assoc, Pi.map_π] using congrArg (fun t ↦ t ≫ Pi.π (X₂ S) n) h

include hS in
private theorem first_mono : Mono (inclusion S a) := by
  letI : Mono (f S) := productFirst_mono S hS
  haveI : Mono (inclusion S a ≫ toProduct S a) := by rw [inclusion_snd]; infer_instance
  exact mono_of_mono _ (toProduct S a)

include hS in
private def firstIsKernel :
    IsLimit (KernelFork.ofι (inclusion S a) (inclusion_fst S a)) := by
  letI : Mono (inclusion S a) := first_mono S a hS
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  have hw : k ≫ toProduct S a ≫ g S = 0 := by
    rw [← pullback.condition, ← Category.assoc, hk, zero_comp]
  have hz (n : ℕ) : (k ≫ toProduct S a ≫ Pi.π (X₂ S) n) ≫ (S n).g = 0 := by
    simpa only [Category.assoc, Pi.map_π, zero_comp] using
      congrArg (fun t ↦ t ≫ Pi.π (X₃ S) n) hw
  let v (n : ℕ) := KernelFork.IsLimit.lift' (hS n).fIsKernel
    (k ≫ toProduct S a ≫ Pi.π (X₂ S) n) (hz n)
  let t (n : ℕ) := (v n).val
  have ht (n : ℕ) : t n ≫ (S n).f = k ≫ toProduct S a ≫ Pi.π (X₂ S) n := (v n).property
  refine ⟨Pi.lift t, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, inclusion_fst, comp_zero, hk]
  · rw [Category.assoc, inclusion_snd]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.map_π, Pi.lift_π_assoc, ht]

include hS in
/-- Local surjectivity of the one actual projection suffices for a simultaneous extension. -/
theorem sequence_shortExact [Epi (projection S a)] : (sequence S a).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel (sequence S a) (firstIsKernel S a hS))
    (first_mono S a hS) (inferInstanceAs (Epi (projection S a)))

/-- Projection onto each original short complex. -/
def compare (n : ℕ) : sequence S a ⟶ S n where
  τ₁ := Pi.π (X₁ S) n
  τ₂ := toProduct S a ≫ Pi.π (X₂ S) n
  τ₃ := a n
  comm₁₂ := by
    change Pi.π (X₁ S) n ≫ (S n).f = inclusion S a ≫ toProduct S a ≫ Pi.π (X₂ S) n
    rw [← Category.assoc, inclusion_snd, Pi.map_π]
  comm₂₃ := by
    change (toProduct S a ≫ Pi.π (X₂ S) n) ≫ (S n).g = projection S a ≫ a n
    have hg : g S ≫ Pi.π (X₃ S) n = Pi.π (X₂ S) n ≫ (S n).g :=
      Pi.map_π (fun i ↦ (S i).g) n
    calc
      _ = (toProduct S a ≫ g S) ≫ Pi.π (X₃ S) n := by simp only [Category.assoc, hg]
      _ = (projection S a ≫ b S a) ≫ Pi.π (X₃ S) n :=
        congrArg (fun q ↦ q ≫ Pi.π (X₃ S) n) (pullback.condition (f := b S a) (g := g S)).symm
      _ = _ := by rw [Category.assoc, Pi.lift_π]

/-- A single native product Ext class projects to the pullback of every input extension. -/
theorem extension_project [Epi (projection S a)] (n : ℕ) :
    (sequence_shortExact S a hS).extClass.comp (Ext.mk₀ (Pi.π (X₁ S) n)) (add_zero 1) =
      (Ext.mk₀ (a n)).comp (hS n).extClass (zero_add 1) :=
  (sequence_shortExact S a hS).extClass_naturality (hS n) (compare S a n)

end
end ManuscriptAudit.ExtOneSimultaneousPullback

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ExtOneSimultaneousPullback.extension_project
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
