import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerBoundaryNative

/-! Power maps induce actual morphisms of the native Kummer sequences,
preserving the boundary of each fixed global unit. -/

namespace ManuscriptAudit.ProetaleKummerKernelTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (sequence sequence_shortExact)
open ProetaleUnitSheaf (unitSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

theorem power_comp (a b : ℕ) : power X a ≫ power X b = power X (a * b) := by
  unfold power
  rw [Preadditive.comp_nsmul, Category.comp_id, smul_smul, Nat.mul_comm b a]

variable (ℓ n : ℕ)

private theorem power_comp_successor :
    power X ℓ ≫ power X (ℓ ^ n) = power X (ℓ ^ (n + 1)) := by
  rw [power_comp, Nat.mul_comm ℓ (ℓ ^ n), ← pow_succ]

/-- The actual power morphism between the categorical Kummer kernels. -/
def kernelTransition : kernel (power X (ℓ ^ (n + 1))) ⟶ kernel (power X (ℓ ^ n)) :=
  kernel.lift (power X (ℓ ^ n)) (kernel.ι (power X (ℓ ^ (n + 1))) ≫ power X ℓ)
    (by rw [Category.assoc, power_comp_successor, kernel.condition])

theorem kernelTransition_ι :
    kernelTransition X ℓ n ≫ kernel.ι (power X (ℓ ^ n)) =
      kernel.ι (power X (ℓ ^ (n + 1))) ≫ power X ℓ :=
  kernel.lift_ι _ _ _

/-- The actual arrow of short complexes uses power on the middle and the identity on the right. -/
def sequenceTransition : sequence X (ℓ ^ (n + 1)) ⟶ sequence X (ℓ ^ n) where
  τ₁ := kernelTransition X ℓ n
  τ₂ := power X ℓ
  τ₃ := 𝟙 (unitSheaf X)
  comm₁₂ := kernelTransition_ι X ℓ n
  comm₂₃ := by
    change power X ℓ ≫ power X (ℓ ^ n) = power X (ℓ ^ (n + 1)) ≫ 𝟙 _
    exact (power_comp_successor X ℓ n).trans (Category.comp_id _).symm

private abbrev integers :=
  (constantSheaf (J X) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))

variable {X}
variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))

/-- The native boundary taken in the actual categorical kernel, before trivializing roots. -/
abbrev kernelBoundary (d : ℕ) [NeZero d] [NeZero (d : K)] :
    Sheaf.H (unitSheaf X) 0 →+ Sheaf.H (kernel (power X d)) 1 :=
  (sequence_shortExact k d).extClass.postcomp (integers X) (show 0 + 1 = 1 by rfl)

/-- Reducing an actual Kummer class in the kernel preserves the fixed unit defining it. -/
theorem kernelBoundary_transition [Fact ℓ.Prime] [NeZero (ℓ : K)]
    (u : Sheaf.H (unitSheaf X) 0) :
    haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (show ℓ.Prime from Fact.out).ne_zero⟩
    haveI : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (show ℓ.Prime from Fact.out).ne_zero⟩
    haveI : NeZero ((ℓ ^ n : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ (NeZero.ne (ℓ : K))⟩
    haveI : NeZero ((ℓ ^ (n + 1) : ℕ) : K) := ⟨by rw [Nat.cast_pow]; exact pow_ne_zero _ (NeZero.ne (ℓ : K))⟩
    Sheaf.H.map (kernelTransition X ℓ n) 1 (kernelBoundary k (ℓ ^ (n + 1)) u) =
      kernelBoundary k (ℓ ^ n) u := by
  let h := sequence_shortExact k (ℓ ^ (n + 1))
  let h' := sequence_shortExact k (ℓ ^ n)
  let f := sequenceTransition X ℓ n
  have ht := h.extClass_naturality h' f
  change h.extClass.comp (Ext.mk₀ (kernelTransition X ℓ n)) rfl =
    (Ext.mk₀ (𝟙 (unitSheaf X))).comp h'.extClass rfl at ht
  change (u.comp h.extClass rfl).comp (Ext.mk₀ (kernelTransition X ℓ n)) rfl =
    u.comp h'.extClass rfl
  rw [Ext.comp_assoc_of_third_deg_zero, ht, Ext.mk₀_id_comp]

end
end ManuscriptAudit.ProetaleKummerKernelTransition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerKernelTransition.power_comp,
      ``ManuscriptAudit.ProetaleKummerKernelTransition.kernelTransition_ι,
      ``ManuscriptAudit.ProetaleKummerKernelTransition.sequenceTransition,
      ``ManuscriptAudit.ProetaleKummerKernelTransition.kernelBoundary_transition] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
