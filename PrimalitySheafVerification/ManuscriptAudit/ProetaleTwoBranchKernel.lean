import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousDirectImageMaps
import PrimalitySheafVerification.ManuscriptAudit.SheafPointwiseKernel

/-! A universally closed surjective map with at most the displayed two branches
has the expected native continuous-function kernel on every chart. -/

namespace ManuscriptAudit.ProetaleTwoBranchKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Y P Z : Scheme.{0}} (p : Y ⟶ Z) (q : P ⟶ Z)
  (b₀ b₁ : P ⟶ Y) (h₀ : b₀ ≫ p = q) (h₁ : b₁ ≫ p = q)

private abbrev project (U : Z.ProEt) := pullback.fst U.hom p

private abbrev fiberScheme (U : Z.ProEt) := pullback U.hom q
private abbrev normScheme (U : Z.ProEt) := pullback U.hom p

/-- Any two distinct points over the same chart point are precisely the two displayed branches. -/
def BranchFibers : Prop :=
  ∀ (U : Z.ProEt) (a b : normScheme p U), project p U a = project p U b →
    a = b ∨ ∃ c : fiberScheme q U,
      (pullbackMap U.hom b₀ h₀ c = a ∧ pullbackMap U.hom b₁ h₁ c = b) ∨
      (pullbackMap U.hom b₀ h₀ c = b ∧ pullbackMap U.hom b₁ h₁ c = a)

variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

/-- The native difference between the two branch restrictions. -/
def difference : functionsOver M p ⟶ functionsOver M q :=
  restriction M b₀ h₀ - restriction M b₁ h₁

theorem diagonal_difference_zero : diagonal M p ≫ difference p q b₀ b₁ h₀ h₁ M = 0 := by
  rw [difference, Preadditive.comp_sub, diagonal_restriction, diagonal_restriction, sub_self]

/-- The native diagonal and two branch maps, with no exactness hypothesis built into the objects. -/
def sequence : ShortComplex (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{1}) :=
  ShortComplex.mk (diagonal M p) (difference p q b₀ b₁ h₀ h₁ M)
    (diagonal_difference_zero p q b₀ b₁ h₀ h₁ M)

variable [UniversallyClosed p] [Surjective p]

private theorem projection_quotient (U : Z.ProEt) : Topology.IsQuotientMap (project p U) :=
  (project p U).isClosedMap.isQuotientMap (project p U).continuous
    (inferInstance : Surjective (project p U)).surj

/-- The native diagonal is pointwise injective. -/
theorem diagonal_injective (U : Z.ProEt) :
    Function.Injective ((diagonal M p).hom.app (op U)) := by
  intro a b h
  change ULift.{1} (C(U.left, M)) at a b
  apply ULift.ext
  apply ContinuousMap.ext
  intro y
  obtain ⟨t, ht⟩ := (projection_quotient p U).surjective y
  have he := congrArg (fun c : ULift.{1} (C(normScheme p U, M)) ↦ c.down t) h
  change a.down (project p U t) = b.down (project p U t) at he
  rwa [ht] at he

/-- If the actual geometric pairs are the displayed branches, the
pointwise difference kernel is exactly the diagonal. -/
theorem exact_on_sections (hFib : BranchFibers p q b₀ b₁ h₀ h₁) (U : Z.ProEt) :
    Function.Exact ((diagonal M p).hom.app (op U)) ((difference p q b₀ b₁ h₀ h₁ M).hom.app (op U)) := by
  intro s
  constructor
  · intro hs
    let s' : C(normScheme p U, M) := s.down
    have hh (c : fiberScheme q U) :
        s' (pullbackMap U.hom b₀ h₀ c) = s' (pullbackMap U.hom b₁ h₁ c) := by
      have h := congrArg (fun t : ULift.{1} (C(fiberScheme q U, M)) ↦ t.down c) hs
      change s' (pullbackMap U.hom b₀ h₀ c) - s' (pullbackMap U.hom b₁ h₁ c) = 0 at h
      exact sub_eq_zero.mp h
    let u : C(normScheme p U, U.left) := ⟨project p U, (project p U).continuous⟩
    have hz : Topology.IsQuotientMap u := projection_quotient p U
    have hf : Function.FactorsThrough s' u := by
      intro a b hab
      rcases hFib U a b hab with rfl | ⟨c, h | h⟩
      · rfl
      · simpa only [h.1, h.2] using hh c
      · simpa only [h.1, h.2] using (hh c).symm
    refine ⟨⟨hz.lift s' hf⟩, ?_⟩
    apply ULift.ext
    exact hz.lift_comp s' hf
  · rintro ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app (op U)) (diagonal_difference_zero p q b₀ b₁ h₀ h₁ M)) x

/-- Native kernel and Epi imply the actual conductor short exact sequence. -/
theorem sequence_shortExact (hFib : BranchFibers p q b₀ b₁ h₀ h₁)
    [Epi (difference p q b₀ b₁ h₀ h₁ M)] :
    (sequence p q b₀ b₁ h₀ h₁ M).ShortExact := by
  let S := sequence p q b₀ b₁ h₀ h₁ M
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    SheafPointwiseKernel.kernel_isLimit S (fun U ↦ diagonal_injective p M U.unop)
      (fun U ↦ exact_on_sections p q b₀ b₁ h₀ h₁ M hFib U.unop)
  letI : Epi S.g := inferInstanceAs (Epi (difference p q b₀ b₁ h₀ h₁ M))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S hKer)
    (mono_of_isLimit_fork hKer) inferInstance

end
end ManuscriptAudit.ProetaleTwoBranchKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleTwoBranchKernel.exact_on_sections,
      ``ManuscriptAudit.ProetaleTwoBranchKernel.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
