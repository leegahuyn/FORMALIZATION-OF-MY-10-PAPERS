import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.EpiMono
import PrimalitySheafVerification.ManuscriptAudit.ProetaleBranchBinaryLabelling
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedSupportLocalConstants

/-! A native covering lift of the binary label 1 implies epimorphy of
the actual branch difference for all discrete abelian coefficients. -/

namespace ManuscriptAudit.ProetaleBranchDifferenceEpi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleContinuousDirectImageMaps ProetaleTwoBranchKernel
open ProetaleBranchBinaryLabelling ProetaleClosedSupportLocalConstants

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance binaryTopology : TopologicalSpace Binary := ⊥
local instance binaryDiscrete : DiscreteTopology Binary := ⟨rfl⟩

variable {N P X : Scheme.{0}} {p : N ⟶ X} {q : P ⟶ X} [IsClosedImmersion q]
  (b₀ b₁ : P ⟶ N) (h₀ : b₀ ≫ p = q) (h₁ : b₁ ≫ p = q)
  (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev J := Scheme.ProEt.topology X

/-- The constant 1 on the displayed native closed conductor. -/
def oneSection (U : X.ProEt) : (functionsOver Binary q).obj.obj (op U) :=
  ⟨ContinuousMap.const (↥(pullback U.hom q : Scheme.{0})) 1⟩

theorem oneSection_restrict {U V : X.ProEt} (f : U ⟶ V) :
    (functionsOver Binary q).obj.map f.op (oneSection (q := q) V) = oneSection (q := q) U := by
  apply ULift.ext
  exact ContinuousMap.ext (fun _ ↦ rfl)

set_option maxHeartbeats 2200000 in
/-- An actual binary separator on one chart gives local lifts of every
discrete-valued function on that chart's closed support. -/
theorem image_mem_with_separator (U : X.ProEt)
    (s : (functionsOver M q).obj.obj (op U)) (b : (functionsOver Binary p).obj.obj (op U))
    (hb : (binaryDifference b₀ b₁ h₀ h₁).hom.app (op U) b = oneSection (q := q) U) :
    Presheaf.imageSieve (difference p q b₀ b₁ h₀ h₁ M).hom s ∈ J (X := X) U := by
  classical
  let P₀ := positiveTrace b₀ h₀
  let u := P₀.hom.app (op U) b
  let H := functionsOver (M × Binary) q
  let s' : C(pullback U.hom q, M) := s.down
  let u' : C(pullback U.hom q, Binary) := u.down
  let t : H.obj.obj (op U) := ⟨s'.prodMk u'⟩
  choose W hW c hc using fun x : U.left ↦
    exists_open_restriction_const q (M × Binary) U t x
  let V (x : U.left) := openObject U (W x)
  let f (x : U.left) : V x ⟶ U := openArrow U (W x)
  have hCov : Sieve.ofArrows V f ∈ J (X := X) U := by
    apply Precoverage.generate_mem_toGrothendieck
    change (Presieve.ofArrows V f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
      Scheme.proetalePrecoverage U.left
    rw [Presieve.map_ofArrows]
    apply Scheme.etalePrecoverage_le_proetalePrecoverage _
    change Presieve.ofArrows (fun x ↦ (W x).toScheme) (fun x ↦ (W x).ι) ∈
      Scheme.precoverage @Etale U.left
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
      ⟨fun x ↦ ⟨x, ⟨x, hW x⟩, rfl⟩, fun _ ↦ inferInstance⟩
  apply (J (X := X)).superset_covering _ hCov
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨x⟩
  let v := f x
  let b' := (functionsOver Binary p).obj.map v.op b
  have hVal : (functionsOver M q).obj.map v.op s =
      ⟨ContinuousMap.const (↥(pullback (V x).hom q : Scheme.{0})) (c x).1⟩ := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro a
    exact congrArg (fun t : ULift.{1} (C(pullback (V x).hom q, M × Binary)) ↦ (t.down a).1) (hc x)
  have hLabel : (functionsOver Binary q).obj.map v.op u =
      ⟨ContinuousMap.const (↥(pullback (V x).hom q : Scheme.{0})) (c x).2⟩ := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro a
    exact congrArg (fun t : ULift.{1} (C(pullback (V x).hom q, M × Binary)) ↦ (t.down a).2) (hc x)
  have hDiff : (binaryDifference b₀ b₁ h₀ h₁).hom.app (op (V x)) b' =
      oneSection (q := q) (V x) := by
    unfold b'
    rw [NatTrans.naturality_apply (binaryDifference b₀ b₁ h₀ h₁).hom v.op b, hb, oneSection_restrict]
  have hPos : P₀.hom.app (op (V x)) b' = ⟨ContinuousMap.const (↥(pullback (V x).hom q : Scheme.{0})) (c x).2⟩ :=
    (NatTrans.naturality_apply P₀.hom v.op b).trans hLabel
  exact ⟨relabel M (c x).2 (c x).1 b',
    (relabel_difference_const b₀ b₁ h₀ h₁ M (c x).2 (c x).1 b' hDiff hPos).trans hVal.symm⟩

private abbrev terminal := Scheme.ProEt.mk (𝟙 X)

set_option maxHeartbeats 1800000 in
/-- It suffices that 1 has local binary lifts on the actual terminal object. -/
theorem locallySurjective_of_terminal_binary
    (hBin : Presheaf.imageSieve (binaryDifference b₀ b₁ h₀ h₁).hom
      (oneSection (q := q) (terminal (X := X))) ∈ J (X := X) (terminal (X := X))) :
    Presheaf.IsLocallySurjective (J (X := X)) (difference p q b₀ b₁ h₀ h₁ M).hom where
  imageSieve_mem {U} s := by
    let k : U ⟶ terminal (X := X) := MorphismProperty.Over.homMk U.hom (Category.comp_id _)
    have hk := (J (X := X)).pullback_stable k hBin
    rw [Presheaf.pullback_imageSieve, oneSection_restrict] at hk
    apply (J (X := X)).transitive hk
    intro V a ha
    obtain ⟨b, hb⟩ := ha
    rw [Presheaf.pullback_imageSieve]
    rw [oneSection_restrict] at hb
    exact image_mem_with_separator b₀ b₁ h₀ h₁ M V _ b hb

/-- A certified binary covering lift gives an epimorphism of actual native sheaves. -/
theorem epi_of_terminal_binary
    (hBin : Presheaf.imageSieve (binaryDifference b₀ b₁ h₀ h₁).hom
      (oneSection (q := q) (terminal (X := X))) ∈ J (X := X) (terminal (X := X))) :
    Epi (difference p q b₀ b₁ h₀ h₁ M) :=
  (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} _).mp
    (locallySurjective_of_terminal_binary b₀ b₁ h₀ h₁ M hBin)

end
end ManuscriptAudit.ProetaleBranchDifferenceEpi

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleBranchDifferenceEpi.epi_of_terminal_binary
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
