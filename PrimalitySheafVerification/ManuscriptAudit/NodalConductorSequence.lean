import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.LocallySurjective
import PrimalitySheafVerification.ManuscriptAudit.EtaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapConductorUnit
import PrimalitySheafVerification.ManuscriptAudit.SheafPointwiseKernel

/-! The actual split affine node has the normalization-conductor
short exact sequence with constant mod-two coefficients. -/

namespace ManuscriptAudit.NodalConductorSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalNormalizationFiber (affineNode)
open NodalAffineOrigin (originMap)
open NodalConductorSheafKernel (baseFunctions normalizationFunctions conductorFunctions baseDiagonal
  branchDifference diagonal_difference_zero diagonal_injective_on_sections exact_on_sections)
open NodalSwapCoverNoSection (coverObject coverMap_surjective)
open NodalSwapConductorUnit (unitLift unitLift_difference)
open EtaleClosedSupportLocalConstants (openObject openArrow exists_open_restriction_const)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (h2 : (2 : K) ≠ 0)

private abbrev C := AddCommGrpCat.of (ZMod 2)
local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

private abbrev G := normalizationFunctions K C
private abbrev H := conductorFunctions K C

private theorem restrict_unit (V : (affineNode K).Etale) (a : V ⟶ coverObject K h2) :
    (branchDifference K C).hom.app (op V)
        ((G K).obj.map a.op (unitLift K h2)) =
      ContinuousMap.const (NodalNormalizationEtaleFibers.Conductor K V).left (1 : C) := by
  have h := ConcreteCategory.congr_hom
    ((branchDifference K C).hom.naturality a.op) (unitLift K h2)
  change (branchDifference K C).hom.app (op V) ((G K).obj.map a.op (unitLift K h2)) =
    (H K).obj.map a.op ((branchDifference K C).hom.app (op (coverObject K h2)) (unitLift K h2))
    at h
  rw [unitLift_difference] at h
  exact h

include h2 in
private theorem localSurjectivity :
    Presheaf.IsLocallySurjective (affineNode K).smallEtaleTopology (branchDifference K C).hom where
  imageSieve_mem {U} s := by
    classical
    let T := coverObject K h2
    letI : Etale T.hom := T.prop
    letI : Etale U.hom := U.prop
    let P := Scheme.Etale.mk (pullback.fst U.hom T.hom ≫ U.hom)
    let p : P ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom T.hom) rfl
    let q : P ⟶ T := MorphismProperty.Over.homMk (pullback.snd U.hom T.hom) pullback.condition.symm
    let s' := (H K).obj.map p.op s
    choose W hW b hb using fun y : P.left =>
      exists_open_restriction_const (originMap K) C P s' y
    let V (y : P.left) := openObject P (W y)
    let v (y : P.left) : V y ⟶ P := openArrow P (W y)
    let a (y : P.left) : V y ⟶ U := v y ≫ p
    have hcover : Sieve.ofArrows V a ∈ (affineNode K).smallEtaleTopology U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨t, ht⟩ := coverMap_surjective K h2 (U.hom x)
      obtain ⟨y, hy, _⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := U.hom) (g := T.hom) x t ht.symm
      exact Set.mem_iUnion.2 ⟨y, ⟨⟨y, hW y⟩, hy⟩⟩
    refine (affineNode K).smallEtaleTopology.superset_covering ?_ hcover
    apply (Sieve.generate_le_iff _ _).2
    rintro _ _ ⟨y⟩
    have he : (H K).obj.map (a y).op s =
        ContinuousMap.const (NodalNormalizationEtaleFibers.Conductor K (V y)).left (b y) := by
      change (H K).obj.map (v y ≫ p).op s = _
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      exact hb y
    have hv : b y = 0 ∨ b y = 1 :=
      (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (b y)
    rcases hv with hz | ho
    · refine ⟨0, ?_⟩
      rw [map_zero, he, hz] <;> rfl
    · refine ⟨(G K).obj.map (v y ≫ q).op (unitLift K h2), ?_⟩
      rw [he, ho]
      exact restrict_unit K h2 (V y) (v y ≫ q)

/-- The native short complex of constant, normalized, and conductor sections. -/
def sequence : ShortComplex (Sheaf (affineNode K).smallEtaleTopology AddCommGrpCat.{0}) :=
  ShortComplex.mk (baseDiagonal K C) (branchDifference K C) (diagonal_difference_zero K C)

include h2 in
/-- The actual conductor sequence of mod-two étale sheaves is short exact. -/
theorem sequence_shortExact : (sequence K).ShortExact := by
  letI : Sheaf.IsLocallySurjective (branchDifference K C) := localSurjectivity K h2
  let S := sequence K
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    SheafPointwiseKernel.kernel_isLimit S
      (fun U => diagonal_injective_on_sections K C h2 U.unop)
      (fun U => exact_on_sections K C h2 U.unop)
  haveI : Epi S.g := inferInstanceAs (Epi (branchDifference K C))
  haveI : Mono S.f := mono_of_isLimit_fork hKer
  exact { exact := S.exact_of_f_is_kernel hKer }

end
end ManuscriptAudit.NodalConductorSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalConductorSequence.sequence_shortExact
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
