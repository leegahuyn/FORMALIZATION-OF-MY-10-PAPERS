import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorCoefficientLift
import PrimalitySheafVerification.ManuscriptAudit.SheafPointwiseKernel

/-! The actual normalization-conductor sequence of the split node
is short exact for arbitrary discrete abelian coefficients. -/

namespace ManuscriptAudit.NodalConductorAbelianSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open EtaleClosedSupportLocalConstants
open NodalNormalizationFiber (affineNode)
open NodalNormalizationEtaleFibers (Conductor)
open NodalAffineOrigin (originMap)
open NodalConductorSheafKernel
open NodalConductorCoefficientLift
open NodalSwapCoverNoSection (coverObject coverMap_surjective)
open NodalSwapConductorUnit (unitLift)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

variable (K : Type) [Field K]
variable (M : AddCommGrpCat.{0}) [TopologicalSpace M] [DiscreteTopology M]
variable [IsTopologicalAddGroup M]

private abbrev Pairs := AddCommGrpCat.of (M × Binary)

local instance : TopologicalSpace (Pairs M) := inferInstanceAs (TopologicalSpace (M × Binary))
local instance : DiscreteTopology (Pairs M) := inferInstanceAs (DiscreteTopology (M × Binary))
local instance : IsTopologicalAddGroup (Pairs M) := inferInstanceAs (IsTopologicalAddGroup (M × Binary))

private def pairedSection (U : (affineNode K).Etale)
    (s : (conductorFunctions K M).obj.obj (op U))
    (b : (conductorFunctions K Binary).obj.obj (op U)) :
    (conductorFunctions K (Pairs M)).obj.obj (op U) :=
  (show ContinuousMap (Conductor K U).left M from s).prodMk
    (show ContinuousMap (Conductor K U).left Binary from b)

private theorem paired_const_components {U V : (affineNode K).Etale} (v : V ⟶ U)
    (s : (conductorFunctions K M).obj.obj (op U))
    (b : (conductorFunctions K Binary).obj.obj (op U)) (c : Pairs M)
    (h : (conductorFunctions K (Pairs M)).obj.map v.op (pairedSection K M U s b) =
      ContinuousMap.const (Conductor K V).left c) :
    (conductorFunctions K M).obj.map v.op s = ContinuousMap.const (Conductor K V).left c.1 ∧
      (conductorFunctions K Binary).obj.map v.op b = ContinuousMap.const (Conductor K V).left c.2 := by
  constructor <;> apply ContinuousMap.ext <;> intro y
  · exact congrArg (fun v : ContinuousMap (Conductor K V).left (Pairs M) ↦ (v y).1) h
  · exact congrArg (fun v : ContinuousMap (Conductor K V).left (Pairs M) ↦ (v y).2) h

private theorem restrict_restrict {U V W : (affineNode K).Etale}
    (F : (affineNode K).Etaleᵒᵖ ⥤ AddCommGrpCat.{0}) (a : U ⟶ V) (b : V ⟶ W)
    (s : F.obj (op W)) :
    F.map a.op (F.map b.op s) = F.map (a ≫ b).op s := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

set_option maxHeartbeats 5000000 in
/-- Every local conductor value lifts along the actual branch difference. -/
theorem branchDifference_locallySurjective (h2 : (2 : K) ≠ 0) :
    Presheaf.IsLocallySurjective (affineNode K).smallEtaleTopology (branchDifference K M).hom where
  imageSieve_mem {U} s := by
    classical
    let T := coverObject K h2
    letI : Etale T.hom := T.prop
    letI : Etale U.hom := U.prop
    let P := Scheme.Etale.mk (pullback.fst U.hom T.hom ≫ U.hom)
    let p : P ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom T.hom) rfl
    let q : P ⟶ T := MorphismProperty.Over.homMk (pullback.snd U.hom T.hom) pullback.condition.symm
    let F := normalizationFunctions K Binary
    let H := conductorFunctions K M
    let sP := H.obj.map p.op s
    let bP := F.obj.map q.op (unitLift K h2)
    let positiveLabel := (positiveTrace K).hom.app (op P) bP
    letI : IsClosedImmersion (originMap K) := NodalAffineOrigin.originMap_isClosedImmersion K
    choose W hW c hc using fun y : P.left ↦
      exists_open_restriction_const (originMap K) (Pairs M) P (pairedSection K M P sP positiveLabel) y
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
    obtain ⟨hVal, hLabel⟩ := paired_const_components K M (v y) sP positiveLabel (c y) (hc y)
    let b := F.obj.map (v y).op bP
    have hDiff : (branchDifference K Binary).hom.app (op (V y)) b =
        ContinuousMap.const (Conductor K (V y)).left (1 : Binary) := by
      have hb : b = F.obj.map (v y ≫ q).op (unitLift K h2) :=
        restrict_restrict K F.obj (v y) q (unitLift K h2)
      exact (congrArg ((branchDifference K Binary).hom.app (op (V y))) hb).trans
        (unitLift_difference_after K h2 (V y) (v y ≫ q))
    have hPos : (positiveTrace K).hom.app (op (V y)) b =
        ContinuousMap.const (Conductor K (V y)).left (c y).2 :=
      (NatTrans.naturality_apply (positiveTrace K).hom (v y).op bP).trans hLabel
    refine ⟨relabel K M (V y) (c y).2 (c y).1 b, ?_⟩
    have hValue : H.obj.map (a y).op s = ContinuousMap.const (Conductor K (V y)).left (c y).1 :=
      (restrict_restrict K H.obj (v y) p s).symm.trans hVal
    exact (relabel_difference_const K M (V y) (c y).2 (c y).1 b hDiff hPos).trans hValue.symm

/-- The normalization and conductor maps of continuous local sections for M. -/
def sequence : ShortComplex (Sheaf (affineNode K).smallEtaleTopology AddCommGrpCat.{0}) :=
  ShortComplex.mk (baseDiagonal K M) (branchDifference K M) (diagonal_difference_zero K M)

/-- The genuine normalization-conductor sequence is short exact. -/
theorem sequence_shortExact (h2 : (2 : K) ≠ 0) : (sequence K M).ShortExact := by
  letI : Sheaf.IsLocallySurjective (branchDifference K M) := branchDifference_locallySurjective K M h2
  let S := sequence K M
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) :=
    SheafPointwiseKernel.kernel_isLimit S
      (fun U ↦ diagonal_injective_on_sections K M h2 U.unop)
      (fun U ↦ exact_on_sections K M h2 U.unop)
  letI : Epi S.g := inferInstanceAs (Epi (branchDifference K M))
  letI : Mono S.f := mono_of_isLimit_fork hKer
  exact { exact := S.exact_of_f_is_kernel hKer }

end

end ManuscriptAudit.NodalConductorAbelianSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalConductorAbelianSequence.branchDifference_locallySurjective,
      ``ManuscriptAudit.NodalConductorAbelianSequence.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
