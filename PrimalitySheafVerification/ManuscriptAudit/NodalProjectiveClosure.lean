import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.NodalAffinePresentation

/-! The proper schematic closure of the actual affine nodal model. -/

namespace ManuscriptAudit.NodalProjectiveClosure

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification NodalConductor NodalAffinePresentation

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

def chartValues (i : Fin 3) : coordinates K :=
  if i = 0 then NodalAffinePresentation.nodeX K else if i = 1 then
    NodalAffinePresentation.nodeY K else 1

theorem chartValues_Z : chartValues K 2 = 1 := by
  simp [chartValues]

def chartEvaluation : standardZChartRing K →+* coordinates K :=
  standardZChartEvaluation K (chartValues K) (chartValues_Z K)

theorem chartEvaluation_surjective : Function.Surjective (chartEvaluation K) := by
  rintro ⟨f, hf⟩
  refine Algebra.adjoin_induction
    (p := fun a ha => ∃ q : standardZChartRing K, chartEvaluation K q = ⟨a, ha⟩)
    ?_ ?_ ?_ ?_ hf
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨_, by
        simpa [chartEvaluation, chartValues, NodalAffinePresentation.nodeX] using
          standardZChartEvaluation_X K (chartValues K) (chartValues_Z K) 0⟩
    · exact ⟨_, by
        simpa [chartEvaluation, chartValues, NodalAffinePresentation.nodeY] using
          standardZChartEvaluation_X K (chartValues K) (chartValues_Z K) 1⟩
  · intro a
    exact ⟨_, standardZChartEvaluation_C K (chartValues K) (chartValues_Z K) a⟩
  · rintro a b _ _ ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨p + q, (map_add (chartEvaluation K) p q).trans (congrArg₂ (· + ·) hp hq)⟩
  · rintro a b _ _ ⟨p, hp⟩ ⟨q, hq⟩
    exact ⟨p * q, (map_mul (chartEvaluation K) p q).trans (congrArg₂ (· * ·) hp hq)⟩

abbrev affineNode : Scheme.{u} := Spec (CommRingCat.of (coordinates K))

/-- The projective embedding on the affine chart is [t²−1:t(t²−1):1]. -/
def nodeInPlane : affineNode K ⟶ projectivePlane K :=
  Spec.map (CommRingCat.ofHom (chartEvaluation K)) ≫ affineZChartι K

private instance nodeInPlane_isImmersion : IsImmersion (nodeInPlane K) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (chartEvaluation K))) :=
    IsClosedImmersion.spec_of_surjective _ (chartEvaluation_surjective K)
  unfold nodeInPlane
  infer_instance

private instance nodeInPlane_quasiCompact : QuasiCompact (nodeInPlane K) :=
  quasiCompact_of_compactSpace _

/-- Schematic closure of the actual affine nodal curve. -/
abbrev projectiveNode : Scheme.{u} := (nodeInPlane K).image

def affineOpen : affineNode K ⟶ projectiveNode K := (nodeInPlane K).toImage

def projectiveNodeToBase : projectiveNode K ⟶ Spec (CommRingCat.of K) :=
  (nodeInPlane K).imageι ≫ projectivePlaneToBase K

theorem projectiveNode_isProper : IsProper (projectiveNodeToBase K) := by
  letI : IsProper (projectivePlaneToBase K) := projectivePlaneToBase_isProper K
  unfold projectiveNodeToBase
  infer_instance

instance affineOpen_isOpenImmersion : IsOpenImmersion (affineOpen K) := by
  unfold affineOpen
  infer_instance

theorem affineOpen_isDominant : IsDominant (affineOpen K) := by
  unfold affineOpen
  infer_instance

/-- The homogeneous defining relation evaluated at the affine parametrization. -/
def homogeneousEquation : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
    MvPolynomial.X 0 ^ 2 * (MvPolynomial.X 0 + MvPolynomial.X 2)

theorem homogeneousEquation_degree :
    MvPolynomial.IsHomogeneous (homogeneousEquation K) 3 := by
  exact (((MvPolynomial.isHomogeneous_X K (1 : Fin 3)).pow 2).mul
    (MvPolynomial.isHomogeneous_X K (2 : Fin 3))).sub
      (((MvPolynomial.isHomogeneous_X K (0 : Fin 3)).pow 2).mul
        ((MvPolynomial.isHomogeneous_X K (0 : Fin 3)).add
          (MvPolynomial.isHomogeneous_X K (2 : Fin 3))))

theorem homogeneousEquation_eval :
    MvPolynomial.aeval (chartValues K) (homogeneousEquation K) = 0 := by
  simp only [homogeneousEquation, map_mul, map_sub, map_pow, map_add, MvPolynomial.aeval_X]
  change NodalAffinePresentation.nodeY K ^ 2 * 1 -
    NodalAffinePresentation.nodeX K ^ 2 * (NodalAffinePresentation.nodeX K + 1) = 0
  apply Subtype.ext
  change y K ^ 2 * 1 - x K ^ 2 * (x K + 1) = 0
  unfold y x
  ring

end
end ManuscriptAudit.NodalProjectiveClosure

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalProjectiveClosure.chartEvaluation_surjective,
      ``ManuscriptAudit.NodalProjectiveClosure.projectiveNode_isProper,
      ``ManuscriptAudit.NodalProjectiveClosure.affineOpen_isOpenImmersion,
      ``ManuscriptAudit.NodalProjectiveClosure.affineOpen_isDominant,
      ``ManuscriptAudit.NodalProjectiveClosure.homogeneousEquation_degree,
      ``ManuscriptAudit.NodalProjectiveClosure.homogeneousEquation_eval] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
