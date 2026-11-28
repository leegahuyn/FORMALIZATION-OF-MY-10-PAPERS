import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Unique
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerSchemePullback
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerConstantTransition

/-! The actual Kummer root trivialization is functorial over a fixed coefficient field. -/

namespace ManuscriptAudit.ProetaleKummerSchemeConstant

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ProetaleBaseChange (baseChange directImage)
open ProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleKummerSchemePullback (unitsToDirectImage unitsPullback kernelPullback kernelMap)
open ProetaleKummerCoefficientMap (coefficientGroup coefficientMap constantToRoots)
open ProetaleKummerRoots (roots_isSheaf rootsKernelIso rootsKernelIso_hom_ι)
open ProetaleKummerConstantTransition (label)
open ProetaleSchemeCohomologyPullback (pullback pullback_naturality constant)
open ProetaleUnitSheaf (unitSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X Y : Scheme.{0}} (d : ℕ)
  [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

private abbrev M := coefficientGroup K d
private abbrev C (Z : Scheme.{0}) := (constantSheaf (J Z) G).obj (M (K := K) d)
private abbrev rootUnits {Z : Scheme.{0}} (k : Z ⟶ Spec (CommRingCat.of K)) :
    C (K := K) d Z ⟶ unitSheaf Z := (constantKernelIso k d).hom ≫ kernel.ι (power Z d)

set_option maxHeartbeats 2700000 in
private theorem label_evaluation {Z : Scheme.{0}} (k : Z ⟶ Spec (CommRingCat.of K))
    {T : Z.ProEt} (hT : IsTerminal T) :
    (constantSheafAdj (J Z) G hT).homEquiv (M (K := K) d) (unitSheaf Z) (rootUnits d k) =
      (label k d).app (op T) := by
  let η := constantToRoots k d
  let D := (Functor.const Z.ProEtᵒᵖ).obj (M (K := K) d)
  let b := sheafificationAdjunction (J Z) G
  have h : (b.homEquiv D (unitSheaf Z)) (rootUnits d k) = label k d := by
    rw [Adjunction.homEquiv_unit]
    change toSheafify (J Z) D ≫ sheafifyMap (J Z) η ≫
      (isoSheafify (J Z) (roots_isSheaf Z d)).inv ≫ (rootsKernelIso Z d).hom.hom ≫
        (kernel.ι (power Z d)).hom = label k d
    rw [rootsKernelIso_hom_ι, ← Category.assoc (toSheafify (J Z) D), ← toSheafify_naturality]
    simp only [Category.assoc, isoSheafify_inv, toSheafify_sheafifyLift_assoc, Category.id_comp, label, η]
  let a := constantPresheafAdj G hT
  change (a.homEquiv (M (K := K) d) (unitSheaf Z).obj)
    ((b.homEquiv D (unitSheaf Z)) (rootUnits d k)) = _
  rw [h, Adjunction.homEquiv_unit]
  change 𝟙 _ ≫ (label k d).app (op T) = _
  rw [Category.id_comp]

variable (f : X ⟶ Y) (x : X ⟶ Spec (CommRingCat.of K)) (y : Y ⟶ Spec (CommRingCat.of K))
  (h : f ≫ y = x)

include h in
private theorem coefficient_projection (V : Y.ProEt) :
    coefficientMap y V ≫ (pullback.fst V.hom f).appTop =
      coefficientMap x ((baseChange f).obj V) := by
  have e : pullback.fst V.hom f ≫ (V.hom ≫ y) = pullback.snd V.hom f ≫ x := by
    rw [← Category.assoc, pullback.condition, Category.assoc, h]
  unfold coefficientMap
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, e] <;> rfl

include h in
private theorem labels_projection (V : Y.ProEt) :
    (label y d).app (op V) ≫ (unitsToDirectImage f).hom.app (op V) =
      (label x d).app (op ((baseChange f).obj V)) := by
  apply AddCommGrpCat.ext
  intro a
  apply ULift.ext
  apply Additive.ext
  apply Units.ext
  exact congrArg (fun t : CommRingCat.of K ⟶
    ProetaleKummerRoots.coordinates X ((baseChange f).obj V) ↦ t (a.down.toMul.val : K))
      (coefficient_projection f x y h V)

include h in
set_option maxHeartbeats 6300000 in
/-- Pullback of actual Kummer kernels is the constant coefficient comparison over the fixed field. -/
theorem constantKernel_pullback :
    (inverseImage f).map (constantKernelIso y d).hom ≫ kernelPullback f d =
      ((constantInverseImageIso f).app (M (K := K) d)).hom ≫ (constantKernelIso x d).hom := by
  let L := inverseImage f
  let R := directImage f G
  let a := adjunction f
  let TY := Scheme.ProEt.mk (𝟙 Y)
  let hTY : IsTerminal TY := MorphismProperty.Over.mkIdTerminal @WeaklyEtale Y
  let U := (baseChange f).obj TY
  let hU : IsTerminal U := IsTerminal.isTerminalObj (baseChange f) TY hTY
  let sy := constantSheafAdj (J Y) G hTY
  let sx := constantSheafAdj (J X) G hU
  let c := sy.comp a
  let ω := M (K := K) d
  let i := (constantInverseImageIso f).app ω
  apply (cancel_mono (kernel.ι (power X d))).mp
  have hi : kernelPullback f d ≫ kernel.ι (power X d) =
      L.map (kernel.ι (power Y d)) ≫ unitsPullback f := kernel.lift_ι _ _ _
  rw [Category.assoc, hi, ← Category.assoc, ← Functor.map_comp, Category.assoc]
  change L.map (rootUnits d y) ≫ unitsPullback f = i.hom ≫ rootUnits d x
  apply (c.homEquiv ω (unitSheaf X)).injective
  have hy : (c.homEquiv ω (unitSheaf X)) (L.map (rootUnits d y) ≫ unitsPullback f) =
      (label y d).app (op TY) ≫ (unitsToDirectImage f).hom.app (op TY) := by
    change (sy.homEquiv ω (R.obj (unitSheaf X))) ((a.homEquiv _ _) (L.map (rootUnits d y) ≫
      (a.homEquiv _ _).symm (unitsToDirectImage f))) = _
    rw [a.homEquiv_naturality_left, Equiv.apply_symm_apply, sy.homEquiv_naturality_right,
      label_evaluation d y hTY] <;> rfl
  have hx : (c.homEquiv ω (unitSheaf X)) (i.hom ≫ rootUnits d x) =
      (label x d).app (op U) := by
    change (c.homEquiv ω (unitSheaf X)) ((c.leftAdjointUniq sx).hom.app ω ≫ rootUnits d x) = _
    rw [c.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      ← sx.homEquiv_unit, label_evaluation d x hU]
  exact hy.trans ((labels_projection d f x y h TY).trans hx.symm)

include h in
/-- Native constant-coefficient pullback commutes with actual Kummer cohomology. -/
theorem constant_cohomology (n : ℕ) (z : Sheaf.H (C (K := K) d Y) n) :
    kernelMap f d n (Sheaf.H.map (constantKernelIso y d).hom n z) =
      Sheaf.H.map (constantKernelIso x d).hom n (constant f (M (K := K) d) n z) := by
  let q := pullback f (C (K := K) d Y) n z
  change Sheaf.H.map (kernelPullback f d) n
      (pullback f (kernel (power Y d)) n (Sheaf.H.map (constantKernelIso y d).hom n z)) =
    Sheaf.H.map (constantKernelIso x d).hom n
      (Sheaf.H.map ((constantInverseImageIso f).app (M (K := K) d)).hom n q)
  rw [pullback_naturality, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
    constantKernel_pullback d f x y h]

end
end ManuscriptAudit.ProetaleKummerSchemeConstant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.ProetaleKummerSchemeConstant.constantKernel_pullback,
      ``ManuscriptAudit.ProetaleKummerSchemeConstant.constant_cohomology] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
