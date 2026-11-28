import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleKummerCyclicCoordinates
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerKernel

/-! The constant roots-of-unity coefficient tower and the actual full
étale Kummer kernel tower agree with their literal power transitions. -/

namespace ManuscriptAudit.FullEtaleKummerConstantTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerRelativeCoefficients KummerKernel
open KummerConstantCoefficients (coefficientGroup)
open KummerUnitsPresheaf (power)
open KummerSheafSequence (sheafPower)
open EtaleKummerCyclicCoordinates FullEtaleKummerKernel

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0})

private abbrev C := AddCommGrpCat.{0}
private abbrev A := Scheme.AffineEtale.topology X
private abbrev J := X.smallEtaleTopology
private abbrev F := presheafToSheaf (A X) C
private abbrev E := Scheme.AffineEtale.sheafEquiv X C
private abbrev S := KummerRelativeFull.sequence X
private abbrev p := sheafPower X

private theorem sheafifiedRoots_hom_ι (d : ℕ) :
    (sheafifiedRootsIsoKernel X d).hom ≫ kernel.ι (p X d) =
      (F X).map (inclusion X d) := by
  let e := (rootsIsKernel X d).conePointUniqueUpToIso (limit.isLimit (parallelPair (power X d) 0))
  let b := PreservesKernel.iso (F X) (power X d)
  have h := IsLimit.conePointUniqueUpToIso_hom_comp (rootsIsKernel X d)
    (limit.isLimit (parallelPair (power X d) 0)) WalkingParallelPair.zero
  change e.hom ≫ kernel.ι (power X d) = inclusion X d at h
  have hb : b.hom ≫ kernel.ι (p X d) = (F X).map (kernel.ι (power X d)) := by
    have hb := PreservesKernel.iso_inv_ι (F X) (power X d)
    calc
      _ = b.hom ≫ (b.inv ≫ (F X).map (kernel.ι (power X d))) := congrArg (b.hom ≫ ·) hb.symm
      _ = _ := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  change (F X).map e.hom ≫ b.hom ≫ kernel.ι (p X d) = _
  rw [hb, ← Functor.map_comp, h]

variable {X} {K : Type} [Field K] [IsAlgClosed K]
variable (k : X ⟶ Spec (CommRingCat.of K)) (l : ℕ) [Fact l.Prime] [NeZero (l : K)]

local instance power_neZero (n : ℕ) : NeZero (l ^ n) :=
  ⟨pow_ne_zero n (Fact.out : l.Prime).ne_zero⟩

local instance castPower_neZero (n : ℕ) : NeZero ((l ^ n : ℕ) : K) :=
  ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (l : K))⟩

private abbrev M (n : ℕ) := coefficientGroup K (l ^ n)

private def affineIso (n : ℕ) :
    (constantSheaf (A X) C).obj (M l n) ≅ kernel (p X (l ^ n)) :=
  constantRootSheafIso (d := l ^ n) k ≪≫ sheafifiedRootsIsoKernel X (l ^ n)

private theorem affineIso_hom_ι (n : ℕ) :
    (affineIso k l n).hom ≫ kernel.ι (p X (l ^ n)) = (F X).map (label k (l ^ n)) := by
  change (F X).map (constantToRoots k (l ^ n)) ≫
    (sheafifiedRootsIsoKernel X (l ^ n)).hom ≫ kernel.ι (p X (l ^ n)) = _
  rw [sheafifiedRoots_hom_ι, ← Functor.map_comp] <;> rfl

private abbrev affineStep (n : ℕ) :=
  (constantSheaf (A X) C).map (coefficientStep K l n)

private theorem affineStep_label (n : ℕ) :
    affineStep (X := X) (K := K) l n ≫ (F X).map (label k (l ^ n)) =
      (F X).map (label k (l ^ (n + 1))) ≫ p X l := by
  change (F X).map ((Functor.const X.AffineEtaleᵒᵖ).map (coefficientStep K l n)) ≫
    (F X).map (label k (l ^ n)) = (F X).map (label k (l ^ (n + 1))) ≫ (F X).map (power X l)
  rw [← Functor.map_comp, ← Functor.map_comp, label_step l n k]

private def constantComparison (n : ℕ) :
    (constantSheaf (A X) C).obj (M l n) ≅
      (E X).inverse.obj ((constantSheaf (J X) C).obj (M l n)) :=
  let e := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    (A X) (J X) (Scheme.AffineEtale.Spec X) C
  e.app ((Functor.const X.Etaleᵒᵖ).obj (M l n))

/-- Actual constant coefficient power step on the full small étale site. -/
abbrev constantStep (n : ℕ) :=
  (constantSheaf (J X) C).map (coefficientStep K l n)

private theorem constantComparison_naturality (n : ℕ) :
    (E X).inverse.map (constantStep (X := X) (K := K) l n) ≫ (constantComparison (X := X) (K := K) l n).inv =
      (constantComparison (X := X) (K := K) l (n + 1)).inv ≫ affineStep (X := X) (K := K) l n := by
  let e := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    (A X) (J X) (Scheme.AffineEtale.Spec X) C
  exact e.inv.naturality ((Functor.const X.Etaleᵒᵖ).map (coefficientStep K l n))

/-- Natural comparison of the literal coefficients with the Kummer kernel. -/
def constantKernelIso (n : ℕ) :
    (constantSheaf (J X) C).obj (M l n) ≅ (S X (l ^ n)).X₁ :=
  ((E X).counitIso.app _).symm ≪≫
    (E X).functor.mapIso ((constantComparison (X := X) (K := K) l n).symm ≪≫ affineIso k l n)

private abbrev comparisonArrow (n : ℕ) :=
  (constantComparison (X := X) (K := K) l n).inv

private abbrev rootLabel (n : ℕ) := comparisonArrow (X := X) (K := K) l n ≫
  (F X).map (label k (l ^ n))

/-- The native full Kummer first-term comparison followed by inclusion
is the transported literal affine root label. -/
theorem constantKernel_toUnits (n : ℕ) :
    (constantKernelIso k l n).hom ≫ (S X (l ^ n)).f =
      (E X).counitIso.inv.app ((constantSheaf (J X) C).obj (M l n)) ≫
        (E X).functor.map (rootLabel k l n) := by
  change (E X).counitIso.inv.app _ ≫ (E X).functor.map
      (comparisonArrow (X := X) (K := K) l n ≫ (affineIso k l n).hom) ≫
      (E X).functor.map (kernel.ι (p X (l ^ n))) = _
  rw [← Functor.map_comp, Category.assoc, affineIso_hom_ι] <;> rfl

/-- The actual full small étale coefficient comparison intertwines the
native root transition at every level. -/
theorem constantKernelIso_step (n : ℕ) :
    constantStep (X := X) (K := K) l n ≫ (constantKernelIso k l n).hom =
      (constantKernelIso k l (n + 1)).hom ≫ rootsStep X (l ^ n) l := by
  letI : Mono ((S X (l ^ n)).f) :=
    inferInstanceAs (Mono ((E X).functor.map (kernel.ι (p X (l ^ n)))))
  apply (cancel_mono (S X (l ^ n)).f).mp
  rw [Category.assoc, constantKernel_toUnits, Category.assoc, rootsStep_inclusion,
    ← Category.assoc (constantKernelIso k l (n + 1)).hom, constantKernel_toUnits]
  let h := constantStep (X := X) (K := K) l n
  have hc := (E X).counitIso.inv.naturality h
  change h ≫ (E X).counitIso.inv.app _ = (E X).counitIso.inv.app _ ≫
    (E X).functor.map ((E X).inverse.map h) at hc
  rw [← Category.assoc h, hc, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  congr 1
  change (E X).inverse.map h ≫ (comparisonArrow (X := X) (K := K) l n ≫
    (F X).map (label k (l ^ n))) = (comparisonArrow (X := X) (K := K) l (n + 1) ≫
      (F X).map (label k (l ^ (n + 1)))) ≫ p X l
  rw [← Category.assoc, constantComparison_naturality, Category.assoc, affineStep_label, Category.assoc]

end

end ManuscriptAudit.FullEtaleKummerConstantTransition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleKummerConstantTransition.constantKernelIso_step
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
